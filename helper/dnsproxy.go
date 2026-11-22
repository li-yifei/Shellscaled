package main

import (
	"bytes"
	"context"
	"encoding/binary"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/netip"
	"net/url"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
)

// The proxy answers queries handed to it by the module chains shellscaled_dns
// (IPv4 nat and IPv6 nat on 127.0.0.1:1053 / [::1]:1053, or IPv6 filter NFQUEUE
// queue 1053 on kernels lacking IPv6 NAT). Its own UDP/53 and transparent
// replies carry the bypass mark, which each chain returns first.
const (
	magicDNSChain         = "shellscaled_dns"
	magicDNSFallbackChain = "shellscaled_dns6_fallback"
	magicDNSPort          = 1053
	magicDNSMaxSuffix     = 16
)

const (
	ipv6ModeNAT = iota
	ipv6ModeNFQueue
	ipv6ModeFallback
)

const (
	nfnlSubsysQueue   = 3
	nfqnlMsgPacket    = 0
	nfqnlMsgVerdict   = 1
	nfqnlMsgConfig    = 2
	nfqnlCfgCmdBind   = 1
	nfqnlCfgCmdUnbind = 2
	nfqnlCopyPacket   = 2
	nfqaPacketHdr     = 1
	nfqaVerdictHdr    = 2
	nfqaMark          = 3
	nfqaIfindexOutdev = 6
	nfqaPayload       = 10
	nfqaCfgCmd        = 1
	nfqaCfgParams     = 2
	nfqaCfgMask       = 4
	nfqaCfgFlags      = 5
	nfqaCfgFailOpen   = 1
	nfDrop            = 0
	nfAccept          = 1
	ipv6Transparent   = 75
	soReusePort       = 15
)

// magicDNSEnabledFile records the requested state; absence defaults to off.
// A variable for tests.
var magicDNSEnabledFile = dataDir + "/magicdns-enabled"

func magicDNSEnabled() bool {
	request, _ := readMagicDNSRequest()
	return request.Enabled
}

var (
	magicDNSStatePath = dataDir + "/run/magicdns.json"
	magicDNSPIDPath   = dataDir + "/run/magicdns.pid"
)

type magicDNSState struct {
	Running      bool   `json:"running"`
	Mode         string `json:"mode"`
	Enabled      bool   `json:"enabled"`
	NoString     bool   `json:"noString,omitempty"`
	Rules        bool   `json:"rules"`
	Rules6       bool   `json:"rules6"`
	IPv6Fallback bool   `json:"ipv6Fallback,omitempty"`
	PrivateDNS   string `json:"privateDns"`
	Upstream     string `json:"upstream"`
	Daemon       string `json:"daemon"`
	ExitNode     string `json:"exitNode"`
	Pending      bool   `json:"pending,omitempty"`
	ApplyFailed  bool   `json:"applyFailed,omitempty"`
	generation   string // The acknowledged request, never product display data.
}

// Daemon and ExitNode record the BackendState and prefs.ExitNodeID the mode
// was derived from, so status can tell when it is stale.
type magicDNSFile struct {
	Updated      int64  `json:"updated"`
	Mode         string `json:"mode"`
	Enabled      bool   `json:"enabled"`
	NoString     bool   `json:"noString,omitempty"`
	Rules        bool   `json:"rules"`
	Rules6       bool   `json:"rules6"`
	IPv6Fallback bool   `json:"ipv6Fallback,omitempty"`
	PrivateDNS   string `json:"privateDns"`
	Upstream     string `json:"upstream"`
	Daemon       string `json:"daemon"`
	ExitNode     string `json:"exitNode"`
	Generation   string `json:"generation"`
	ApplyFailed  bool   `json:"applyFailed,omitempty"`
}

type magicDNSProxy struct {
	backend      *backend
	doh          *http.Client
	run          func(ctx context.Context, name string, args ...string) ([]byte, error)
	origDst      func(client netip.AddrPort) (netip.AddrPort, uint32, error)
	ctProbe      func(family int) error
	sweep        func(switched bool) (int, error)
	forward      func(ctx context.Context, dst netip.AddrPort, ctmark uint32, pkt []byte) ([]byte, error)
	reply6       func(origDst, client netip.AddrPort, outdev uint32, resp []byte) error
	ifName       func(ifindex int) string
	openNFQ      func(queue uint16) (*nfqConn, error)
	probeTProxy6 func() error
	state        string
	dead6        atomic.Bool // the IPv6 listener stopped

	mu      sync.RWMutex
	suffix  string
	routes  map[string][]netip.AddrPort
	mode    string
	exitDoH string

	logMu  sync.Mutex
	logged map[string]string

	// Owned by the refresh goroutine.
	exitID       string
	enabled      bool   // Last successfully applied request, not merely read prefs.
	generation   string // Includes explicit off requests to prevent ABA matches.
	applyFailed  bool
	daemon       string
	prefsExit    string
	applied      [2]string
	rulesOK      [2]bool
	noString     bool
	conntrack    [2]int // per family: 0 untested, 1 usable, -1 unusable
	listen6      bool
	ipv6Mode     int  // ipv6ModeNAT, ipv6ModeNFQueue, or ipv6ModeFallback
	ipv6Fallback bool // Legacy/test flag: forces ipv6ModeFallback when true.
	privateDNS   string
	tick         int
	routing      *exitRouting // last observed, nil until known
}

func newMagicDNSProxy(b *backend) *magicDNSProxy {
	return &magicDNSProxy{
		backend: b,
		doh:     &http.Client{Timeout: 5 * time.Second},
		run: func(ctx context.Context, name string, args ...string) ([]byte, error) {
			return exec.CommandContext(ctx, name, args...).CombinedOutput()
		},
		origDst: conntrackOrigDst,
		ctProbe: func(family int) error {
			a := netip.AddrFrom4([4]byte{127, 0, 0, 1})
			if family == 1 {
				a = netip.IPv6Loopback()
			}
			_, _, err := conntrackOrigDst(netip.AddrPortFrom(a, 9))
			return err
		},
		sweep:        sweepStaleFlows,
		forward:      queryPassthrough,
		reply6:       sendTransparentUDP6,
		ifName:       defaultIfName,
		openNFQ:      openNFQueue,
		probeTProxy6: probeTransparentUDP6,
		state:        magicDNSStatePath,
		mode:         "off",
		listen6:      true,
		applied:      [2]string{"\x00", "\x00"},
		privateDNS:   "unknown",
		logged:       map[string]string{},
	}
}

func (p *magicDNSProxy) v6Mode() int {
	if p.ipv6Fallback {
		return ipv6ModeFallback
	}
	return p.ipv6Mode
}

func (p *magicDNSProxy) logOnce(key, msg string) {
	p.logMu.Lock()
	defer p.logMu.Unlock()
	if p.logged[key] != msg {
		p.logged[key] = msg
		if msg != "" {
			fmt.Fprintln(os.Stderr, "MagicDNS: "+msg)
		}
	}
}

func (p *magicDNSProxy) refresh(ctx context.Context) {
	var st struct {
		BackendState   string
		MagicDNSSuffix string
		CurrentTailnet *struct{ MagicDNSSuffix string }
		ExitNodeStatus *struct{ ID string }
	}
	mode, suffix, exitNode := "off", "", false
	// Opt-in: while disabled the mode stays off and the chains empty, so no
	// DNS is redirected; the proxy still runs for the stale flow reset.
	request, requestErr := readMagicDNSRequest()
	enabled := requestErr == nil && request.Enabled
	routes := map[string][]netip.AddrPort{}
	exitDoH := p.exitDoH
	p.daemon, p.prefsExit = "", ""
	if p.backend.api(ctx, "GET", "status?peers=false", nil, &st) == nil {
		p.daemon = st.BackendState
	}
	// Unknown while LocalAPI fails.
	routing, routingKnown := exitRouting{}, p.daemon != ""
	if st.BackendState == "Running" {
		suffix = st.MagicDNSSuffix
		if st.CurrentTailnet != nil && st.CurrentTailnet.MagicDNSSuffix != "" {
			suffix = st.CurrentTailnet.MagicDNSSuffix
		}
		suffix = normalizeDNSName(suffix)
		if !validDNSName(suffix) {
			suffix = ""
		}
		// dns-config returns the control-plane config whatever accept-dns is;
		// tailscaled applies split-DNS Routes only with accept-dns on.
		var prefs struct {
			CorpDNS                bool
			ExitNodeID             string
			ExitNodeAllowLANAccess bool
		}
		var cfg struct {
			Routes map[string][]struct{ Addr string }
		}
		routingKnown = false
		if p.backend.api(ctx, "GET", "prefs", nil, &prefs) == nil {
			p.prefsExit = prefs.ExitNodeID
			exit := prefs.ExitNodeID != ""
			routing, routingKnown = exitRouting{prefs.ExitNodeID, exit && exitNodeIPv6Takeover(), exit && prefs.ExitNodeAllowLANAccess}, true
			if prefs.CorpDNS && p.backend.api(ctx, "GET", "dns-config", nil, &cfg) == nil {
				routes = parseDNSRoutes(cfg.Routes)
			}
		}
		exitID := ""
		if st.ExitNodeStatus != nil {
			exitID = st.ExitNodeStatus.ID
		}
		// Probe again while DoH is unavailable, and recheck it every 30 s so a
		// lost grant falls back to the system path.
		switch {
		case exitID == "" || !enabled:
			exitDoH = ""
		case exitID != p.exitID || exitDoH == "" || p.tick%6 == 0:
			exitDoH = p.probeExitDoH(ctx, exitID)
		}
		p.exitID, exitNode = exitID, exitID != ""
		if enabled {
			mode = selectMagicDNSMode(exitID != "", exitDoH != "", len(dnsSuffixes(suffix, routes)) > 0, p.noString, p.passthroughCapable())
		}
	}
	if p.tick%6 == 0 {
		p.readPrivateDNS(ctx)
	}
	p.tick++

	err := requestErr
	if err == nil {
		err = withMagicDNSControl(ctx, func() error {
			// Network probes do not own the apply lock. A switch may have changed
			// while they were waiting; never install that superseded plan.
			current, err := readMagicDNSRequest()
			if err != nil {
				return err
			}
			if current != request {
				if current.Enabled {
					return errMagicDNSPlanSuperseded
				}
				request = current
			}
			if !request.Enabled {
				mode, suffix, routes, exitDoH = "off", "", map[string][]netip.AddrPort{}, ""
			}
			p.mu.Lock()
			p.suffix, p.routes, p.exitDoH = suffix, routes, exitDoH
			p.mu.Unlock()
			suffixes := dnsSuffixes(suffix, routes)
			v4, v6 := p.familyRules(mode, suffixes)
			ok4 := p.applyRules(ctx, 0, v4)
			if !ok4 && !p.noString && p.familyMode(mode, 0, suffixes) == "tailnet" && xtStringMissing() {
				p.noString = true
				mode = selectMagicDNSMode(exitNode, exitDoH != "", true, true, p.passthroughCapable())
				v4, v6 = p.familyRules(mode, suffixes)
				ok4 = p.applyRules(ctx, 0, v4)
			}
			ok6 := true
			switch {
			case p.v6Mode() == ipv6ModeFallback:
				ok6 = p.applyRules(ctx, 1, ipv6FallbackRules(mode, suffixes))
			case p.listen6 && p.dead6.Load():
				ok6 = p.applyRules(ctx, 1, nil)
				if ok6 {
					p.listen6 = false
				}
				p.rulesOK[1] = false
			case p.listen6:
				ok6 = p.applyRules(ctx, 1, v6)
			case p.applied[1] != "\x00":
				ok6 = p.applyRules(ctx, 1, nil)
			}
			p.mu.Lock()
			p.mode = mode
			p.applyFailed = !ok4 || !ok6
			if !p.applyFailed {
				p.enabled, p.generation = request.Enabled, request.Generation
			}
			p.mu.Unlock()
			return nil
		})
	}
	if err != nil && !errors.Is(err, errMagicDNSPlanSuperseded) {
		p.applyFailed = true
		p.logOnce("apply", "cannot apply the current request: "+err.Error())
	} else if err == nil && !p.applyFailed {
		p.logOnce("apply", "")
	}
	// Flow repair is independent of the optional DNS interception and its
	// request/apply failures. Never hold the preference lock during a sweep.
	if routingKnown {
		p.observeExitRouting(routing)
	}
	p.writeState(time.Now())
}

// selectMagicDNSMode picks the chain contents while the daemon runs. Without
// working exit-node DoH, ordinary names go to the server the system chose.
// Catch-all redirection needs conntrack to find that server.
func selectMagicDNSMode(exitNode, exitDoH, suffixes, noString, conntrack bool) string {
	switch {
	case exitNode && exitDoH:
		return "exit-doh"
	case exitNode && conntrack:
		return "exit-passthrough"
	case !suffixes || noString:
		return "off"
	}
	return "tailnet"
}

// conntrackOK tests once per family whether conntrack netlink lookups work; a
// lookup of a missing entry returns ENOENT.
func (p *magicDNSProxy) conntrackOK(family int) bool {
	if p.conntrack[family] == 0 {
		p.conntrack[family] = 1
		if err := p.ctProbe(family); err != nil && !errors.Is(err, syscall.ENOENT) {
			p.conntrack[family] = -1
			fmt.Fprintln(os.Stderr, "MagicDNS: IPv"+[2]string{"4", "6"}[family]+" conntrack lookups fail ("+err.Error()+"); ordinary IPv"+[2]string{"4", "6"}[family]+" DNS is not redirected.")
		}
	}
	return p.conntrack[family] == 1
}

// passthroughCapable reports whether at least one address family can recover
// original DNS destinations for exit-passthrough. IPv6 NFQUEUE obtains them
// directly from the queued packet and does not rely on conntrack.
func (p *magicDNSProxy) passthroughCapable() bool {
	if p.conntrackOK(0) {
		return true
	}
	if p.v6Mode() == ipv6ModeNFQueue {
		return p.listen6 && !p.dead6.Load()
	}
	return p.conntrackOK(1)
}

func (p *magicDNSProxy) familyPassthroughOK(family int) bool {
	if family == 1 && p.v6Mode() == ipv6ModeNFQueue {
		return p.listen6 && !p.dead6.Load()
	}
	return p.conntrackOK(family)
}

// familyMode narrows a passthrough mode for one family whose conntrack
// lookups fail: that chain keeps only the suffix rules, or none without
// xt_string.
func (p *magicDNSProxy) familyMode(mode string, family int, suffixes []string) string {
	if mode == "exit-passthrough" && !p.familyPassthroughOK(family) {
		if p.noString || len(suffixes) == 0 {
			return "off"
		}
		return "tailnet"
	}
	return mode
}

func (p *magicDNSProxy) familyRules(mode string, suffixes []string) (v4, v6 [][]string) {
	v4, _ = desiredRules(p.familyMode(mode, 0, suffixes), suffixes)
	v6Mode := p.familyMode(mode, 1, suffixes)
	if p.v6Mode() == ipv6ModeNFQueue {
		v6 = desiredNFQueueRules(v6Mode, suffixes)
	} else {
		_, v6 = desiredRules(v6Mode, suffixes)
	}
	return v4, v6
}

var ipTablesMatchesPath = "/proc/net/ip_tables_matches"

func xtStringMissing() bool {
	data, err := os.ReadFile(ipTablesMatchesPath)
	return err == nil && !strings.Contains("\n"+string(data), "\nstring\n")
}

func (p *magicDNSProxy) probeExitDoH(ctx context.Context, exitID string) string {
	var peers struct {
		Peer map[string]struct {
			ID         string
			PeerAPIURL []string
		}
	}
	dohURL := ""
	if err := p.backend.api(ctx, "GET", "status?peers=true", nil, &peers); err == nil {
		for _, peer := range peers.Peer {
			if peer.ID == exitID && len(peer.PeerAPIURL) > 0 {
				dohURL = strings.TrimSuffix(peer.PeerAPIURL[0], "/") + "/dns-query"
				break
			}
		}
	}
	if dohURL == "" {
		p.logOnce("exit", "the exit node has no PeerAPI; ordinary names go to the system resolver outside the tunnel.")
		return ""
	}
	// NS query for the root zone.
	probe := []byte{0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1}
	if _, err := p.queryDoH(ctx, dohURL, probe); err != nil {
		p.logOnce("exit", "the exit node does not offer DNS to this device; ordinary names go to the system resolver outside the tunnel.")
		return ""
	}
	p.logOnce("exit", "")
	return dohURL
}

func (p *magicDNSProxy) readPrivateDNS(ctx context.Context) {
	ctx, cancel := context.WithTimeout(ctx, 2*time.Second)
	defer cancel()
	mode := "unknown"
	if out, err := p.run(ctx, "/system/bin/cmd", "settings", "get", "global", "private_dns_mode"); err == nil {
		switch value := strings.TrimSpace(string(out)); value {
		case "", "null":
			mode = "opportunistic"
		case "off", "opportunistic", "hostname":
			mode = value
		}
	}
	if mode != p.privateDNS && (mode == "hostname" || mode == "opportunistic") {
		fmt.Fprintf(os.Stderr, "MagicDNS: Android Private DNS mode is %s; encrypted DNS bypasses tailnet name interception.\n", mode)
	}
	p.privateDNS = mode
}

func normalizeDNSName(name string) string {
	return strings.TrimSuffix(strings.ToLower(strings.TrimSpace(name)), ".")
}

func validDNSName(name string) bool {
	if name == "" || len(name) > 253 {
		return false
	}
	for _, label := range strings.Split(name, ".") {
		if label == "" || len(label) > 63 {
			return false
		}
		for _, c := range label {
			if !(c >= 'a' && c <= 'z' || c >= '0' && c <= '9' || c == '-' || c == '_') {
				return false
			}
		}
	}
	return true
}

func parseDNSRoutes(in map[string][]struct{ Addr string }) map[string][]netip.AddrPort {
	out := map[string][]netip.AddrPort{}
	for key, resolvers := range in {
		name := normalizeDNSName(key)
		if !validDNSName(name) {
			continue
		}
		addrs := []netip.AddrPort{}
		for _, r := range resolvers {
			if ap, err := netip.ParseAddrPort(r.Addr); err == nil {
				addrs = append(addrs, ap)
			} else if a, err := netip.ParseAddr(r.Addr); err == nil {
				addrs = append(addrs, netip.AddrPortFrom(a, 53))
			}
		}
		// A route whose resolvers are all unusable (DoH URLs) is skipped; an
		// empty resolver list means tailscaled answers it locally.
		if len(resolvers) > 0 && len(addrs) == 0 {
			continue
		}
		out[name] = addrs
	}
	return out
}

func dnsSuffixes(suffix string, routes map[string][]netip.AddrPort) []string {
	var out []string
	if suffix != "" {
		out = append(out, suffix)
	}
	keys := make([]string, 0, len(routes))
	for key := range routes {
		if key != suffix {
			keys = append(keys, key)
		}
	}
	sort.Strings(keys)
	out = append(out, keys...)
	if len(out) > magicDNSMaxSuffix {
		out = out[:magicDNSMaxSuffix]
	}
	return out
}

// wireHex returns the DNS wire encoding of name, including the root label,
// as space separated hex for iptables --hex-string.
func wireHex(name string) string {
	var parts []string
	for _, label := range strings.Split(name, ".") {
		parts = append(parts, fmt.Sprintf("%02x", len(label)))
		for i := 0; i < len(label); i++ {
			parts = append(parts, fmt.Sprintf("%02x", label[i]))
		}
	}
	return strings.Join(append(parts, "00"), " ")
}

// desiredRules returns the IPv4 and IPv6 nat chain contents, which are the
// same apart from the xt_string offsets. The QNAME starts after the IP, UDP
// and DNS headers: 20+8+12 = 40 in IPv4, 40+8+12 = 60 in IPv6 without
// extension headers. The search window ends 260 bytes later, which fits a
// maximal 255-byte QNAME. In the catch-all modes the IPv6 chain leaves
// link-local servers alone: conntrack carries no zone, so the proxy could not
// forward to them.
func desiredRules(mode string, suffixes []string) (v4, v6 [][]string) {
	if mode == "off" {
		return nil, nil
	}
	redirect := []string{"-p", "udp", "-j", "REDIRECT", "--to-ports", strconv.Itoa(magicDNSPort)}
	chain := func(from, to string, v6 bool) [][]string {
		// The proxy's forwarded queries carry the bypass mark. The connection
		// keeps netd's network selection for the forward (passthroughMark).
		rules := [][]string{{"-m", "mark", "--mark", "0x10000000/0x1e000000", "-j", "RETURN"},
			{"-j", "CONNMARK", "--save-mark", "--nfmask", "0x1ffff", "--ctmask", "0x1ffff"}}
		if mode != "tailnet" {
			if v6 {
				rules = append(rules, []string{"-d", "fe80::/10", "-j", "RETURN"})
			}
			return append(rules, redirect)
		}
		for _, suffix := range suffixes {
			rules = append(rules, append([]string{"-m", "string", "--algo", "bm", "--icase",
				"--from", from, "--to", to, "--hex-string", "|" + wireHex(suffix) + "|"}, redirect...))
		}
		return rules
	}
	return chain("40", "300", false), chain("60", "320", true)
}

// desiredNFQueueRules returns the IPv6 filter chain contents for stock GKI
// kernels lacking IPv6 NAT. Unlike REDIRECT, NFQUEUE supplies the outgoing
// interface index (NFQA_IFINDEX_OUTDEV) and skb mark (NFQA_MARK) directly, so
// fe80::/10 servers are intercepted in all modes without CONNMARK.
func desiredNFQueueRules(mode string, suffixes []string) [][]string {
	if mode == "off" {
		return nil
	}
	nfqueue := []string{"-p", "udp", "-j", "NFQUEUE", "--queue-num", strconv.Itoa(magicDNSPort), "--queue-bypass"}
	rules := [][]string{{"-m", "mark", "--mark", "0x10000000/0x1e000000", "-j", "RETURN"}}
	if mode != "tailnet" {
		return append(rules, nfqueue)
	}
	if len(suffixes) == 0 {
		return nil
	}
	for _, suffix := range suffixes {
		rules = append(rules, append([]string{"-m", "string", "--algo", "bm", "--icase",
			"--from", "60", "--to", "320", "--hex-string", "|" + wireHex(suffix) + "|"}, nfqueue...))
	}
	return rules
}

// ipv6FallbackRules rejects IPv6 DNS that the IPv4 proxy should answer, so
// netd retries via IPv4 DNS. With an exit node that is every query, keeping
// ordinary names off the physical network as with IPv6 NAT.
func ipv6FallbackRules(mode string, suffixes []string) [][]string {
	if mode == "off" {
		return nil
	}
	rules := [][]string{{"-m", "mark", "--mark", "0x10000000/0x1e000000", "-j", "RETURN"}}
	if strings.HasPrefix(mode, "exit") {
		return append(rules, []string{"-p", "udp", "-j", "REJECT", "--reject-with", "icmp6-port-unreachable"})
	}
	if len(suffixes) == 0 {
		return nil
	}
	for _, suffix := range suffixes {
		rules = append(rules, []string{"-m", "string", "--algo", "bm", "--icase",
			"--from", "60", "--to", "320", "--hex-string", "|" + wireHex(suffix) + "|",
			"-p", "udp", "-j", "REJECT", "--reject-with", "icmp6-port-unreachable"})
	}
	return rules
}

// applyRules reports false when the rule set could not be applied; it is
// retried on the next refresh.
func (p *magicDNSProxy) applyRules(ctx context.Context, family int, rules [][]string) bool {
	bin, table, chain := "/system/bin/iptables", "nat", magicDNSChain
	if family == 1 {
		bin = "/system/bin/ip6tables"
		switch p.v6Mode() {
		case ipv6ModeNFQueue:
			table, chain = "filter", magicDNSChain
		case ipv6ModeFallback:
			table, chain = "filter", magicDNSFallbackChain
		}
	}
	parts := make([]string, len(rules))
	for i, rule := range rules {
		parts[i] = strings.Join(rule, " ")
	}
	key := strings.Join(parts, "\n")
	if key == p.applied[family] {
		return true
	}
	p.applied[family], p.rulesOK[family] = "\x00", false
	ctx, cancel := context.WithTimeout(ctx, 10*time.Second)
	defer cancel()
	base := []string{"-w", "-t", table}
	if out, err := p.run(ctx, bin, append(base, "-F", chain)...); err != nil {
		p.logOnce(bin, "cannot flush the module chain: "+commandError(out, err))
		return false
	}
	for _, rule := range rules {
		if out, err := p.run(ctx, bin, append(append(base, "-A", chain), rule...)...); err != nil {
			_, _ = p.run(ctx, bin, append(base, "-F", chain)...)
			p.logOnce(bin, "rules not applied, DNS stays on the system path: "+commandError(out, err))
			return false
		}
	}
	p.applied[family], p.rulesOK[family] = key, true
	p.logOnce(bin, "")
	return true
}

func commandError(out []byte, err error) string {
	msg := strings.TrimSpace(strings.SplitN(string(out), "\n", 2)[0])
	if msg == "" {
		msg = err.Error()
	}
	return boundedText(msg, 200)
}

func (p *magicDNSProxy) flushRules() {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()
	_, _ = p.run(ctx, "/system/bin/iptables", "-w", "-t", "nat", "-F", magicDNSChain)
	_, _ = p.run(ctx, "/system/bin/ip6tables", "-w", "-t", "nat", "-F", magicDNSChain)
	_, _ = p.run(ctx, "/system/bin/ip6tables", "-w", "-t", "filter", "-F", magicDNSChain)
	_, _ = p.run(ctx, "/system/bin/ip6tables", "-w", "-t", "filter", "-F", magicDNSFallbackChain)
}

func (p *magicDNSProxy) writeState(now time.Time) {
	p.mu.RLock()
	f := magicDNSFile{Updated: now.Unix(), Mode: p.mode, Enabled: p.enabled, Generation: p.generation, ApplyFailed: p.applyFailed, NoString: p.noString, Rules: p.rulesOK[0], Rules6: p.rulesOK[1], IPv6Fallback: p.v6Mode() == ipv6ModeFallback, PrivateDNS: p.privateDNS, Upstream: "system", Daemon: p.daemon, ExitNode: p.prefsExit}
	p.mu.RUnlock()
	switch f.Mode {
	case "exit-doh":
		f.Upstream = "exit-node"
	case "exit-passthrough":
		f.Upstream = "passthrough"
	}
	data, err := json.Marshal(f)
	if err != nil {
		return
	}
	tmp := p.state + ".new"
	if os.WriteFile(tmp, data, 0600) == nil {
		_ = os.Rename(tmp, p.state)
	}
}

func readMagicDNSState(path string, now time.Time) *magicDNSState {
	file, err := os.Open(path)
	if err != nil {
		return nil
	}
	defer file.Close()
	var f magicDNSFile
	if json.NewDecoder(io.LimitReader(file, 4096)).Decode(&f) != nil {
		return nil
	}
	age := now.Unix() - f.Updated
	return &magicDNSState{Running: age >= 0 && age <= 20, Mode: f.Mode, Enabled: f.Enabled, generation: f.Generation, ApplyFailed: f.ApplyFailed, NoString: f.NoString, Rules: f.Rules, Rules6: f.Rules6, IPv6Fallback: f.IPv6Fallback, PrivateDNS: f.PrivateDNS, Upstream: f.Upstream, Daemon: f.Daemon, ExitNode: f.ExitNode}
}

// dnsQuestion parses a standard query with exactly one uncompressed question.
func dnsQuestion(pkt []byte) (name string, qtype uint16, end int, ok bool) {
	if len(pkt) < 12 || pkt[2]&0x80 != 0 || pkt[2]&0x78 != 0 || binary.BigEndian.Uint16(pkt[4:6]) != 1 {
		return "", 0, 0, false
	}
	offset := 12
	var labels []string
	for {
		if offset >= len(pkt) {
			return "", 0, 0, false
		}
		size := int(pkt[offset])
		offset++
		if size == 0 {
			break
		}
		if size > 63 || offset+size > len(pkt) {
			return "", 0, 0, false
		}
		labels = append(labels, strings.ToLower(string(pkt[offset:offset+size])))
		offset += size
	}
	if offset+4 > len(pkt) {
		return "", 0, 0, false
	}
	name = strings.Join(labels, ".")
	if len(name) > 253 {
		return "", 0, 0, false
	}
	return name, binary.BigEndian.Uint16(pkt[offset : offset+2]), offset + 4, true
}

// reply builds an answer without records: the client ID and question, QR, RD
// copied, RA, and rcode.
func reply(pkt []byte, end int, rcode byte) []byte {
	out := append([]byte(nil), pkt[:end]...)
	out[2] = 0x80 | pkt[2]&0x79
	out[3] = 0x80 | rcode&0x0f
	qd := uint16(0)
	if end > 12 {
		qd = 1
	}
	binary.BigEndian.PutUint16(out[4:6], qd)
	clear(out[6:12])
	return out
}

var dnsTypeNames = map[uint16]string{1: "A", 2: "NS", 5: "CNAME", 6: "SOA", 12: "PTR", 15: "MX", 16: "TXT", 28: "AAAA", 33: "SRV"}

func (p *magicDNSProxy) answer(ctx context.Context, pkt []byte, client netip.AddrPort) []byte {
	return p.answerQuery(ctx, pkt, func() (netip.AddrPort, uint32, error) {
		return p.origDst(client)
	})
}

func (p *magicDNSProxy) answerQuery(ctx context.Context, pkt []byte, lookup func() (netip.AddrPort, uint32, error)) []byte {
	if len(pkt) < 12 {
		return nil
	}
	name, qtype, end, ok := dnsQuestion(pkt)
	if !ok {
		return reply(pkt, 12, 1)
	}
	p.mu.RLock()
	suffix, routes, mode, exitDoH := p.suffix, p.routes, p.mode, p.exitDoH
	p.mu.RUnlock()

	var resp []byte
	var err error
	magic := suffix != "" && (name == suffix || strings.HasSuffix(name, "."+suffix))
	route, resolvers := "", []netip.AddrPort(nil)
	if !magic {
		for key, addrs := range routes {
			if len(key) > len(route) && (name == key || strings.HasSuffix(name, "."+key)) {
				route, resolvers = key, addrs
			}
		}
	}
	switch {
	case magic || route != "" && len(resolvers) == 0:
		typeName, known := dnsTypeNames[qtype]
		if !known {
			return reply(pkt, end, 0)
		}
		resp, err = p.queryLocal(ctx, name, typeName)
		if err == nil && magic && (resp[3]&0x0f == 2 || resp[3]&0x0f == 5) {
			resp[3] = resp[3]&0xf0 | 3
		}
	case route != "":
		err = errors.New("no resolver")
		for _, addr := range resolvers {
			if resp, err = queryTCP(ctx, addr, pkt); err == nil {
				break
			}
		}
	default:
		if mode == "exit-doh" {
			resp, err = p.queryDoH(ctx, exitDoH, pkt)
		}
		// A failed DoH query falls back to the server the system chose.
		if mode != "exit-doh" || err != nil {
			var dst netip.AddrPort
			var mark uint32
			if dst, mark, err = lookup(); err == nil {
				resp, err = p.forward(ctx, dst, mark, pkt)
			}
		}
	}
	if err != nil || len(resp) < 12 {
		return reply(pkt, end, 2)
	}
	copy(resp[0:2], pkt[0:2])
	resp[2] = resp[2]&^0x01 | pkt[2]&0x01
	if len(resp) > 512 && binary.BigEndian.Uint16(pkt[10:12]) == 0 {
		trunc := append(append([]byte(nil), resp[:12]...), pkt[12:end]...)
		trunc[2] |= 0x02
		binary.BigEndian.PutUint16(trunc[4:6], 1)
		clear(trunc[6:12])
		return trunc
	}
	return resp
}

func (p *magicDNSProxy) queryLocal(ctx context.Context, name, typeName string) ([]byte, error) {
	ctx, cancel := context.WithTimeout(ctx, 3*time.Second)
	defer cancel()
	var res struct{ Bytes []byte }
	if err := p.backend.api(ctx, "GET", "dns-query?name="+url.QueryEscape(name+".")+"&type="+typeName, nil, &res); err != nil {
		return nil, err
	}
	if len(res.Bytes) < 12 {
		return nil, errors.New("short reply")
	}
	return res.Bytes, nil
}

// queryTCP forwards over TCP, which the UDP-only interception never matches.
func queryTCP(ctx context.Context, addr netip.AddrPort, pkt []byte) ([]byte, error) {
	ctx, cancel := context.WithTimeout(ctx, 3*time.Second)
	defer cancel()
	conn, err := (&net.Dialer{}).DialContext(ctx, "tcp", addr.String())
	if err != nil {
		return nil, err
	}
	defer conn.Close()
	deadline, _ := ctx.Deadline()
	_ = conn.SetDeadline(deadline)
	msg := binary.BigEndian.AppendUint16(nil, uint16(len(pkt)))
	if _, err := conn.Write(append(msg, pkt...)); err != nil {
		return nil, err
	}
	var size [2]byte
	if _, err := io.ReadFull(conn, size[:]); err != nil {
		return nil, err
	}
	resp := make([]byte, binary.BigEndian.Uint16(size[:]))
	if _, err := io.ReadFull(conn, resp); err != nil {
		return nil, err
	}
	return resp, nil
}

// passthroughMark is the bypass mark plus the netId and explicit bit that netd
// set on the original query, saved by the chain's CONNMARK rule.
func passthroughMark(ctmark uint32) int {
	return int(0x10020000 | ctmark&0x1ffff)
}

// queryPassthrough sends the query to the server the system chose, over the
// family of that address, marked to bypass table 52 and the module chain and
// routed on netd's network.
func queryPassthrough(ctx context.Context, dst netip.AddrPort, ctmark uint32, pkt []byte) ([]byte, error) {
	if dst.Addr().IsLoopback() && dst.Port() == magicDNSPort {
		return nil, errors.New("no original destination")
	}
	if dst.Addr().IsLinkLocalUnicast() && dst.Addr().Zone() == "" {
		return nil, errors.New("missing interface scope")
	}
	ctx, cancel := context.WithTimeout(ctx, 3*time.Second)
	defer cancel()
	control := func(_, _ string, raw syscall.RawConn) error {
		var socketErr error
		if err := raw.Control(func(fd uintptr) {
			socketErr = syscall.SetsockoptInt(int(fd), syscall.SOL_SOCKET, syscall.SO_MARK, passthroughMark(ctmark))
		}); err != nil {
			return err
		}
		return socketErr
	}
	network := "udp4"
	if dst.Addr().Is6() {
		network = "udp6"
	}
	// SO_MARK is a SOL_SOCKET option, so the same control applies to IPv6.
	conn, err := (&net.Dialer{Control: control}).DialContext(ctx, network, dst.String())
	if err != nil {
		return nil, err
	}
	defer conn.Close()
	deadline, _ := ctx.Deadline()
	_ = conn.SetDeadline(deadline)
	if _, err := conn.Write(pkt); err != nil {
		return nil, err
	}
	resp := make([]byte, 64<<10)
	for {
		n, err := conn.Read(resp)
		if err != nil {
			return nil, err
		}
		if n >= 12 && resp[0] == pkt[0] && resp[1] == pkt[1] {
			return resp[:n], nil
		}
	}
}

// Conntrack netlink constants (linux/netfilter/nfnetlink_conntrack.h).
const (
	ctaTupleOrig    = 1
	ctaTupleReply   = 2
	ctaTupleIP      = 1
	ctaTupleProto   = 2
	ctaIPv4Src      = 1
	ctaIPv4Dst      = 2
	ctaIPv6Src      = 3
	ctaIPv6Dst      = 4
	ctaProtoNum     = 1
	ctaProtoSrcPort = 2
	ctaProtoDstPort = 3
	ctaMark         = 8
	nlaNested       = 0x8000
)

func nlAttr(typ uint16, data ...[]byte) []byte {
	var body []byte
	for _, d := range data {
		body = append(body, d...)
	}
	out := binary.NativeEndian.AppendUint16(nil, uint16(4+len(body)))
	out = binary.NativeEndian.AppendUint16(out, typ)
	out = append(out, body...)
	for len(out)%4 != 0 {
		out = append(out, 0)
	}
	return out
}

func nlFind(b []byte, typ uint16) []byte {
	for len(b) >= 4 {
		size := int(binary.NativeEndian.Uint16(b))
		if size < 4 || size > len(b) {
			return nil
		}
		if binary.NativeEndian.Uint16(b[2:])&^0xc000 == typ {
			return b[4:size]
		}
		b = b[min((size+3)&^3, len(b)):]
	}
	return nil
}

// conntrackQuery builds IPCTNL_MSG_CT_GET for the reply tuple of a redirected
// query: 127.0.0.1:1053 or [::1]:1053 (REDIRECT in OUTPUT rewrites to the
// loopback address of the family) back to the client.
func conntrackQuery(client netip.AddrPort) []byte {
	family, src, dst := byte(syscall.AF_INET), uint16(ctaIPv4Src), uint16(ctaIPv4Dst)
	local := netip.AddrFrom4([4]byte{127, 0, 0, 1})
	if client.Addr().Is6() {
		family, src, dst, local = syscall.AF_INET6, ctaIPv6Src, ctaIPv6Dst, netip.IPv6Loopback()
	}
	tuple := nlAttr(ctaTupleReply|nlaNested,
		nlAttr(ctaTupleIP|nlaNested, nlAttr(src, local.AsSlice()), nlAttr(dst, client.Addr().AsSlice())),
		nlAttr(ctaTupleProto|nlaNested, nlAttr(ctaProtoNum, []byte{syscall.IPPROTO_UDP}),
			nlAttr(ctaProtoSrcPort, binary.BigEndian.AppendUint16(nil, magicDNSPort)),
			nlAttr(ctaProtoDstPort, binary.BigEndian.AppendUint16(nil, client.Port()))))
	msg := binary.NativeEndian.AppendUint32(nil, uint32(16+4+len(tuple)))
	msg = binary.NativeEndian.AppendUint16(msg, 1<<8|1) // NFNL_SUBSYS_CTNETLINK, IPCTNL_MSG_CT_GET
	msg = binary.NativeEndian.AppendUint16(msg, 1)      // NLM_F_REQUEST
	msg = binary.NativeEndian.AppendUint32(msg, 1)
	msg = binary.NativeEndian.AppendUint32(msg, 0)
	msg = append(msg, family, 0, 0, 0) // nfgenmsg
	return append(msg, tuple...)
}

// parseConntrackOrigDst returns the original destination and the connection
// mark (0 when absent).
func parseConntrackOrigDst(msg []byte) (netip.AddrPort, uint32, error) {
	if len(msg) < 20 || int(binary.NativeEndian.Uint32(msg)) > len(msg) || binary.NativeEndian.Uint32(msg) < 20 {
		return netip.AddrPort{}, 0, errors.New("short conntrack reply")
	}
	msg = msg[:binary.NativeEndian.Uint32(msg)]
	switch typ := binary.NativeEndian.Uint16(msg[4:]); {
	case typ == 2: // NLMSG_ERROR
		return netip.AddrPort{}, 0, fmt.Errorf("conntrack: %w", syscall.Errno(-int32(binary.NativeEndian.Uint32(msg[16:]))))
	case typ>>8 != 1:
		return netip.AddrPort{}, 0, errors.New("unexpected conntrack reply")
	}
	orig := nlFind(msg[20:], ctaTupleOrig)
	ip := nlFind(orig, ctaTupleIP)
	port := nlFind(nlFind(orig, ctaTupleProto), ctaProtoDstPort)
	var addr netip.Addr
	if dst := nlFind(ip, ctaIPv4Dst); len(dst) == 4 {
		addr = netip.AddrFrom4([4]byte(dst))
	} else if dst := nlFind(ip, ctaIPv6Dst); len(dst) == 16 {
		addr = netip.AddrFrom16([16]byte(dst))
	}
	if !addr.IsValid() || len(port) != 2 {
		return netip.AddrPort{}, 0, errors.New("no original destination")
	}
	var mark uint32
	if m := nlFind(msg[20:], ctaMark); len(m) == 4 {
		mark = binary.BigEndian.Uint32(m)
	}
	return netip.AddrPortFrom(addr, binary.BigEndian.Uint16(port)), mark, nil
}

// conntrackOrigDst looks up where a REDIRECTed query was going. IP_ORIGDSTADDR
// cannot be used: it reports the rewritten header, 127.0.0.1:1053.
func conntrackOrigDst(client netip.AddrPort) (netip.AddrPort, uint32, error) {
	client = netip.AddrPortFrom(client.Addr().Unmap(), client.Port())
	if !client.Addr().IsValid() {
		return netip.AddrPort{}, 0, errors.New("no client address")
	}
	fd, err := syscall.Socket(syscall.AF_NETLINK, syscall.SOCK_RAW|syscall.SOCK_CLOEXEC, 12) // NETLINK_NETFILTER
	if err != nil {
		return netip.AddrPort{}, 0, err
	}
	defer syscall.Close(fd)
	_ = syscall.SetsockoptTimeval(fd, syscall.SOL_SOCKET, syscall.SO_RCVTIMEO, &syscall.Timeval{Sec: 1})
	if err := syscall.Sendto(fd, conntrackQuery(client), 0, &syscall.SockaddrNetlink{Family: syscall.AF_NETLINK}); err != nil {
		return netip.AddrPort{}, 0, err
	}
	buf := make([]byte, 4096)
	n, _, err := syscall.Recvfrom(fd, buf, 0)
	if err != nil {
		return netip.AddrPort{}, 0, err
	}
	return parseConntrackOrigDst(buf[:n])
}

// sameHelperExe reports whether exe (a /proc/PID/exe link) is this helper:
// either self, or a module tree a live update moved to trash, as in
// sc_magicdns_running.
func sameHelperExe(self, exe string) bool {
	exe = strings.TrimSuffix(exe, " (deleted)")
	trashed, _ := filepath.Match(dataDir+"/trash/*/bin/shellscaled-web", exe)
	return exe == self || trashed
}

// nudgeMagicDNS asks the running proxy to refresh now. The pid must belong to
// this same helper binary (see sameHelperExe).
func nudgeMagicDNS() {
	data, err := os.ReadFile(magicDNSPIDPath)
	fields := strings.Fields(string(data))
	if err != nil || len(fields) == 0 {
		return
	}
	pid, err := strconv.Atoi(fields[0])
	if err != nil || pid <= 1 {
		return
	}
	self, err := os.Readlink("/proc/self/exe")
	if exe, err2 := os.Readlink("/proc/" + fields[0] + "/exe"); err == nil && err2 == nil && sameHelperExe(self, exe) {
		_ = syscall.Kill(pid, syscall.SIGUSR1)
	}
}

func (p *magicDNSProxy) queryDoH(ctx context.Context, dohURL string, pkt []byte) ([]byte, error) {
	req, err := http.NewRequestWithContext(ctx, "POST", dohURL, bytes.NewReader(pkt))
	if err != nil {
		return nil, err
	}
	req.Header.Set("Content-Type", "application/dns-message")
	req.Header.Set("Accept", "application/dns-message")
	res, err := p.doh.Do(req)
	if err != nil {
		return nil, err
	}
	defer res.Body.Close()
	if res.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("DoH %d", res.StatusCode)
	}
	resp, err := io.ReadAll(io.LimitReader(res.Body, 64<<10+1))
	if err != nil || len(resp) > 64<<10 {
		return nil, errors.New("bad DoH reply")
	}
	return resp, nil
}

func defaultIfName(ifindex int) string {
	if ifindex <= 0 {
		return ""
	}
	if ifi, err := net.InterfaceByIndex(ifindex); err == nil && ifi.Name != "" {
		return ifi.Name
	}
	return strconv.Itoa(ifindex)
}

func (p *magicDNSProxy) resolveZone(outdev uint32) string {
	if outdev == 0 {
		return ""
	}
	if p.ifName != nil {
		return p.ifName(int(outdev))
	}
	return defaultIfName(int(outdev))
}

func nfqMsg(msgType, flags uint16, seq uint32, family byte, queue uint16, attrs ...[]byte) []byte {
	var body []byte
	for _, a := range attrs {
		body = append(body, a...)
	}
	msg := binary.NativeEndian.AppendUint32(nil, uint32(20+len(body)))
	msg = binary.NativeEndian.AppendUint16(msg, nfnlSubsysQueue<<8|msgType)
	msg = binary.NativeEndian.AppendUint16(msg, flags)
	msg = binary.NativeEndian.AppendUint32(msg, seq)
	msg = binary.NativeEndian.AppendUint32(msg, 0)
	msg = append(msg, family, 0)
	msg = binary.BigEndian.AppendUint16(msg, queue)
	return append(msg, body...)
}

func nfqVerdictMsg(queue uint16, packetID, verdict uint32) []byte {
	hdr := make([]byte, 8)
	binary.BigEndian.PutUint32(hdr[0:4], verdict)
	binary.BigEndian.PutUint32(hdr[4:8], packetID)
	return nfqMsg(nfqnlMsgVerdict, 1, 0, syscall.AF_UNSPEC, queue, nlAttr(nfqaVerdictHdr, hdr))
}

type nfqPacket struct {
	id      uint32
	mark    uint32
	outdev  uint32
	payload []byte
}

func parseNFQPacket(attrs []byte) (nfqPacket, bool) {
	hdr := nlFind(attrs, nfqaPacketHdr)
	payload := nlFind(attrs, nfqaPayload)
	if len(hdr) < 4 || len(payload) == 0 {
		return nfqPacket{}, false
	}
	var mark, outdev uint32
	if m := nlFind(attrs, nfqaMark); len(m) == 4 {
		mark = binary.BigEndian.Uint32(m)
	}
	if o := nlFind(attrs, nfqaIfindexOutdev); len(o) == 4 {
		outdev = binary.BigEndian.Uint32(o)
	}
	return nfqPacket{
		id:      binary.BigEndian.Uint32(hdr[:4]),
		mark:    mark,
		outdev:  outdev,
		payload: payload,
	}, true
}

func parseIPv6UDPDNS(payload []byte) (dns []byte, src, dst netip.AddrPort, ok bool) {
	if len(payload) < 48 || payload[0]>>4 != 6 || payload[6] != syscall.IPPROTO_UDP {
		return nil, netip.AddrPort{}, netip.AddrPort{}, false
	}
	ipLen := int(binary.BigEndian.Uint16(payload[4:6]))
	if ipLen < 8 || 40+ipLen > len(payload) {
		return nil, netip.AddrPort{}, netip.AddrPort{}, false
	}
	udpLen := int(binary.BigEndian.Uint16(payload[44:46]))
	if udpLen < 8 || udpLen > ipLen {
		return nil, netip.AddrPort{}, netip.AddrPort{}, false
	}
	srcAddr := netip.AddrFrom16([16]byte(payload[8:24]))
	dstAddr := netip.AddrFrom16([16]byte(payload[24:40]))
	if srcAddr.Is4In6() || dstAddr.Is4In6() {
		return nil, netip.AddrPort{}, netip.AddrPort{}, false
	}
	srcPort := binary.BigEndian.Uint16(payload[40:42])
	dstPort := binary.BigEndian.Uint16(payload[42:44])
	if srcPort == 0 || dstPort == 0 {
		return nil, netip.AddrPort{}, netip.AddrPort{}, false
	}
	return payload[48 : 40+udpLen], netip.AddrPortFrom(srcAddr, srcPort), netip.AddrPortFrom(dstAddr, dstPort), true
}

type nfqConn struct {
	queue uint16
	file  *os.File
	read  func([]byte) (int, error)
	write func([]byte) (int, error)
	close func() error
}

func (q *nfqConn) verdict(packetID, verdict uint32) error {
	_, err := q.write(nfqVerdictMsg(q.queue, packetID, verdict))
	return err
}

func (q *nfqConn) Close() error {
	if q.close != nil {
		return q.close()
	}
	return nil
}

func nfqExchangeACK(f *os.File, req []byte) error {
	if _, err := f.Write(req); err != nil {
		return err
	}
	buf := make([]byte, 4096)
	n, err := f.Read(buf)
	if err != nil {
		return err
	}
	return nlErrno(buf[:n])
}

func openNFQueue(queue uint16) (*nfqConn, error) {
	fd, err := syscall.Socket(syscall.AF_NETLINK, syscall.SOCK_RAW|syscall.SOCK_CLOEXEC|syscall.SOCK_NONBLOCK, 12) // NETLINK_NETFILTER
	if err != nil {
		return nil, err
	}
	if err := syscall.Bind(fd, &syscall.SockaddrNetlink{Family: syscall.AF_NETLINK}); err != nil {
		_ = syscall.Close(fd)
		return nil, err
	}
	_ = syscall.SetsockoptInt(fd, syscall.SOL_SOCKET, syscall.SO_RCVBUF, 512<<10)
	f := os.NewFile(uintptr(fd), "nfqueue")
	_ = f.SetDeadline(time.Now().Add(2 * time.Second))
	bindReq := nfqMsg(nfqnlMsgConfig, 5, 1, syscall.AF_UNSPEC, queue,
		nlAttr(nfqaCfgCmd, []byte{nfqnlCfgCmdBind, 0, 0, 0}))
	if err := nfqExchangeACK(f, bindReq); err != nil {
		_ = f.Close()
		return nil, err
	}
	params := append(binary.BigEndian.AppendUint32(nil, 0xffff), nfqnlCopyPacket)
	mask := binary.BigEndian.AppendUint32(nil, nfqaCfgFailOpen)
	flags := binary.BigEndian.AppendUint32(nil, nfqaCfgFailOpen)
	cfgReq := nfqMsg(nfqnlMsgConfig, 5, 2, syscall.AF_UNSPEC, queue,
		nlAttr(nfqaCfgParams, params), nlAttr(nfqaCfgMask, mask), nlAttr(nfqaCfgFlags, flags))
	if err := nfqExchangeACK(f, cfgReq); err != nil {
		if errors.Is(err, syscall.EINVAL) || errors.Is(err, syscall.EOPNOTSUPP) {
			err = nfqExchangeACK(f, nfqMsg(nfqnlMsgConfig, 5, 3, syscall.AF_UNSPEC, queue, nlAttr(nfqaCfgParams, params)))
		}
		if err != nil {
			_, _ = f.Write(nfqMsg(nfqnlMsgConfig, 1, 4, syscall.AF_UNSPEC, queue, nlAttr(nfqaCfgCmd, []byte{nfqnlCfgCmdUnbind, 0, 0, 0})))
			_ = f.Close()
			return nil, err
		}
	}
	_ = f.SetDeadline(time.Time{})
	return &nfqConn{
		queue: queue,
		file:  f,
		read:  f.Read,
		write: f.Write,
		close: func() error {
			_, _ = f.Write(nfqMsg(nfqnlMsgConfig, 1, 0, syscall.AF_UNSPEC, queue, nlAttr(nfqaCfgCmd, []byte{nfqnlCfgCmdUnbind, 0, 0, 0})))
			return f.Close()
		},
	}, nil
}

func openTransparentUDP6() (int, error) {
	fd, err := syscall.Socket(syscall.AF_INET6, syscall.SOCK_DGRAM|syscall.SOCK_CLOEXEC, syscall.IPPROTO_UDP)
	if err != nil {
		return -1, err
	}
	for _, opt := range [][3]int{
		{syscall.SOL_SOCKET, syscall.SO_REUSEADDR, 1},
		{syscall.SOL_SOCKET, soReusePort, 1},
		{syscall.IPPROTO_IPV6, ipv6Transparent, 1},
		{syscall.SOL_SOCKET, syscall.SO_MARK, 0x10020000},
	} {
		if err := syscall.SetsockoptInt(fd, opt[0], opt[1], opt[2]); err != nil {
			_ = syscall.Close(fd)
			return -1, err
		}
	}
	return fd, nil
}

func sendTransparentUDP6(origDst, client netip.AddrPort, outdev uint32, resp []byte) error {
	if !origDst.Addr().Is6() || origDst.Addr().Is4In6() || !client.Addr().Is6() || client.Addr().Is4In6() {
		return errors.New("non-ipv6 address")
	}
	fd, err := openTransparentUDP6()
	if err != nil {
		return err
	}
	defer syscall.Close(fd)
	bindSA := &syscall.SockaddrInet6{
		Port: int(origDst.Port()),
		Addr: origDst.Addr().As16(),
	}
	if origDst.Addr().IsLinkLocalUnicast() || origDst.Addr().IsLinkLocalMulticast() {
		bindSA.ZoneId = outdev
	}
	if err := syscall.Bind(fd, bindSA); err != nil {
		return err
	}
	dstSA := &syscall.SockaddrInet6{
		Port: int(client.Port()),
		Addr: client.Addr().As16(),
	}
	if client.Addr().IsLinkLocalUnicast() || client.Addr().IsLinkLocalMulticast() {
		dstSA.ZoneId = outdev
	}
	return syscall.Sendto(fd, resp, 0, dstSA)
}

func probeTransparentUDP6() error {
	fd, err := openTransparentUDP6()
	if err != nil {
		return err
	}
	return syscall.Close(fd)
}

func probeIPv6NFQueueRuntime() error {
	if err := probeTransparentUDP6(); err != nil {
		return err
	}
	nfq, err := openNFQueue(magicDNSPort)
	if err != nil {
		return err
	}
	return nfq.Close()
}

func (p *magicDNSProxy) probeIPv6(ctx context.Context) (*net.UDPConn, *nfqConn) {
	probeCtx, probeCancel := context.WithTimeout(ctx, 5*time.Second)
	_, err := p.run(probeCtx, "/system/bin/ip6tables", "-w", "-t", "nat", "-S", "OUTPUT")
	probeCancel()
	if err == nil {
		p.ipv6Mode = ipv6ModeNAT
		p.ipv6Fallback = false
		conn6, err := net.ListenUDP("udp6", &net.UDPAddr{IP: net.IPv6loopback, Port: magicDNSPort})
		if err != nil {
			fmt.Fprintln(os.Stderr, "MagicDNS: cannot listen on [::1]:1053 ("+err.Error()+"); IPv6 DNS is not redirected.")
		}
		p.listen6 = conn6 != nil
		return conn6, nil
	}
	filterCtx, filterCancel := context.WithTimeout(ctx, 5*time.Second)
	_, filterErr := p.run(filterCtx, "/system/bin/ip6tables", "-w", "-t", "filter", "-S", magicDNSChain)
	filterCancel()
	if filterErr == nil && p.probeTProxy6() == nil {
		if nfq, err := p.openNFQ(magicDNSPort); err == nil {
			p.ipv6Mode = ipv6ModeNFQueue
			p.ipv6Fallback = false
			p.listen6 = true
			return nil, nfq
		} else {
			fmt.Fprintln(os.Stderr, "MagicDNS: IPv6 NFQUEUE unavailable ("+err.Error()+"); falling back.")
		}
	}
	p.ipv6Mode = ipv6ModeFallback
	p.ipv6Fallback = true
	p.listen6 = false
	fmt.Fprintln(os.Stderr, "MagicDNS: IPv6 NAT and NFQUEUE interception unavailable; tailnet queries to IPv6 DNS retry via system IPv4 DNS. A working IPv4 DNS server is required.")
	return nil, nil
}

func (p *magicDNSProxy) magicDNSRun(ctx context.Context) error {
	// Before anything else: unhandled SIGUSR1 would kill the process.
	nudge := make(chan os.Signal, 1)
	signal.Notify(nudge, syscall.SIGUSR1)
	defer signal.Stop(nudge)
	conn, err := net.ListenUDP("udp4", &net.UDPAddr{IP: net.IPv4(127, 0, 0, 1), Port: magicDNSPort})
	if err != nil {
		return fmt.Errorf("listen magicdns proxy: %w", err)
	}
	conn6, nfq := p.probeIPv6(ctx)
	defer os.Remove(p.state)
	var wg sync.WaitGroup
	defer wg.Wait()
	ctx, cancel := context.WithCancel(ctx)
	defer cancel()
	wg.Add(1)
	go func() {
		defer wg.Done()
		// Flush before closing the sockets: a successor cannot bind 1053 and
		// apply its rules until they are closed.
		defer conn.Close()
		if conn6 != nil {
			defer conn6.Close()
		}
		if nfq != nil {
			defer nfq.Close()
		}
		defer p.flushRules()
		p.refresh(ctx)
		ticker := time.NewTicker(5 * time.Second)
		defer ticker.Stop()
		for {
			select {
			case <-ctx.Done():
				return
			case <-ticker.C:
				p.refresh(ctx)
			case <-nudge:
				p.refresh(ctx)
			}
		}
	}()
	slots := make(chan struct{}, 64)
	if conn6 != nil {
		wg.Add(1)
		go func() {
			defer wg.Done()
			if err := p.serve(ctx, conn6, slots); err != nil {
				fmt.Fprintln(os.Stderr, "MagicDNS: IPv6 listener stopped: "+err.Error())
				p.dead6.Store(true)
				select {
				case nudge <- syscall.SIGUSR1:
				default:
				}
			}
		}()
	} else if nfq != nil {
		wg.Add(1)
		go func() {
			defer wg.Done()
			if err := p.serveNFQueue(ctx, nfq, slots); err != nil {
				fmt.Fprintln(os.Stderr, "MagicDNS: IPv6 NFQUEUE listener stopped: "+err.Error())
				p.dead6.Store(true)
				select {
				case nudge <- syscall.SIGUSR1:
				default:
				}
			}
		}()
	}
	return p.serve(ctx, conn, slots)
}

func (b *backend) magicDNSProxy(ctx context.Context) error {
	return newMagicDNSProxy(b).magicDNSRun(ctx)
}

func (p *magicDNSProxy) handleNFQMessage(ctx context.Context, q *nfqConn, attrs []byte, slots chan struct{}) {
	pkt, ok := parseNFQPacket(attrs)
	if !ok {
		return
	}
	dnsPkt, src, dst, valid := parseIPv6UDPDNS(pkt.payload)
	if !valid || len(dnsPkt) < 12 || (pkt.mark&0x1e000000) == 0x10000000 ||
		(dst.Addr().IsLoopback() && dst.Port() == magicDNSPort) ||
		((dst.Addr().IsLinkLocalUnicast() || src.Addr().IsLinkLocalUnicast()) && pkt.outdev == 0) {
		_ = q.verdict(pkt.id, nfAccept)
		return
	}
	select {
	case slots <- struct{}{}:
	default:
		_ = q.verdict(pkt.id, nfAccept)
		return
	}
	query := append([]byte(nil), dnsPkt...)
	if err := q.verdict(pkt.id, nfDrop); err != nil {
		<-slots
		return
	}
	go func() {
		defer func() { <-slots }()
		resp := p.answerQuery(ctx, query, func() (netip.AddrPort, uint32, error) {
			target := dst
			if target.Addr().IsLinkLocalUnicast() {
				zone := p.resolveZone(pkt.outdev)
				if zone == "" {
					return netip.AddrPort{}, 0, errors.New("missing interface scope")
				}
				target = netip.AddrPortFrom(target.Addr().WithZone(zone), target.Port())
			}
			return target, pkt.mark, nil
		})
		if resp != nil {
			if err := p.reply6(dst, src, pkt.outdev, resp); err != nil {
				p.logOnce("reply6", "cannot send IPv6 MagicDNS reply: "+err.Error())
			}
		}
	}()
}

func (p *magicDNSProxy) serveNFQueue(ctx context.Context, q *nfqConn, slots chan struct{}) error {
	buf := make([]byte, 68<<10)
	for {
		n, err := q.read(buf)
		if err != nil {
			if errors.Is(err, syscall.EINTR) || errors.Is(err, syscall.ENOBUFS) {
				continue
			}
			if ctx.Err() != nil || errors.Is(err, net.ErrClosed) || errors.Is(err, os.ErrClosed) {
				return nil
			}
			return err
		}
		for msg := buf[:n]; len(msg) >= 16; {
			size := int(binary.NativeEndian.Uint32(msg[:4]))
			if size < 16 || size > len(msg) {
				break
			}
			if binary.NativeEndian.Uint16(msg[4:6]) == nfnlSubsysQueue<<8|nfqnlMsgPacket && size >= 20 {
				p.handleNFQMessage(ctx, q, msg[20:size], slots)
			}
			msg = msg[min((size+3)&^3, len(msg)):]
		}
	}
}

// serve answers queries on one listener; both share the concurrency slots.
func (p *magicDNSProxy) serve(ctx context.Context, conn *net.UDPConn, slots chan struct{}) error {
	for {
		buf := make([]byte, 1500)
		n, addr, err := conn.ReadFromUDP(buf)
		if err != nil {
			if ctx.Err() != nil || errors.Is(err, net.ErrClosed) {
				return nil
			}
			return err
		}
		select {
		case slots <- struct{}{}:
		default:
			continue
		}
		go func() {
			defer func() { <-slots }()
			if resp := p.answer(ctx, buf[:n], addr.AddrPort()); resp != nil {
				_, _ = conn.WriteToUDP(resp, addr)
			}
		}()
	}
}
