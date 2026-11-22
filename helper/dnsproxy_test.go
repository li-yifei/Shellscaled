package main

import (
	"context"
	"encoding/binary"
	"encoding/json"
	"errors"
	"io"
	"net"
	"net/http"
	"net/netip"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"syscall"
	"testing"
	"time"
)

func testQuery(id uint16, name string, qtype uint16) []byte {
	pkt := []byte{byte(id >> 8), byte(id), 0x01, 0, 0, 1, 0, 0, 0, 0, 0, 0}
	for _, label := range strings.Split(name, ".") {
		pkt = append(pkt, byte(len(label)))
		pkt = append(pkt, label...)
	}
	pkt = append(pkt, 0)
	pkt = binary.BigEndian.AppendUint16(pkt, qtype)
	return binary.BigEndian.AppendUint16(pkt, 1)
}

func dnsTestProxy(t *testing.T, handler func(*http.Request) (int, string)) (*magicDNSProxy, *int) {
	t.Helper()
	calls := 0
	var mu sync.Mutex
	b := &backend{client: &http.Client{Transport: transportFunc(func(r *http.Request) (*http.Response, error) {
		mu.Lock()
		calls++
		mu.Unlock()
		code, body := handler(r)
		return &http.Response{StatusCode: code, Body: io.NopCloser(strings.NewReader(body)), Header: http.Header{}}, nil
	})}}
	p := newMagicDNSProxy(b)
	p.state = filepath.Join(t.TempDir(), "magicdns.json")
	p.run = func(context.Context, string, ...string) ([]byte, error) { return nil, nil }
	p.ctProbe = func(int) error { return syscall.ENOENT }
	p.sweep = func(bool) (int, error) { return 0, nil }
	enabled := filepath.Join(t.TempDir(), "magicdns-enabled")
	if err := os.WriteFile(enabled, nil, 0600); err != nil {
		t.Fatal(err)
	}
	old := magicDNSEnabledFile
	magicDNSEnabledFile = enabled
	t.Cleanup(func() { magicDNSEnabledFile = old })
	return p, &calls
}

func TestWireHex(t *testing.T) {
	if got := wireHex("tail1234.ts.net"); got != "08 74 61 69 6c 31 32 33 34 02 74 73 03 6e 65 74 00" {
		t.Fatal(got)
	}
}

func TestDesiredRules(t *testing.T) {
	if v4, v6 := desiredRules("off", []string{"tail1234.ts.net"}); len(v4) != 0 || len(v6) != 0 {
		t.Fatal("off mode must not install rules")
	}
	v4, v6 := desiredRules("tailnet", []string{"tail1234.ts.net", "corp.example"})
	if len(v4) != 4 || len(v6) != 4 {
		t.Fatalf("got %d/%d rules", len(v4), len(v6))
	}
	for _, chain := range [][][]string{v4, v6} {
		if strings.Join(chain[0], " ") != markReturn || strings.Join(chain[1], " ") != saveMark {
			t.Fatalf("chain head %v", chain[:2])
		}
	}
	for i, c := range []struct {
		rule   []string
		window string
	}{{v4[2], "--from 40 --to 300"}, {v6[2], "--from 60 --to 320"}} {
		r := strings.Join(c.rule, " ")
		for _, want := range []string{"-m string --algo bm --icase " + c.window, "|08 74 61 69 6c 31 32 33 34 02 74 73 03 6e 65 74 00|", "-p udp -j REDIRECT --to-ports 1053"} {
			if !strings.Contains(r, want) {
				t.Fatalf("family %d rule %q lacks %q", i, r, want)
			}
		}
	}
	for _, mode := range []string{"exit-doh", "exit-passthrough"} {
		v4, v6 = desiredRules(mode, []string{"tail1234.ts.net"})
		// Link-local IPv6 servers stay on the system path: no zone to forward with.
		v6head := [][]string{v6[0], v6[1], v6[len(v6)-1]}
		for _, chain := range [][][]string{v4, v6head} {
			if len(chain) != 3 || strings.Join(chain[0], " ") != markReturn || strings.Join(chain[1], " ") != saveMark || strings.Join(chain[2], " ") != "-p udp -j REDIRECT --to-ports 1053" {
				t.Fatalf("%s rules %v %v", mode, v4, v6)
			}
		}
		if len(v6) != 4 || strings.Join(v6[2], " ") != linkLocalReturn {
			t.Fatalf("%s v6 rules %v", mode, v6)
		}
	}
}

const (
	markReturn = "-m mark --mark 0x10000000/0x1e000000 -j RETURN"
	saveMark   = "-j CONNMARK --save-mark --nfmask 0x1ffff --ctmask 0x1ffff"

	linkLocalReturn = "-d fe80::/10 -j RETURN"
)

func TestSelectMagicDNSMode(t *testing.T) {
	for _, c := range []struct {
		exit, doh, suffixes, noString, ct bool
		want                              string
	}{
		{false, false, false, false, true, "off"},
		{false, false, false, true, true, "off"},
		{false, false, true, false, true, "tailnet"},
		// Without xt_string tailnet names cannot be matched; nothing is caught wholesale.
		{false, false, true, true, true, "off"},
		{true, true, true, false, true, "exit-doh"},
		{true, true, false, true, true, "exit-doh"},
		{true, false, true, false, true, "exit-passthrough"},
		{true, false, false, true, true, "exit-passthrough"},
		// Without conntrack lookups nothing is caught wholesale.
		{false, false, true, true, false, "off"},
		{true, false, true, false, false, "tailnet"},
		{true, false, true, true, false, "off"},
		{true, true, true, false, false, "exit-doh"},
	} {
		if got := selectMagicDNSMode(c.exit, c.doh, c.suffixes, c.noString, c.ct); got != c.want {
			t.Errorf("%+v: got %s", c, got)
		}
	}
}

func TestConntrackOrigDst(t *testing.T) {
	client := netip.MustParseAddrPort("192.168.1.5:34567")
	q := conntrackQuery(client)
	if int(binary.NativeEndian.Uint32(q)) != len(q) || binary.NativeEndian.Uint16(q[4:]) != 0x101 || q[16] != 2 {
		t.Fatalf("header %x", q[:20])
	}
	reply := nlFind(q[20:], ctaTupleReply)
	ip, proto := nlFind(reply, ctaTupleIP), nlFind(reply, ctaTupleProto)
	if string(nlFind(ip, ctaIPv4Src)) != "\x7f\x00\x00\x01" || string(nlFind(ip, ctaIPv4Dst)) != "\xc0\xa8\x01\x05" ||
		nlFind(proto, ctaProtoNum)[0] != 17 || binary.BigEndian.Uint16(nlFind(proto, ctaProtoSrcPort)) != 1053 ||
		binary.BigEndian.Uint16(nlFind(proto, ctaProtoDstPort)) != 34567 {
		t.Fatalf("query %x", q)
	}

	// A crafted IPCTNL_MSG_CT_NEW reply: orig 192.168.1.5:34567 -> 1.1.1.1:53.
	be := func(v uint16) []byte { return binary.BigEndian.AppendUint16(nil, v) }
	orig := nlAttr(ctaTupleOrig|nlaNested,
		nlAttr(ctaTupleIP|nlaNested, nlAttr(ctaIPv4Src, []byte{192, 168, 1, 5}), nlAttr(ctaIPv4Dst, []byte{1, 1, 1, 1})),
		nlAttr(ctaTupleProto|nlaNested, nlAttr(ctaProtoNum, []byte{17}), nlAttr(ctaProtoSrcPort, be(34567)), nlAttr(ctaProtoDstPort, be(53))))
	body := append([]byte{2, 0, 0, 0}, append(nlAttr(3, []byte{0, 0, 0, 8}), append(orig, append(reply, nlAttr(ctaMark, []byte{0, 1, 0, 0x64})...)...)...)...)
	msg := binary.NativeEndian.AppendUint32(nil, uint32(16+len(body)))
	msg = binary.NativeEndian.AppendUint16(msg, 0x100)
	msg = append(append(msg, make([]byte, 10)...), body...)
	if got, mark, err := parseConntrackOrigDst(msg); err != nil || got != netip.MustParseAddrPort("1.1.1.1:53") || mark != 0x10064 || passthroughMark(mark) != 0x10030064 {
		t.Fatalf("got %v %x %v", got, mark, err)
	}

	nlErr := binary.NativeEndian.AppendUint32(nil, 36)
	nlErr = binary.NativeEndian.AppendUint16(nlErr, 2)
	nlErr = append(nlErr, make([]byte, 10)...)
	nlErr = binary.NativeEndian.AppendUint32(nlErr, uint32(0xfffffffe)) // -ENOENT
	nlErr = append(nlErr, q[:16]...)
	if _, _, err := parseConntrackOrigDst(nlErr); !errors.Is(err, syscall.ENOENT) {
		t.Fatalf("error reply: %v", err)
	}
	// IPv6: reply tuple [::1]:1053 -> client, orig client -> 2001:db8:53::1:53.
	client6 := netip.MustParseAddrPort("[2001:db8::5]:34567")
	q6 := conntrackQuery(client6)
	reply6 := nlFind(q6[20:], ctaTupleReply)
	ip6 := nlFind(reply6, ctaTupleIP)
	if q6[16] != syscall.AF_INET6 || string(nlFind(ip6, ctaIPv6Src)) != string(netip.IPv6Loopback().AsSlice()) ||
		string(nlFind(ip6, ctaIPv6Dst)) != string(client6.Addr().AsSlice()) || nlFind(ip6, ctaIPv4Src) != nil ||
		binary.BigEndian.Uint16(nlFind(nlFind(reply6, ctaTupleProto), ctaProtoSrcPort)) != 1053 {
		t.Fatalf("v6 query %x", q6)
	}
	server6 := netip.MustParseAddr("2001:db8:53::1")
	orig6 := nlAttr(ctaTupleOrig|nlaNested,
		nlAttr(ctaTupleIP|nlaNested, nlAttr(ctaIPv6Src, client6.Addr().AsSlice()), nlAttr(ctaIPv6Dst, server6.AsSlice())),
		nlAttr(ctaTupleProto|nlaNested, nlAttr(ctaProtoNum, []byte{17}), nlAttr(ctaProtoSrcPort, be(34567)), nlAttr(ctaProtoDstPort, be(53))))
	body6 := append([]byte{10, 0, 0, 0}, append(orig6, append(reply6, nlAttr(ctaMark, []byte{0, 1, 0, 0x65})...)...)...)
	msg6 := binary.NativeEndian.AppendUint32(nil, uint32(16+len(body6)))
	msg6 = binary.NativeEndian.AppendUint16(msg6, 0x100)
	msg6 = append(append(msg6, make([]byte, 10)...), body6...)
	if got, mark, err := parseConntrackOrigDst(msg6); err != nil || got != netip.AddrPortFrom(server6, 53) || mark != 0x10065 {
		t.Fatalf("v6 got %v %x %v", got, mark, err)
	}

	for _, bad := range [][]byte{nil, msg[:19], msg[:len(msg)-4]} {
		if _, _, err := parseConntrackOrigDst(bad); err == nil {
			t.Fatalf("accepted %x", bad)
		}
	}
}

func TestAnswerPassthrough(t *testing.T) {
	server, err := net.ListenUDP("udp", &net.UDPAddr{IP: net.IPv4(127, 0, 0, 1)})
	if err != nil {
		t.Fatal(err)
	}
	defer server.Close()
	go func() {
		buf := make([]byte, 512)
		n, addr, err := server.ReadFromUDP(buf)
		if err != nil {
			return
		}
		stray := reply(testQuery(1, "other.example", 1), 12, 0)
		_, _ = server.WriteToUDP(stray, addr)
		_, _ = server.WriteToUDP(reply(buf[:n], n, 3), addr)
	}()
	p, calls := dnsTestProxy(t, func(*http.Request) (int, string) { return 500, "" })
	p.suffix, p.mode = "tail1234.ts.net", "exit-passthrough"
	client := netip.MustParseAddrPort("192.0.2.5:40000")
	p.origDst = func(c netip.AddrPort) (netip.AddrPort, uint32, error) {
		if c != client {
			t.Errorf("lookup for %v", c)
		}
		return server.LocalAddr().(*net.UDPAddr).AddrPort(), 0, nil
	}
	out := p.answer(context.Background(), testQuery(0x7777, "www.example.com", 1), client)
	if *calls != 0 || len(out) < 12 || out[0] != 0x77 || out[1] != 0x77 || out[3]&0x0f != 3 {
		t.Fatalf("calls=%d reply=%x", *calls, out)
	}
}

func TestDNSQuestion(t *testing.T) {
	pkt := testQuery(7, "Host.Tail1234.ts.net", 28)
	name, qtype, end, ok := dnsQuestion(pkt)
	if !ok || name != "host.tail1234.ts.net" || qtype != 28 || end != len(pkt) {
		t.Fatalf("%q %d %d %v", name, qtype, end, ok)
	}
	response := append([]byte(nil), pkt...)
	response[2] |= 0x80
	twoQuestions := append([]byte(nil), pkt...)
	twoQuestions[5] = 2
	for _, bad := range [][]byte{response, twoQuestions, pkt[:12], pkt[:len(pkt)-2]} {
		if _, _, _, ok := dnsQuestion(bad); ok {
			t.Fatalf("accepted %x", bad)
		}
	}
}

func TestReplyBuilder(t *testing.T) {
	pkt := testQuery(0xabcd, "a.example", 1)
	pkt[11] = 1 // ARCOUNT, must be cleared
	_, _, end, _ := dnsQuestion(pkt)
	out := reply(pkt, end, 2)
	if out[0] != 0xab || out[1] != 0xcd || out[2] != 0x81 || out[3] != 0x82 {
		t.Fatalf("header %x", out[:4])
	}
	if binary.BigEndian.Uint16(out[4:6]) != 1 || binary.BigEndian.Uint16(out[6:8]) != 0 || binary.BigEndian.Uint16(out[10:12]) != 0 {
		t.Fatalf("counts %x", out[4:12])
	}
	if string(out[12:]) != string(pkt[12:end]) {
		t.Fatal("question not kept")
	}
}

func TestAnswerLocal(t *testing.T) {
	p, calls := dnsTestProxy(t, func(r *http.Request) (int, string) {
		if r.URL.Path != "/localapi/v0/dns-query" || r.URL.Query().Get("name") != "host.tail1234.ts.net." || r.URL.Query().Get("type") != "AAAA" {
			t.Errorf("unexpected request %s", r.URL)
		}
		body, _ := json.Marshal(struct{ Bytes []byte }{reply(testQuery(1, "host.tail1234.ts.net", 28), 12, 2)})
		return 200, string(body)
	})
	p.suffix, p.mode = "tail1234.ts.net", "tailnet"
	out := p.answer(context.Background(), testQuery(0x4242, "host.tail1234.ts.net", 28), netip.AddrPort{})
	if out[0] != 0x42 || out[1] != 0x42 || out[3]&0x0f != 3 || out[2]&0x01 != 1 {
		t.Fatalf("reply %x", out)
	}
	out = p.answer(context.Background(), testQuery(5, "host.tail1234.ts.net", 65), netip.AddrPort{})
	if *calls != 1 || out[3]&0x0f != 0 || binary.BigEndian.Uint16(out[6:8]) != 0 {
		t.Fatalf("qtype 65 must be local NODATA: calls=%d reply=%x", *calls, out)
	}
}

func TestAnswerNoOriginalDstServfail(t *testing.T) {
	p, calls := dnsTestProxy(t, func(*http.Request) (int, string) { return 500, "" })
	p.suffix, p.mode = "tail1234.ts.net", "exit-passthrough"
	for _, dst := range []netip.AddrPort{{}, netip.MustParseAddrPort("127.0.0.1:1053")} {
		p.origDst = func(netip.AddrPort) (netip.AddrPort, uint32, error) {
			if !dst.IsValid() {
				return dst, 0, errors.New("conntrack: no such file or directory")
			}
			return dst, 0, nil
		}
		out := p.answer(context.Background(), testQuery(9, "www.example.com", 1), netip.MustParseAddrPort("192.0.2.5:40000"))
		if *calls != 0 || out[3]&0x0f != 2 {
			t.Fatalf("dst=%v calls=%d reply=%x", dst, *calls, out)
		}
	}
	bad := testQuery(9, "www.example.com", 1)
	bad[5] = 0
	if out := p.answer(context.Background(), bad, netip.AddrPort{}); out[3]&0x0f != 1 {
		t.Fatalf("FORMERR expected, got %x", out)
	}
}

func TestRefreshModes(t *testing.T) {
	running := true
	var commands []string
	p, _ := dnsTestProxy(t, func(r *http.Request) (int, string) {
		switch r.URL.Path + "?" + r.URL.RawQuery {
		case "/localapi/v0/status?peers=false":
			if !running {
				return 200, `{"BackendState":"Stopped"}`
			}
			return 200, `{"BackendState":"Running","CurrentTailnet":{"MagicDNSSuffix":"tail1234.ts.net"},"ExitNodeStatus":{"ID":"nExit"}}`
		case "/localapi/v0/status?peers=true":
			return 200, `{"Peer":{"k":{"ID":"nExit"}}}`
		case "/localapi/v0/prefs?":
			return 200, `{"ExitNodeID":"nExit"}`
		case "/localapi/v0/dns-config?":
			return 503, "no netmap"
		}
		return 404, ""
	})
	p.run = func(_ context.Context, name string, args ...string) ([]byte, error) {
		commands = append(commands, name+" "+strings.Join(args, " "))
		if strings.HasSuffix(name, "cmd") {
			return []byte("hostname\n"), nil
		}
		return nil, nil
	}
	p.refresh(context.Background())
	if p.mode != "exit-passthrough" || p.exitDoH != "" || p.privateDNS != "hostname" {
		t.Fatalf("mode=%s doh=%q private=%s", p.mode, p.exitDoH, p.privateDNS)
	}
	state := readMagicDNSState(p.state, time.Now())
	if state == nil || !state.Running || state.Mode != "exit-passthrough" || !state.Rules || !state.Rules6 || state.Upstream != "passthrough" ||
		state.Daemon != "Running" || state.ExitNode != "nExit" {
		t.Fatalf("state %+v", state)
	}
	for _, c := range commands {
		if strings.Contains(c, "iptables") && !strings.Contains(c, " shellscaled_dns") {
			t.Fatalf("command outside module chain: %s", c)
		}
	}
	running = false
	p.refresh(context.Background())
	if p.mode != "off" {
		t.Fatalf("mode=%s", p.mode)
	}
	if state := readMagicDNSState(p.state, time.Now()); state == nil || state.Daemon != "Stopped" || state.ExitNode != "" {
		t.Fatalf("state %+v", state)
	}
}

func TestApplyRulesFailureFlushes(t *testing.T) {
	p, _ := dnsTestProxy(t, func(*http.Request) (int, string) { return 500, "" })
	var flushes int
	p.run = func(_ context.Context, _ string, args ...string) ([]byte, error) {
		if args[3] == "-F" {
			flushes++
			return nil, nil
		}
		return []byte("Couldn't load match `string'"), errors.New("exit status 2")
	}
	v4, _ := desiredRules("tailnet", []string{"tail1234.ts.net"})
	p.applyRules(context.Background(), 0, v4)
	if p.rulesOK[0] || flushes != 2 {
		t.Fatalf("ok=%v flushes=%d", p.rulesOK[0], flushes)
	}
}

func TestRefreshExitProbeRetryAndRoutesGate(t *testing.T) {
	corpDNS, dohOK := false, false
	p, _ := dnsTestProxy(t, func(r *http.Request) (int, string) {
		switch r.URL.Path + "?" + r.URL.RawQuery {
		case "/localapi/v0/status?peers=false":
			return 200, `{"BackendState":"Running","CurrentTailnet":{"MagicDNSSuffix":"tail1234.ts.net"},"ExitNodeStatus":{"ID":"nExit"}}`
		case "/localapi/v0/status?peers=true":
			return 200, `{"Peer":{"k":{"ID":"nExit","PeerAPIURL":["http://100.64.0.2:1234"]}}}`
		case "/localapi/v0/prefs?":
			if corpDNS {
				return 200, `{"CorpDNS":true}`
			}
			return 200, `{"CorpDNS":false}`
		case "/localapi/v0/dns-config?":
			return 200, `{"Routes":{"corp.example.":[{"Addr":"10.0.0.53"}]}}`
		}
		return 404, ""
	})
	p.doh = &http.Client{Transport: transportFunc(func(*http.Request) (*http.Response, error) {
		if !dohOK {
			return nil, errors.New("timeout")
		}
		return &http.Response{StatusCode: 200, Body: io.NopCloser(strings.NewReader("")), Header: http.Header{}}, nil
	})}
	p.refresh(context.Background())
	if p.mode != "exit-passthrough" || len(p.routes) != 0 {
		t.Fatalf("mode=%s routes=%d", p.mode, len(p.routes))
	}
	corpDNS, dohOK = true, true
	p.refresh(context.Background())
	if p.mode != "exit-doh" || len(p.routes) != 1 {
		t.Fatalf("retry: mode=%s routes=%d", p.mode, len(p.routes))
	}
	dohOK = false
	for i := 0; i < 6 && p.mode == "exit-doh"; i++ {
		p.refresh(context.Background())
	}
	if p.mode != "exit-passthrough" {
		t.Fatalf("lost DoH must fall back, mode=%s", p.mode)
	}
}

func TestRefreshStringFallback(t *testing.T) {
	p, _ := dnsTestProxy(t, func(r *http.Request) (int, string) {
		if r.URL.Path+"?"+r.URL.RawQuery == "/localapi/v0/status?peers=false" {
			return 200, `{"BackendState":"Running","CurrentTailnet":{"MagicDNSSuffix":"tail1234.ts.net"}}`
		}
		return 404, ""
	})
	matches := filepath.Join(t.TempDir(), "ip_tables_matches")
	old := ipTablesMatchesPath
	ipTablesMatchesPath = matches
	defer func() { ipTablesMatchesPath = old }()
	// A failure while the kernel lists xt_string is transient and retried.
	_ = os.WriteFile(matches, []byte("mark\nstring\n"), 0600)
	var appends []string
	p.run = func(_ context.Context, name string, args ...string) ([]byte, error) {
		if len(args) > 3 && args[3] == "-A" {
			rule := strings.Join(args[5:], " ")
			appends = append(appends, rule)
			if strings.Contains(rule, "-m string") {
				return []byte("Couldn't load match `string'"), errors.New("exit status 2")
			}
		}
		return nil, nil
	}
	p.refresh(context.Background())
	if p.mode != "tailnet" || p.noString || p.rulesOK[0] {
		t.Fatalf("transient: mode=%s ok=%v", p.mode, p.rulesOK)
	}
	appends = nil
	p.refresh(context.Background())
	if len(appends) == 0 {
		t.Fatal("failed rules must be retried")
	}
	// Without xt_string nothing is redirected, and the state says why.
	_ = os.WriteFile(matches, []byte("mark\n"), 0600)
	p.refresh(context.Background())
	if p.mode != "off" || !p.noString {
		t.Fatalf("mode=%s noString=%v appends=%q", p.mode, p.noString, appends)
	}
	appends = nil
	p.refresh(context.Background())
	if p.mode != "off" || len(appends) != 0 {
		t.Fatalf("missing xt_string must stick without reapplying: mode=%s appends=%q", p.mode, appends)
	}
	if state := readMagicDNSState(p.state, time.Now()); state == nil || !state.NoString || state.Mode != "off" {
		t.Fatalf("state %+v", state)
	}
}

func TestRefreshDisabledRedirectsNothing(t *testing.T) {
	probeAllowed := false
	p, _ := dnsTestProxy(t, func(r *http.Request) (int, string) {
		switch r.URL.Path + "?" + r.URL.RawQuery {
		case "/localapi/v0/status?peers=false":
			return 200, `{"BackendState":"Running","CurrentTailnet":{"MagicDNSSuffix":"tail1234.ts.net"},"ExitNodeStatus":{"ID":"nExit"}}`
		case "/localapi/v0/prefs?":
			return 200, `{"ExitNodeID":"nExit"}`
		case "/localapi/v0/status?peers=true":
			if !probeAllowed {
				t.Error("disabled MagicDNS probed the exit node's DoH")
			}
		}
		return 404, ""
	})
	p.ctProbe = func(int) error { t.Error("disabled MagicDNS probed conntrack"); return syscall.ENOENT }
	enabledFile := magicDNSEnabledFile
	magicDNSEnabledFile = filepath.Join(t.TempDir(), "absent")
	swept := 0
	p.sweep = func(bool) (int, error) { swept++; return 0, nil }
	var appends []string
	p.run = func(_ context.Context, _ string, args ...string) ([]byte, error) {
		if len(args) > 3 && args[3] == "-A" {
			appends = append(appends, strings.Join(args, " "))
		}
		return nil, nil
	}
	p.refresh(context.Background())
	if p.mode != "off" || len(appends) != 0 {
		t.Fatalf("disabled MagicDNS redirected DNS: mode=%s appends=%q", p.mode, appends)
	}
	if swept != 1 {
		t.Fatalf("the flow reset must keep running while MagicDNS is off: %d sweeps", swept)
	}
	if state := readMagicDNSState(p.state, time.Now()); state == nil || state.Enabled || state.Mode != "off" {
		t.Fatalf("state %+v", state)
	}

	// Turning it off after it was on flushes the chains.
	probeAllowed = true
	p.ctProbe = func(int) error { return syscall.ENOENT }
	magicDNSEnabledFile = enabledFile
	p.refresh(context.Background())
	if p.mode == "off" || len(appends) == 0 {
		t.Fatalf("enabled: mode=%s appends=%q", p.mode, appends)
	}
	var flushed []string
	p.run = func(_ context.Context, name string, args ...string) ([]byte, error) {
		if len(args) > 3 && args[3] == "-F" {
			flushed = append(flushed, name)
		}
		return nil, nil
	}
	magicDNSEnabledFile = filepath.Join(t.TempDir(), "absent")
	p.refresh(context.Background())
	if p.mode != "off" || len(flushed) < 2 {
		t.Fatalf("disabling left rules in place: mode=%s flushed=%q", p.mode, flushed)
	}
}

func TestRefreshWithoutConntrack(t *testing.T) {
	p, _ := dnsTestProxy(t, func(r *http.Request) (int, string) {
		if r.URL.Path+"?"+r.URL.RawQuery == "/localapi/v0/status?peers=false" {
			return 200, `{"BackendState":"Running","CurrentTailnet":{"MagicDNSSuffix":"tail1234.ts.net"},"ExitNodeStatus":{"ID":"nExit"}}`
		}
		return 404, ""
	})
	probes := 0
	p.ctProbe = func(int) error { probes++; return syscall.EPERM }
	p.refresh(context.Background())
	p.refresh(context.Background())
	if p.mode != "tailnet" || probes != 2 {
		t.Fatalf("mode=%s probes=%d", p.mode, probes)
	}
}

// One family's failing conntrack lookups narrow only that family's chain.
func TestRefreshConntrackPerFamily(t *testing.T) {
	for _, bad := range []int{0, 1} {
		p, _ := dnsTestProxy(t, func(r *http.Request) (int, string) {
			if r.URL.Path+"?"+r.URL.RawQuery == "/localapi/v0/status?peers=false" {
				return 200, `{"BackendState":"Running","CurrentTailnet":{"MagicDNSSuffix":"tail1234.ts.net"},"ExitNodeStatus":{"ID":"nExit"}}`
			}
			return 404, ""
		})
		p.ctProbe = func(family int) error {
			if family == bad {
				return syscall.EOPNOTSUPP
			}
			return syscall.ENOENT
		}
		chains := map[string][]string{}
		p.run = func(_ context.Context, name string, args ...string) ([]byte, error) {
			if args[3] == "-A" {
				chains[name] = append(chains[name], strings.Join(args[5:], " "))
			}
			return nil, nil
		}
		p.refresh(context.Background())
		v4, v6 := chains["/system/bin/iptables"], chains["/system/bin/ip6tables"]
		good, narrowed := v4, v6
		if bad == 0 {
			good, narrowed = v6, v4
		}
		if p.mode != "exit-passthrough" || good[len(good)-1] != "-p udp -j REDIRECT --to-ports 1053" ||
			len(narrowed) != 3 || !strings.Contains(narrowed[2], "-m string") {
			t.Fatalf("bad=%d mode=%s v4=%q v6=%q", bad, p.mode, v4, v6)
		}
	}
}

// A dead [::1] listener hands IPv6 DNS back to the system path.
func TestRefreshDeadIPv6Listener(t *testing.T) {
	p, _ := dnsTestProxy(t, func(r *http.Request) (int, string) {
		if r.URL.Path+"?"+r.URL.RawQuery == "/localapi/v0/status?peers=false" {
			return 200, `{"BackendState":"Running","CurrentTailnet":{"MagicDNSSuffix":"tail1234.ts.net"}}`
		}
		return 404, ""
	})
	var v6 []string
	p.run = func(_ context.Context, name string, args ...string) ([]byte, error) {
		if strings.HasSuffix(name, "ip6tables") {
			v6 = append(v6, strings.Join(args[3:], " "))
		}
		return nil, nil
	}
	p.refresh(context.Background())
	if !p.rulesOK[1] || len(v6) != 4 {
		t.Fatalf("ok=%v v6=%q", p.rulesOK, v6)
	}
	v6 = nil
	p.dead6.Store(true)
	p.refresh(context.Background())
	p.refresh(context.Background())
	if p.listen6 || p.rulesOK[1] || len(v6) != 1 || v6[0] != "-F "+magicDNSChain {
		t.Fatalf("listen6=%v ok=%v v6=%q", p.listen6, p.rulesOK, v6)
	}
	if state := readMagicDNSState(p.state, time.Now()); state == nil || state.Rules6 || !state.Rules {
		t.Fatalf("state %+v", state)
	}
}

func TestRefreshIPv6NAT(t *testing.T) {
	p, _ := dnsTestProxy(t, func(r *http.Request) (int, string) {
		if r.URL.Path+"?"+r.URL.RawQuery == "/localapi/v0/status?peers=false" {
			return 200, `{"BackendState":"Running","CurrentTailnet":{"MagicDNSSuffix":"tail1234.ts.net"},"ExitNodeStatus":{"ID":"nExit"}}`
		}
		return 404, ""
	})
	var v6 []string
	p.run = func(_ context.Context, name string, args ...string) ([]byte, error) {
		if strings.HasSuffix(name, "ip6tables") {
			if args[1] != "-t" || args[2] != "nat" {
				t.Errorf("ip6tables outside nat: %v", args)
			}
			if args[3] == "-A" {
				v6 = append(v6, strings.Join(args[5:], " "))
			}
		}
		return nil, nil
	}
	p.refresh(context.Background())
	if p.mode != "exit-passthrough" || len(v6) != 4 || v6[0] != markReturn || v6[2] != linkLocalReturn || v6[3] != "-p udp -j REDIRECT --to-ports 1053" {
		t.Fatalf("mode=%s v6=%q", p.mode, v6)
	}
	if state := readMagicDNSState(p.state, time.Now()); state == nil || !state.Rules6 {
		t.Fatalf("state %+v", state)
	}

	// Without the [::1] listener the IPv6 chain is left untouched.
	q, _ := dnsTestProxy(t, func(r *http.Request) (int, string) {
		if r.URL.Path+"?"+r.URL.RawQuery == "/localapi/v0/status?peers=false" {
			return 200, `{"BackendState":"Running","CurrentTailnet":{"MagicDNSSuffix":"tail1234.ts.net"}}`
		}
		return 404, ""
	})
	q.listen6 = false
	q.run = func(_ context.Context, name string, args ...string) ([]byte, error) {
		if strings.HasSuffix(name, "ip6tables") {
			t.Errorf("ip6tables without listener: %v", args)
		}
		return nil, nil
	}
	q.refresh(context.Background())
	if q.mode != "tailnet" || !q.rulesOK[0] || q.rulesOK[1] {
		t.Fatalf("mode=%s ok=%v", q.mode, q.rulesOK)
	}
}

func TestRefreshIPv6WithoutNAT(t *testing.T) {
	p, _ := dnsTestProxy(t, func(r *http.Request) (int, string) {
		if r.URL.Path+"?"+r.URL.RawQuery == "/localapi/v0/status?peers=false" {
			return 200, `{"BackendState":"Running","CurrentTailnet":{"MagicDNSSuffix":"tail1234.ts.net"}}`
		}
		return 404, ""
	})
	p.ipv6Fallback = true
	p.listen6 = false // The fallback needs only the IPv4 listener.
	var rules []string
	p.run = func(_ context.Context, name string, args ...string) ([]byte, error) {
		if strings.HasSuffix(name, "ip6tables") {
			if args[2] != "filter" {
				t.Fatalf("IPv6 NAT used on unsupported kernel: %v", args)
			}
			rules = append(rules, strings.Join(args[3:], " "))
		}
		return nil, nil
	}
	p.refresh(context.Background())
	if len(rules) != 3 || !strings.Contains(rules[2], "--from 60 --to 320") ||
		!strings.Contains(rules[2], "|"+wireHex("tail1234.ts.net")+"|") ||
		!strings.HasSuffix(rules[2], "-p udp -j REJECT --reject-with icmp6-port-unreachable") {
		t.Fatalf("fallback must reject only tailnet DNS: %q", rules)
	}
	state := readMagicDNSState(p.state, time.Now())
	if state == nil || !state.Rules || !state.Rules6 || !state.IPv6Fallback {
		t.Fatalf("fallback state %+v", state)
	}
	// Disconnect clears the filter chain.
	rules = nil
	p.backend.client.Transport = transportFunc(func(*http.Request) (*http.Response, error) {
		return &http.Response{StatusCode: 200, Body: io.NopCloser(strings.NewReader(`{"BackendState":"Stopped"}`)), Header: http.Header{}}, nil
	})
	p.refresh(context.Background())
	if len(rules) != 1 || rules[0] != "-F "+magicDNSFallbackChain {
		t.Fatalf("disconnect leaves fallback rules: %q", rules)
	}
}

func TestIPv6FallbackRulesExitNode(t *testing.T) {
	for _, mode := range []string{"exit-doh", "exit-passthrough"} {
		rules := ipv6FallbackRules(mode, nil)
		if len(rules) != 2 || strings.Join(rules[1], " ") != "-p udp -j REJECT --reject-with icmp6-port-unreachable" {
			t.Fatalf("%s: every IPv6 query must retry via the IPv4 proxy: %q", mode, rules)
		}
	}
	if rules := ipv6FallbackRules("tailnet", nil); rules != nil {
		t.Fatalf("tailnet mode without suffixes: %q", rules)
	}
}

func TestAnswerPassthroughIPv6(t *testing.T) {
	server, err := net.ListenUDP("udp6", &net.UDPAddr{IP: net.IPv6loopback})
	if err != nil {
		t.Skip("no IPv6 loopback:", err)
	}
	defer server.Close()
	go func() {
		buf := make([]byte, 512)
		if n, addr, err := server.ReadFromUDP(buf); err == nil {
			_, _ = server.WriteToUDP(reply(buf[:n], n, 3), addr)
		}
	}()
	p, calls := dnsTestProxy(t, func(*http.Request) (int, string) { return 500, "" })
	p.suffix, p.mode = "tail1234.ts.net", "exit-passthrough"
	client := netip.MustParseAddrPort("[2001:db8::5]:40000")
	p.origDst = func(c netip.AddrPort) (netip.AddrPort, uint32, error) {
		if c != client {
			t.Errorf("lookup for %v", c)
		}
		return server.LocalAddr().(*net.UDPAddr).AddrPort(), 0x10064, nil
	}
	out := p.answer(context.Background(), testQuery(0x6666, "www.example.com", 28), client)
	if *calls != 0 || len(out) < 12 || out[0] != 0x66 || out[1] != 0x66 || out[3]&0x0f != 3 {
		t.Fatalf("calls=%d reply=%x", *calls, out)
	}
	// The loopback listener itself is never a forward target.
	p.origDst = func(netip.AddrPort) (netip.AddrPort, uint32, error) {
		return netip.MustParseAddrPort("[::1]:1053"), 0, nil
	}
	if out := p.answer(context.Background(), testQuery(1, "www.example.com", 28), client); out[3]&0x0f != 2 {
		t.Fatalf("reply %x", out)
	}
}

func TestApplyRulesRetry(t *testing.T) {
	p, _ := dnsTestProxy(t, func(*http.Request) (int, string) { return 500, "" })
	fail, runs := true, 0
	p.run = func(context.Context, string, ...string) ([]byte, error) {
		runs++
		if fail {
			return []byte("Another app is currently holding the xtables lock."), errors.New("exit status 4")
		}
		return nil, nil
	}
	v4, _ := desiredRules("exit-passthrough", nil)
	if p.applyRules(context.Background(), 0, v4) || p.rulesOK[0] {
		t.Fatal("failure reported as applied")
	}
	fail, runs = false, 0
	if !p.applyRules(context.Background(), 0, v4) || !p.rulesOK[0] || runs != 1+len(v4) {
		t.Fatalf("retry: ok=%v runs=%d", p.rulesOK[0], runs)
	}
	runs = 0
	if !p.applyRules(context.Background(), 0, v4) || runs != 0 {
		t.Fatalf("unchanged rules reapplied: runs=%d", runs)
	}
}

func TestAnswerDoHFailureFallsBack(t *testing.T) {
	server, err := net.ListenUDP("udp", &net.UDPAddr{IP: net.IPv4(127, 0, 0, 1)})
	if err != nil {
		t.Fatal(err)
	}
	defer server.Close()
	go func() {
		buf := make([]byte, 512)
		if n, addr, err := server.ReadFromUDP(buf); err == nil {
			_, _ = server.WriteToUDP(reply(buf[:n], n, 0), addr)
		}
	}()
	p, _ := dnsTestProxy(t, func(*http.Request) (int, string) { return 500, "" })
	p.mode, p.exitDoH = "exit-doh", "http://100.64.0.2:1234/dns-query"
	p.doh = &http.Client{Transport: transportFunc(func(*http.Request) (*http.Response, error) {
		return nil, errors.New("timeout")
	})}
	p.origDst = func(netip.AddrPort) (netip.AddrPort, uint32, error) {
		return server.LocalAddr().(*net.UDPAddr).AddrPort(), 0, nil
	}
	out := p.answer(context.Background(), testQuery(0x1234, "www.example.com", 1), netip.MustParseAddrPort("192.0.2.5:40000"))
	if len(out) < 12 || out[3]&0x0f != 0 {
		t.Fatalf("reply %x", out)
	}
}

func TestSameHelperExe(t *testing.T) {
	self := "/data/adb/modules/shellscaled/bin/shellscaled-web"
	for exe, want := range map[string]bool{
		self: true,
		dataDir + "/trash/1761800000/bin/shellscaled-web":           true,
		dataDir + "/trash/1761800000/bin/shellscaled-web (deleted)": true,
		self + " (deleted)":                          true,
		dataDir + "/trash/1761800000/bin/tailscaled": false,
		dataDir + "/trash/a/b/bin/shellscaled-web":   false,
		"/data/local/tmp/shellscaled-web":            false,
	} {
		if got := sameHelperExe(self, exe); got != want {
			t.Errorf("sameHelperExe(%q) = %v, want %v", exe, got, want)
		}
	}
}

func testIPv6UDPPacket(src, dst netip.AddrPort, payload []byte) []byte {
	pkt := make([]byte, 48+len(payload))
	pkt[0] = 0x60
	binary.BigEndian.PutUint16(pkt[4:6], uint16(8+len(payload)))
	pkt[6] = syscall.IPPROTO_UDP
	pkt[7] = 64
	copy(pkt[8:24], src.Addr().AsSlice())
	copy(pkt[24:40], dst.Addr().AsSlice())
	binary.BigEndian.PutUint16(pkt[40:42], src.Port())
	binary.BigEndian.PutUint16(pkt[42:44], dst.Port())
	binary.BigEndian.PutUint16(pkt[44:46], uint16(8+len(payload)))
	copy(pkt[48:], payload)
	return pkt
}

func testNFQPacketMsg(queue uint16, packetID, mark, outdev uint32, ipPayload []byte) []byte {
	hdr := make([]byte, 7)
	binary.BigEndian.PutUint32(hdr[0:4], packetID)
	binary.BigEndian.PutUint16(hdr[4:6], 0x86dd)
	var attrs [][]byte
	attrs = append(attrs, nlAttr(nfqaPacketHdr, hdr))
	if mark != 0 {
		attrs = append(attrs, nlAttr(nfqaMark, binary.BigEndian.AppendUint32(nil, mark)))
	}
	if outdev != 0 {
		attrs = append(attrs, nlAttr(nfqaIfindexOutdev, binary.BigEndian.AppendUint32(nil, outdev)))
	}
	attrs = append(attrs, nlAttr(nfqaPayload, ipPayload))
	return nfqMsg(nfqnlMsgPacket, 0, 0, syscall.AF_INET6, queue, attrs...)
}

func TestDesiredNFQueueRules(t *testing.T) {
	if got := desiredNFQueueRules("off", []string{"tail1234.ts.net"}); len(got) != 0 {
		t.Fatalf("off mode must not install rules: %v", got)
	}
	if got := desiredNFQueueRules("tailnet", nil); len(got) != 0 {
		t.Fatalf("tailnet without suffixes must not install rules: %v", got)
	}
	rules := desiredNFQueueRules("tailnet", []string{"tail1234.ts.net", "corp.example"})
	if len(rules) != 3 || strings.Join(rules[0], " ") != markReturn {
		t.Fatalf("unexpected tailnet nfqueue rules: %v", rules)
	}
	for _, r := range rules[1:] {
		joined := strings.Join(r, " ")
		if strings.Contains(joined, "CONNMARK") {
			t.Fatalf("nfqueue rule must not use CONNMARK: %q", joined)
		}
		for _, want := range []string{"-m string --algo bm --icase --from 60 --to 320", "-p udp -j NFQUEUE --queue-num 1053 --queue-bypass"} {
			if !strings.Contains(joined, want) {
				t.Fatalf("rule %q lacks %q", joined, want)
			}
		}
	}
	for _, mode := range []string{"exit-doh", "exit-passthrough"} {
		rules = desiredNFQueueRules(mode, nil)
		if len(rules) != 2 || strings.Join(rules[0], " ") != markReturn ||
			strings.Join(rules[1], " ") != "-p udp -j NFQUEUE --queue-num 1053 --queue-bypass" {
			t.Fatalf("%s nfqueue rules: %v", mode, rules)
		}
	}
}

func TestRefreshIPv6NFQueueMode(t *testing.T) {
	p, _ := dnsTestProxy(t, func(r *http.Request) (int, string) {
		switch r.URL.Path + "?" + r.URL.RawQuery {
		case "/localapi/v0/status?peers=false":
			return 200, `{"BackendState":"Running","CurrentTailnet":{"MagicDNSSuffix":"tail1234.ts.net"},"ExitNodeStatus":{"ID":"nExit"}}`
		case "/localapi/v0/prefs?":
			return 200, `{"ExitNodeID":"nExit"}`
		}
		return 404, ""
	})
	p.ipv6Mode = ipv6ModeNFQueue
	// IPv4 conntrack failing must not disable exit-passthrough when IPv6 NFQUEUE is active.
	p.ctProbe = func(family int) error {
		if family == 1 {
			t.Error("NFQUEUE mode must not probe IPv6 conntrack")
		}
		return syscall.EOPNOTSUPP
	}
	var v4Rules, v6Rules, flushes []string
	p.run = func(_ context.Context, name string, args ...string) ([]byte, error) {
		if strings.HasSuffix(name, "iptables") && len(args) > 4 {
			if args[2] != "nat" || args[4] != magicDNSChain {
				t.Errorf("unexpected v4 command: %v", args)
			}
			if args[3] == "-A" {
				v4Rules = append(v4Rules, strings.Join(args[5:], " "))
			}
		}
		if strings.HasSuffix(name, "ip6tables") && len(args) > 4 {
			if args[3] == "-F" {
				flushes = append(flushes, args[2]+":"+args[4])
			}
			if args[3] == "-A" {
				if args[2] != "filter" || args[4] != magicDNSChain {
					t.Fatalf("unexpected v6 nfqueue target: %v", args)
				}
				v6Rules = append(v6Rules, strings.Join(args[5:], " "))
			}
		}
		return nil, nil
	}
	p.refresh(context.Background())
	if p.mode != "exit-passthrough" || len(v4Rules) != 3 || !strings.Contains(v4Rules[2], "-m string") {
		t.Fatalf("v4 must narrow while mode stays exit-passthrough: mode=%s v4=%q", p.mode, v4Rules)
	}
	if len(v6Rules) != 2 || v6Rules[0] != markReturn || v6Rules[1] != "-p udp -j NFQUEUE --queue-num 1053 --queue-bypass" {
		t.Fatalf("unexpected v6 nfqueue rules: %q", v6Rules)
	}
	state := readMagicDNSState(p.state, time.Now())
	if state == nil || !state.Rules || !state.Rules6 || state.IPv6Fallback || state.Mode != "exit-passthrough" {
		t.Fatalf("unexpected nfqueue state: %+v", state)
	}
	// Stopping the NFQUEUE listener flushes filter/shellscaled_dns and sets rules6=false.
	flushes = nil
	p.dead6.Store(true)
	p.refresh(context.Background())
	if p.listen6 || p.rulesOK[1] || len(flushes) != 1 || flushes[0] != "filter:"+magicDNSChain {
		t.Fatalf("dead nfqueue listener cleanup failed: listen6=%v ok=%v flushes=%q", p.listen6, p.rulesOK, flushes)
	}
	if state := readMagicDNSState(p.state, time.Now()); state == nil || state.Rules6 {
		t.Fatalf("expected rules6=false after dead nfqueue listener, got %+v", state)
	}
	// flushRules must flush all module IPv4 and IPv6 chains across tiers.
	flushes = nil
	var v4Flushed bool
	origRun := p.run
	p.run = func(ctx context.Context, name string, args ...string) ([]byte, error) {
		if strings.HasSuffix(name, "/iptables") && len(args) > 4 && args[3] == "-F" {
			v4Flushed = true
		}
		return origRun(ctx, name, args...)
	}
	p.flushRules()
	if !v4Flushed || strings.Join(flushes, ",") != "nat:shellscaled_dns,filter:shellscaled_dns,filter:shellscaled_dns6_fallback" {
		t.Fatalf("flushRules did not clear every tier: v4=%v v6=%q", v4Flushed, flushes)
	}
}

func TestProbeIPv6Tiers(t *testing.T) {
	t.Run("tier1-nat", func(t *testing.T) {
		p, _ := dnsTestProxy(t, func(*http.Request) (int, string) { return 500, "" })
		p.openNFQ = func(uint16) (*nfqConn, error) { t.Fatal("tier1 must not open nfqueue"); return nil, nil }
		conn6, nfq := p.probeIPv6(context.Background())
		if conn6 != nil {
			defer conn6.Close()
		}
		if nfq != nil || p.v6Mode() != ipv6ModeNAT || p.ipv6Fallback {
			t.Fatalf("tier1 got mode=%d fallback=%v nfq=%v", p.v6Mode(), p.ipv6Fallback, nfq)
		}
	})
	t.Run("tier2-nfqueue", func(t *testing.T) {
		p, _ := dnsTestProxy(t, func(*http.Request) (int, string) { return 500, "" })
		p.run = func(_ context.Context, _ string, args ...string) ([]byte, error) {
			if args[2] == "nat" {
				return nil, errors.New("no nat")
			}
			return nil, nil
		}
		p.probeTProxy6 = func() error { return nil }
		fakeNFQ := &nfqConn{queue: magicDNSPort, close: func() error { return nil }}
		p.openNFQ = func(q uint16) (*nfqConn, error) {
			if q != magicDNSPort {
				t.Fatalf("unexpected queue %d", q)
			}
			return fakeNFQ, nil
		}
		conn6, nfq := p.probeIPv6(context.Background())
		if conn6 != nil || nfq != fakeNFQ || p.v6Mode() != ipv6ModeNFQueue || p.ipv6Fallback || !p.listen6 {
			t.Fatalf("tier2 got mode=%d fallback=%v listen6=%v nfq=%v", p.v6Mode(), p.ipv6Fallback, p.listen6, nfq)
		}
	})
	for _, tc := range []struct {
		name      string
		filterErr error
		tproxyErr error
		nfqErr    error
	}{
		{"missing-filter-chain", errors.New("no chain"), nil, nil},
		{"missing-transparent", nil, syscall.ENOPROTOOPT, nil},
		{"missing-nfqueue", nil, nil, syscall.EPROTONOSUPPORT},
	} {
		t.Run("tier3-fallback-"+tc.name, func(t *testing.T) {
			p, _ := dnsTestProxy(t, func(*http.Request) (int, string) { return 500, "" })
			p.run = func(_ context.Context, _ string, args ...string) ([]byte, error) {
				if args[2] == "nat" {
					return nil, errors.New("no nat")
				}
				return nil, tc.filterErr
			}
			p.probeTProxy6 = func() error { return tc.tproxyErr }
			p.openNFQ = func(uint16) (*nfqConn, error) { return nil, tc.nfqErr }
			conn6, nfq := p.probeIPv6(context.Background())
			if conn6 != nil || nfq != nil || p.v6Mode() != ipv6ModeFallback || !p.ipv6Fallback || p.listen6 {
				t.Fatalf("tier3 got mode=%d fallback=%v listen6=%v", p.v6Mode(), p.ipv6Fallback, p.listen6)
			}
		})
	}
}

func TestNFQueueEncodingAndParsing(t *testing.T) {
	vMsg := nfqVerdictMsg(1053, 0x12345678, nfDrop)
	if len(vMsg) < 32 || binary.NativeEndian.Uint32(vMsg[:4]) != uint32(len(vMsg)) ||
		binary.NativeEndian.Uint16(vMsg[4:6]) != nfnlSubsysQueue<<8|nfqnlMsgVerdict ||
		vMsg[16] != syscall.AF_UNSPEC || binary.BigEndian.Uint16(vMsg[18:20]) != 1053 {
		t.Fatalf("unexpected verdict header %x", vMsg)
	}
	vAttr := nlFind(vMsg[20:], nfqaVerdictHdr)
	if len(vAttr) != 8 || binary.BigEndian.Uint32(vAttr[:4]) != nfDrop || binary.BigEndian.Uint32(vAttr[4:8]) != 0x12345678 {
		t.Fatalf("unexpected verdict attr %x", vAttr)
	}

	src := netip.MustParseAddrPort("[2001:db8::10]:45678")
	dst := netip.MustParseAddrPort("[2001:4860:4860::8888]:53")
	q := testQuery(0x2233, "host.tail1234.ts.net", 28)
	raw := testNFQPacketMsg(1053, 42, 0x300a9, 27, testIPv6UDPPacket(src, dst, q))
	pkt, ok := parseNFQPacket(raw[20:])
	if !ok || pkt.id != 42 || pkt.mark != 0x300a9 || pkt.outdev != 27 {
		t.Fatalf("parsed nfq packet: ok=%v %+v", ok, pkt)
	}
	dnsPkt, gotSrc, gotDst, ok := parseIPv6UDPDNS(pkt.payload)
	if !ok || gotSrc != src || gotDst != dst || string(dnsPkt) != string(q) {
		t.Fatalf("parsed ipv6 udp: ok=%v src=%v dst=%v len=%d", ok, gotSrc, gotDst, len(dnsPkt))
	}

	extHdr := testIPv6UDPPacket(src, dst, q)
	extHdr[6] = 0 // Hop-by-Hop extension header, not direct UDP
	v4Mapped := testIPv6UDPPacket(src, netip.MustParseAddrPort("[::ffff:8.8.8.8]:53"), q)
	shortIP := testIPv6UDPPacket(src, dst, q)
	binary.BigEndian.PutUint16(shortIP[4:6], 100)
	badUDP := testIPv6UDPPacket(src, dst, q)
	binary.BigEndian.PutUint16(badUDP[44:46], 4)
	for _, bad := range [][]byte{nil, extHdr[:47], extHdr, v4Mapped, shortIP, badUDP} {
		if _, _, _, ok := parseIPv6UDPDNS(bad); ok {
			t.Fatalf("accepted invalid payload len=%d", len(bad))
		}
	}
}

func TestServeNFQueueRoutingAndPassthrough(t *testing.T) {
	upstream, err := net.ListenUDP("udp6", &net.UDPAddr{IP: net.IPv6loopback})
	if err != nil {
		t.Skip("no IPv6 loopback:", err)
	}
	defer upstream.Close()
	go func() {
		buf := make([]byte, 512)
		for {
			n, addr, err := upstream.ReadFromUDP(buf)
			if err != nil {
				return
			}
			_, _ = upstream.WriteToUDP(reply(buf[:n], n, 3), addr)
		}
	}()
	upstreamPort := uint16(upstream.LocalAddr().(*net.UDPAddr).Port)

	p, _ := dnsTestProxy(t, func(r *http.Request) (int, string) {
		if r.URL.Path == "/localapi/v0/dns-query" {
			body, _ := json.Marshal(struct{ Bytes []byte }{reply(testQuery(1, "host.tail1234.ts.net", 28), 12, 0)})
			return 200, string(body)
		}
		return 404, ""
	})
	p.ipv6Mode = ipv6ModeNFQueue
	p.suffix = "tail1234.ts.net"
	p.mode = "exit-passthrough"
	p.ifName = func(idx int) string {
		if idx == 27 {
			return "wlan1"
		}
		return ""
	}

	type verdictRecord struct {
		id, verdict uint32
	}
	type replyRecord struct {
		origDst, client netip.AddrPort
		outdev          uint32
		resp            []byte
	}
	inCh := make(chan []byte, 16)
	verdictCh := make(chan verdictRecord, 16)
	replyCh := make(chan replyRecord, 16)
	closedCh := make(chan struct{})
	var closeOnce sync.Once
	q := &nfqConn{
		queue: magicDNSPort,
		read: func(buf []byte) (int, error) {
			select {
			case msg := <-inCh:
				n := copy(buf, msg)
				return n, nil
			case <-closedCh:
				return 0, net.ErrClosed
			}
		},
		write: func(b []byte) (int, error) {
			if len(b) >= 20 && binary.NativeEndian.Uint16(b[4:6]) == nfnlSubsysQueue<<8|nfqnlMsgVerdict {
				v := nlFind(b[20:], nfqaVerdictHdr)
				if len(v) == 8 {
					verdictCh <- verdictRecord{binary.BigEndian.Uint32(v[4:8]), binary.BigEndian.Uint32(v[:4])}
				}
			}
			return len(b), nil
		},
		close: func() error {
			closeOnce.Do(func() { close(closedCh) })
			return nil
		},
	}
	p.reply6 = func(origDst, client netip.AddrPort, outdev uint32, resp []byte) error {
		replyCh <- replyRecord{origDst, client, outdev, append([]byte(nil), resp...)}
		return nil
	}

	ctx, cancel := context.WithCancel(context.Background())
	slots := make(chan struct{}, 64)
	done := make(chan error, 1)
	go func() { done <- p.serveNFQueue(ctx, q, slots) }()

	client := netip.MustParseAddrPort("[2001:db8::5]:45000")
	guaDNS := netip.MustParseAddrPort("[2001:4860:4860::8888]:53")
	loopUpstream := netip.AddrPortFrom(netip.IPv6Loopback(), upstreamPort)
	llDNS := netip.MustParseAddrPort("[fe80::1]:53")
	llClient := netip.MustParseAddrPort("[fe80::2]:45001")

	// 1. Tailnet query to GUA DNS -> NF_DROP + LocalAPI answer.
	inCh <- testNFQPacketMsg(1053, 1, 0x300a9, 27, testIPv6UDPPacket(client, guaDNS, testQuery(0x1111, "host.tail1234.ts.net", 28)))
	// 2. Passthrough query to loopback upstream -> NF_DROP + UDP6 passthrough answer.
	inCh <- testNFQPacketMsg(1053, 2, 0x300a9, 27, testIPv6UDPPacket(client, loopUpstream, testQuery(0x2222, "www.example.com", 28)))
	// 3. Bypass-marked query -> NF_ACCEPT without reply.
	inCh <- testNFQPacketMsg(1053, 3, 0x100200a9, 27, testIPv6UDPPacket(client, guaDNS, testQuery(0x3333, "www.example.com", 28)))
	// 4. Link-local query without outdev -> NF_ACCEPT without reply.
	inCh <- testNFQPacketMsg(1053, 4, 0x300a9, 0, testIPv6UDPPacket(llClient, llDNS, testQuery(0x4444, "host.tail1234.ts.net", 28)))
	// 5. Link-local query with outdev=27 -> NF_DROP + LocalAPI answer + outdev preserved for reply6.
	inCh <- testNFQPacketMsg(1053, 5, 0x300a9, 27, testIPv6UDPPacket(llClient, llDNS, testQuery(0x5555, "host.tail1234.ts.net", 28)))
	// 6. Loopback :1053 destination -> NF_ACCEPT.
	inCh <- testNFQPacketMsg(1053, 6, 0, 1, testIPv6UDPPacket(client, netip.MustParseAddrPort("[::1]:1053"), testQuery(0x6666, "www.example.com", 1)))
	// 7. Short non-DNS payload -> NF_ACCEPT.
	inCh <- testNFQPacketMsg(1053, 7, 0, 27, testIPv6UDPPacket(client, guaDNS, []byte{1, 2, 3}))

	wantVerdicts := map[uint32]uint32{
		1: nfDrop, 2: nfDrop, 3: nfAccept, 4: nfAccept, 5: nfDrop, 6: nfAccept, 7: nfAccept,
	}
	for total := len(wantVerdicts); total > 0; total-- {
		v := <-verdictCh
		if want, ok := wantVerdicts[v.id]; !ok || v.verdict != want {
			t.Fatalf("packet %d got verdict %d, want %d", v.id, v.verdict, want)
		}
		delete(wantVerdicts, v.id)
	}
	gotReplies := map[uint16]replyRecord{}
	for i := 0; i < 3; i++ {
		r := <-replyCh
		id := binary.BigEndian.Uint16(r.resp[:2])
		gotReplies[id] = r
	}
	if r := gotReplies[0x1111]; r.origDst != guaDNS || r.client != client || r.outdev != 27 || r.resp[3]&0x0f != 0 {
		t.Fatalf("gua tailnet reply: %+v", r)
	}
	if r := gotReplies[0x2222]; r.origDst != loopUpstream || r.client != client || r.resp[3]&0x0f != 3 {
		t.Fatalf("passthrough reply: %+v", r)
	}
	if r := gotReplies[0x5555]; r.origDst != llDNS || r.client != llClient || r.outdev != 27 || r.resp[3]&0x0f != 0 {
		t.Fatalf("link-local reply: %+v", r)
	}

	// Full concurrency slots must NF_ACCEPT rather than drop or block.
	for i := 0; i < cap(slots); i++ {
		slots <- struct{}{}
	}
	inCh <- testNFQPacketMsg(1053, 8, 0x300a9, 27, testIPv6UDPPacket(client, guaDNS, testQuery(0x8888, "host.tail1234.ts.net", 28)))
	v := <-verdictCh
	if v.id != 8 || v.verdict != nfAccept {
		t.Fatalf("full slots must NF_ACCEPT: %+v", v)
	}
	for i := 0; i < cap(slots); i++ {
		<-slots
	}

	cancel()
	_ = q.Close()
	if err := <-done; err != nil {
		t.Fatalf("serveNFQueue exit error: %v", err)
	}
}

func TestServeNFQueueExitDoHAndTruncation(t *testing.T) {
	p, _ := dnsTestProxy(t, func(*http.Request) (int, string) { return 404, "" })
	p.ipv6Mode = ipv6ModeNFQueue
	p.mode = "exit-doh"
	p.exitDoH = "http://100.64.0.2:1234/dns-query"
	largeResp := append(reply(testQuery(0x0001, "big.example.com", 28), 33, 0), make([]byte, 500)...)
	p.doh = &http.Client{Transport: transportFunc(func(r *http.Request) (*http.Response, error) {
		return &http.Response{StatusCode: 200, Body: io.NopCloser(strings.NewReader(string(largeResp))), Header: http.Header{}}, nil
	})}
	p.ifName = func(idx int) string {
		if idx == 27 {
			return "wlan1"
		}
		return ""
	}
	client := netip.MustParseAddrPort("[fe80::2]:45100")
	llDNS := netip.MustParseAddrPort("[fe80::1]:53")
	inCh := make(chan []byte, 4)
	verdictCh := make(chan uint32, 4)
	replyCh := make(chan []byte, 4)
	closedCh := make(chan struct{})
	var closeOnce sync.Once
	q := &nfqConn{
		queue: magicDNSPort,
		read: func(buf []byte) (int, error) {
			select {
			case msg := <-inCh:
				return copy(buf, msg), nil
			case <-closedCh:
				return 0, net.ErrClosed
			}
		},
		write: func(b []byte) (int, error) {
			if v := nlFind(b[20:], nfqaVerdictHdr); len(v) == 8 {
				verdictCh <- binary.BigEndian.Uint32(v[:4])
			}
			return len(b), nil
		},
		close: func() error {
			closeOnce.Do(func() { close(closedCh) })
			return nil
		},
	}
	p.reply6 = func(origDst, gotClient netip.AddrPort, outdev uint32, resp []byte) error {
		if origDst != llDNS || gotClient != client || outdev != 27 {
			t.Errorf("unexpected reply target: orig=%v client=%v outdev=%d", origDst, gotClient, outdev)
		}
		replyCh <- append([]byte(nil), resp...)
		return nil
	}
	ctx, cancel := context.WithCancel(context.Background())
	done := make(chan error, 1)
	go func() { done <- p.serveNFQueue(ctx, q, make(chan struct{}, 4)) }()

	// Link-local exit-doh query without EDNS must truncate >512B answer and set TC=1.
	inCh <- testNFQPacketMsg(1053, 10, 0x300a9, 27, testIPv6UDPPacket(client, llDNS, testQuery(0x9999, "big.example.com", 28)))
	if v := <-verdictCh; v != nfDrop {
		t.Fatalf("got verdict %d, want nfDrop", v)
	}
	resp := <-replyCh
	if len(resp) > 512 || resp[0] != 0x99 || resp[1] != 0x99 || resp[2]&0x02 == 0 {
		t.Fatalf("expected truncated TC=1 reply <=512B, got len=%d flags=%x", len(resp), resp[:4])
	}

	// Link-local exit-passthrough query must supply %wlan1 zone and exact 0x300a9 mark to queryPassthrough.
	p.mu.Lock()
	p.mode = "exit-passthrough"
	p.mu.Unlock()
	var gotDst netip.AddrPort
	var gotMark uint32
	p.forward = func(_ context.Context, dst netip.AddrPort, mark uint32, pkt []byte) ([]byte, error) {
		gotDst, gotMark = dst, mark
		return reply(pkt, len(pkt), 0), nil
	}
	inCh <- testNFQPacketMsg(1053, 11, 0x300a9, 27, testIPv6UDPPacket(client, llDNS, testQuery(0x7777, "ll.example.com", 28)))
	if v := <-verdictCh; v != nfDrop {
		t.Fatalf("got verdict %d, want nfDrop", v)
	}
	resp = <-replyCh
	if gotDst != netip.MustParseAddrPort("[fe80::1%wlan1]:53") || gotMark != 0x300a9 || resp[0] != 0x77 || resp[1] != 0x77 || resp[3]&0x0f != 0 {
		t.Fatalf("link-local passthrough failed: dst=%v mark=%#x resp=%x", gotDst, gotMark, resp)
	}
	cancel()
	_ = q.Close()
	if err := <-done; err != nil {
		t.Fatalf("serveNFQueue exit error: %v", err)
	}
}

func TestQueryPassthroughLinkLocalRequiresZone(t *testing.T) {
	if _, err := queryPassthrough(context.Background(), netip.MustParseAddrPort("[fe80::1]:53"), 0x300a9, testQuery(1, "example.com", 28)); err == nil {
		t.Fatal("link-local destination without zone must fail")
	}
	if got := passthroughMark(0x300a9); got != 0x100300a9 {
		t.Fatalf("passthroughMark(0x300a9) = %#x, want 0x100300a9", got)
	}
}

func TestTransparentUDP6ConcurrentSameOrigDst(t *testing.T) {
	if err := probeTransparentUDP6(); err != nil {
		t.Skip("transparent IPv6 socket options unavailable in this environment:", err)
	}
	origDst := netip.MustParseAddrPort("[2001:db8:53::1]:15353")
	const workers = 8
	fds := make([]int, workers)
	errs := make(chan error, workers)
	start := make(chan struct{})
	var wg sync.WaitGroup
	for i := 0; i < workers; i++ {
		wg.Add(1)
		go func(idx int) {
			defer wg.Done()
			<-start
			fd, err := openTransparentUDP6()
			if err != nil {
				errs <- err
				return
			}
			fds[idx] = fd
			for _, opt := range [][3]int{
				{syscall.SOL_SOCKET, syscall.SO_REUSEADDR, 1},
				{syscall.SOL_SOCKET, soReusePort, 1},
				{syscall.IPPROTO_IPV6, ipv6Transparent, 1},
				{syscall.SOL_SOCKET, syscall.SO_MARK, 0x10020000},
			} {
				v, err := syscall.GetsockoptInt(fd, opt[0], opt[1])
				if err != nil || v != opt[2] {
					errs <- errors.New("socket option mismatch before bind")
					return
				}
			}
			if err := syscall.Bind(fd, &syscall.SockaddrInet6{Port: int(origDst.Port()), Addr: origDst.Addr().As16()}); err != nil {
				errs <- err
				return
			}
		}(i)
	}
	close(start)
	wg.Wait()
	close(errs)
	for _, fd := range fds {
		if fd > 0 {
			_ = syscall.Close(fd)
		}
	}
	for err := range errs {
		t.Fatalf("concurrent bind to same origDst failed: %v", err)
	}
}
