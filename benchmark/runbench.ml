open Benchmark

let time msg fn sz arg nrep =
  Gc.compact();
  let start_alloc = Gc.allocated_bytes() in
  let start_time = Sys.time () in
  for _i = 1 to nrep do ignore (fn arg) done;
  let stop_time = Sys.time () in
  let stop_alloc = Gc.allocated_bytes() in
  let size = Obj.reachable_words (Obj.repr (sz arg)) in
  Printf.printf "%.2e s %.2e b %.2e b %s\n%!"
                ((stop_time -. start_time) /. float nrep)
                ((stop_alloc -. start_alloc) /. float nrep)
                (float size)
                msg

let nosize x = ()

let _ =
  let nrep =
    if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 500 in
  match Sys.argv.(1) with
  | "o1" ->
      time "Original (words)" TestOriginal.bench1 TestOriginal.dsize poswords nrep
  | "o2" ->
      time "Original (small numbers)" TestOriginal.bench1 TestOriginal.dsize smallnumbers (nrep * 10)
  | "o3" ->
      time "Original (repeated keys)" TestOriginal.bench2 nosize () nrep
  | "c1" ->
      time "Canonical (words)" TestCanonical.bench1 TestCanonical.dsize poswords nrep
  | "c2" ->
      time "Canonical (small numbers)" TestCanonical.bench1 TestCanonical.dsize smallnumbers (nrep * 10)
  | "c3" ->
      time "Canonical (repeated keys)" TestCanonical.bench2 nosize () nrep
  | "s1" ->
      time "Sigma (words)" TestSigma.bench1 TestSigma.dsize poswords nrep
  | "s2" ->
      time "Sigma (small numbers)" TestSigma.bench1 TestSigma.dsize smallnumbers (nrep * 10)
  | "s3" ->
      time "Sigma (repeated keys)" TestSigma.bench2 nosize () nrep
  | "n1" ->
      time "Node01 (words)" TestNode01.bench1 TestNode01.dsize poswords nrep
  | "n2" ->
      time "Node01 (small numbers)" TestNode01.bench1 TestNode01.dsize smallnumbers (nrep * 10)
  | "n3" ->
      time "Node01 (repeated keys)" TestNode01.bench2 nosize () nrep
  | "g1" ->
      time "GADT (words)" TestGADT.bench1 TestGADT.dsize poswords nrep
  | "g2" ->
      time "GADT (small numbers)" TestGADT.bench1 TestGADT.dsize smallnumbers (nrep * 10)
  | "g3" ->
      time "GADT (repeated keys)" TestGADT.bench2 nosize () nrep
  | "p1" ->
      time "Patricia (words)" TestPatricia.bench1 TestPatricia.dsize poswords nrep
  | "p2" ->
      time "Patricia (small numbers)" TestPatricia.bench1 TestPatricia.dsize smallnumbers (nrep * 10)
  | "p3" ->
      time "Patricia (repeated keys)" TestPatricia.bench2 nosize () nrep
  | "a1" ->
      time "AVLPositive (words)" TestAVLPositive.bench1 TestAVLPositive.dsize poswords nrep
  | "a2" ->
      time "AVLPositive (small numbers)" TestAVLPositive.bench1 TestAVLPositive.dsize smallnumbers (nrep * 10)
  | "a3" ->
      time "AVLPositive (repeated keys)" TestAVLPositive.bench2 nosize () (nrep / 10)
  | "as" ->
      time "AVLString (words)" TestAVLString.bench1 TestAVLString.dsize words nrep
  | "r1" ->
      time "RBPositive (words)" TestRBPositive.bench1 TestRBPositive.dsize poswords nrep
  | "r2" ->
      time "RBPositive (small numbers)" TestRBPositive.bench1 TestRBPositive.dsize smallnumbers (nrep * 10)
  | "r3" ->
      time "RBPositive (repeated keys)" TestRBPositive.bench2 nosize () (nrep / 10)
  | "rs" ->
      time "RBString (words)" TestRBString.bench1 TestRBString.dsize words nrep
  | "ct" ->
      time "CharTrie (words)" TestCharTrie.bench1 TestCharTrie.dsize words nrep
  | "os" ->
      time "Originalstring (words)" TestOriginalAsStringmap.bench1 TestOriginalAsStringmap.dsize words nrep
  | "cs" ->
      time "Canonicalstring (words)" TestCanonicalAsStringmap.bench1 TestCanonicalAsStringmap.dsize words nrep
  | "ps" ->
      time "Patriciastring (words)" TestPatriciaAsStringmap.bench1 TestPatriciaAsStringmap.dsize words nrep
  | s ->
      prerr_endline ("unknown test: " ^ s); exit 2

