open Benchmark

let time msg fn arg nrep =
  Gc.compact();
  let start_size = Gc.((stat()).heap_words) * 8 in
  let start_alloc = Gc.allocated_bytes() in
  let start_time = Sys.time () in
  for _i = 1 to nrep do ignore (fn arg) done;
  let stop_time = Sys.time () in
  let stop_alloc = Gc.allocated_bytes() in
  let stop_size = Gc.((stat()).top_heap_words) * 8 in
  Printf.printf "%.2e s %.2e b %.2e b %s\n%!"
                ((stop_time -. start_time) /. float nrep)
                ((stop_alloc -. start_alloc) /. float nrep)
                (float (stop_size - start_size))
                msg

let _ =
  let nrep =
    if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 500 in
  match Sys.argv.(1) with
  | "o1" ->
      time "Original (words)" TestOriginal.bench1 poswords nrep
  | "o2" ->
      time "Original (small numbers)" TestOriginal.bench1 smallnumbers (nrep * 10)
  | "o3" ->
      time "Original (repeated keys)" TestOriginal.bench2 () nrep
  | "c1" ->
      time "Canonical (words)" TestCanonical.bench1 poswords nrep
  | "c2" ->
      time "Canonical (small numbers)" TestCanonical.bench1 smallnumbers (nrep * 10)
  | "c3" ->
      time "Canonical (repeated keys)" TestCanonical.bench2 () nrep
  | "s1" ->
      time "Sigma (words)" TestSigma.bench1 poswords nrep
  | "s2" ->
      time "Sigma (small numbers)" TestSigma.bench1 smallnumbers (nrep * 10)
  | "s3" ->
      time "Sigma (repeated keys)" TestSigma.bench2 () nrep
  | "n1" ->
      time "Node01 (words)" TestNode01.bench1 poswords nrep
  | "n2" ->
      time "Node01 (small numbers)" TestNode01.bench1 smallnumbers (nrep * 10)
  | "n3" ->
      time "Node01 (repeated keys)" TestNode01.bench2 () nrep
  | "g1" ->
      time "GADT (words)" TestGADT.bench1 poswords nrep
  | "g2" ->
      time "GADT (small numbers)" TestGADT.bench1 smallnumbers (nrep * 10)
  | "g3" ->
      time "GADT (repeated keys)" TestGADT.bench2 () nrep
  | "a1" ->
      time "AVLPositive (words)" TestAVLPositive.bench1 poswords nrep
  | "a2" ->
      time "AVLPositive (small numbers)" TestAVLPositive.bench1 smallnumbers (nrep * 10)
  | "a3" ->
      time "AVLPositive (repeated keys)" TestAVLPositive.bench2 () nrep
  | "as" ->
      time "AVLString (words)" TestAVLString.bench1 words nrep
  | "ct" ->
      time "CharTrie (words)" TestCharTrie.bench1 words nrep
  | "os" ->
      time "Originalstring (words)" TestOriginalAsStringmap.bench1 words nrep
  | "cs" ->
      time "Canonicalstring (words)" TestCanonicalAsStringmap.bench1 words nrep
  | s ->
      prerr_endline ("unknown test: " ^ s); exit 2

