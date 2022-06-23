
(prover
  (name andes)
  (cmd "ulimit -t $timeout; $cur_dir/../andes --timeout $timeout $file")
  (unsat "^× no sol")
  (sat "^✔ sol")
  (unknown "UNKNOWN")
  (timeout "TIMEOUT"))

(dir
  (path $cur_dir/)
  (pattern ".*.smt2")
  (expect (const unknown)))
