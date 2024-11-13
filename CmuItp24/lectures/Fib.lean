import Std

def fib₁_aux : Nat → Nat × Nat
  | 0 => (0, 1)
  | n + 1 => let (a, b) := fib₁_aux n
             (b, a + b)

def fib₁ (n : Nat) : Nat := (fib₁_aux n).1

def fib₂ (n : Nat) : Nat := Id.run do
  let mut a := 0
  let mut b := 1
  for _ in [0:n] do
    let tmp := a
    a := b
    b := tmp + b
  return a

def fib₃_aux : Nat → Nat → Nat →  Nat
  | 0, a, _   => a
  | n+1, a, b => fib₃_aux n b (a + b)

def fib₃ (n : Nat) : Nat := fib₃_aux n 0 1

def main (args : List String) : IO Unit := do
  let n :=
    if let some first_arg := args.head? then
      if let some m := first_arg.toNat? then
        m
      else
        0
    else
      0
  IO.println (fib₃ n)
