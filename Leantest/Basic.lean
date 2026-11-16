def hello := "world"

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => True
  | Nat.succ n => not (even n)

#eval even 5
