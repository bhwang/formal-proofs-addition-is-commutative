open nat

-- We first show that zero is the right and left additive identity

-- The first is trivial enough to prove via reflection.
theorem add_zero (m : nat) : m + 0 = m := rfl

-- The second isn't too much harder, just involving some case splitting 
-- on the constructors of nat
theorem zero_add : ∀ n, 0 + n = n
| 0 := rfl
| (succ n) := congr_arg succ (zero_add n) 


-- With these and a couple of built-in lemmas, we prove our result.
theorem add_comm (m n : nat) : m + n = n + m :=
nat.rec_on n  -- We proceed by induction on n.
  (show m + 0 = 0 + m, by rewrite [add_zero, zero_add]) -- Base case 
  (assume n,  -- Inductive step
    assume ih : m + n = n + m, 
    show m + succ n = succ n + m, from calc
      m + succ n = succ (m + n) : by rw add_succ 
                   -- move succ from right term to outside total sum
             ... = succ (n + m) : by rw ih 
                   -- apply induction hypotehsis
             ... = succ n + m   : by rw succ_add) 
                   -- move succ from outside total sum to left term
