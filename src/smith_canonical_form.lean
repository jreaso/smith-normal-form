--follows on from other files

-- # Smith Canonical Form

def smith_canon_form {n m : ℕ} {D : Type*} [euclidean_domain D] (B : matrix (fin n) (fin m) D) : Prop :=
B = B -- definition of smith form here

-- # Main Result

theorem smith_normal {n m : ℕ} {D : Type*} {D : Type*} [euclidean_domain D] (A : matrix (fin n) (fin m) D) : ∃ B : matrix (fin n) (fin m) D, smith_canon_form B ∧ equivalent A B :=
begin
  sorry
end
