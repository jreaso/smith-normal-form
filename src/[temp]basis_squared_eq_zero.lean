 
--following on from definitnins in `elementary_matrices.lean`
 
theorem basis_squared_eq_zero {D : Type*} [euclidean_domain D] {n : ℕ} {i j : fin n} (h : i ≠ j) : (basis D n i j) ⬝ (basis D n i j) = 0 := 
begin
  apply matrix.ext_iff.1,
  intros k l,
  rw [matrix.mul_apply, basis],
  simp,
  rw finset.sum_ite,
  --have h : ∀ x : fin n, (i = k ∧ j = x) → ¬(i = x ∧ j = l),
  have h' : ∀ x : fin n, (j = x) → ¬(i = x ∧ j = l),
  { rintro x ⟨rfl⟩,
    exact not_and_of_not_left (j = l) h },
  -- for the first summation, filter implies j=x and then h' lead the ite to 0 so summing up zeros

  sorry
end

rw finset.sum_ite,

lemma basis_squared_eq_zero {D : Type*} [euclidean_domain D] {n : ℕ} {i j : fin n} (h : i ≠ j) : (Δ D n i j) ⬝ (Δ D n i j) = 0 := 
begin
  apply matrix.ext_iff.1,
  intros i' j',
  rw [matrix.mul_apply, Δ],
  simp,
  rw finset.sum_ite,
  -- first case j = x in finset and i=x is codnition for ite so hypothesis says
  -- 
  have h' : ∀ (a : fin n), ite (i = i' ∧ j = a) (ite (i = a ∧ j = j') 1 0) 0 = 0,
  { intro x,
    by_cases h' : (i = i' ∧ j = x),
    rw if_pos h',
    have h'' : ¬(i = x ∧ j = j'), finish,
    rw if_neg h'',
    rw if_neg h' },
  
  --exact fintype.sum_eq_zero (λ (x : fin n), (ite (i = i' ∧ j = x) (ite (i = x ∧ j = j') 1 0) 0) ) h',

  --rw ← finset.sum_filter,
  rw finset.sum_ite,
  rw finset.sum_filter,
  rw finset.sum_filter,
  --rw ite_eq_or_eq,
  sorry
end


example {n : ℕ} {f : fin n → ℕ} (h : ∀ x : fin n, f x = 0) : ∑ (x : fin n), f x = 0 := 
begin
  exact fintype.sum_eq_zero (λ (a : fin n), f a) h,
end


example {P : Prop} [decidable P] : (λ (n : ℕ) , if P then n else n) = (λ n, n) := 
begin
  suggest
end

example (A B : matrix (fin n) (fin n) D) :  A = B ↔ ∀ (i j : fin n), A i j = B i j := matrix.ext_iff.symm