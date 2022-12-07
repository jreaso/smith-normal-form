import data.finset.basic
import data.matrix.basic
import algebra.euclidean_domain
import linear_algebra.matrix.to_lin

variables (n m : ℕ) (D : Type*) [euclidean_domain D] [decidable_eq D] (A : matrix (fin n) (fin n) D) (i j : fin n)




-- `A' := finset.image₂ A finset.univ finset.univ` converts `A : matrix (fin n) (fin n) D` to `A' : finset D`
-- `A'' := finset.filter (λ (a : D), a ≠ 0) A'` filters out the zero's
-- need a proof `h : A''.nonempty` (from the fact that A ≠ 0)
-- Given the preorder α (which will be ≺ in our case), `finset.exists_minimal` says that A'' has a minimal element
-- extract the minimal element (either using cases or a similar lemma to `finset.min'_mem`)
-- Combine with `finset.mem_image₂` to get the element in original matrix


local infix ` ≺ `:50 := euclidean_domain.r

lemma min_valuation_of_mat {R : Type*} [euclidean_domain R] [decidable_eq R] {n : ℕ} (A : matrix (fin n) (fin n) R) (hA0 : A ≠ 0) : ∃ (k l : fin n), ∀ (i j : fin n), (A k l ≠ 0) ∧ ( A i j ≠ 0 → ¬((A i j) ≺ (A k l)) ) :=
begin
  -- A as a finset without the zero's
  let A' := finset.filter (λ (a : R), a ≠ 0) (finset.image₂ A finset.univ finset.univ),
  -- A has a non-zero element
  have hA0' : ∃ (i' j' : fin n), A i' j' ≠ 0,
  { by_contra h',
    push_neg at h',
    have : A = 0,
    ext A,
    exact h' _ _,
    contradiction },
  rcases hA0' with ⟨i', j', hA0'⟩,
  -- A' is nonempty
  have hA'ne : A'.nonempty,
  { use A i' j',
    simp [A'],
    use [i', j'] },
  -- R is a preorder
  haveI : preorder R,
  { sorry },
  -- There exists a minimal element of A', m
  rcases (finset.exists_minimal A' hA'ne) with ⟨m, hm, hmin⟩,
  rcases ((finset.mem_image₂).mp (finset.mem_of_mem_filter m hm)) with ⟨k, l, _, _, hmin'⟩,
  use [k, l],
  intros i j,
  split,
  { rw hmin',
    exact (finset.mem_filter.mp hm).2 },
  intro h',
  have h'' : (A i j) ∈ A',
  { dsimp [A'],
    rw finset.mem_filter,
    split,
    { rw finset.mem_image₂,
      use [i, j],
      simp },
    exact h' },
  rw hmin',
  exact hmin (A i j) h'',
  sorry
end







#check (matrix (fin n) (fin n) D)


#check finset.image₂ A finset.univ finset.univ






#check A

#check (( matrix (fin n) (fin n) D) : finset D)
#check finite (matrix (fin n) (fin n) D)
#check finite (finset ( matrix (fin n) (fin n) D))

#check finset D


example :fintype ( matrix (fin n) (fin n) D) :=
begin
  haveI : fintype D,
  {sorry},
  exact matrix.fintype D,
end

#check finite ( matrix (fin n) (fin n) D)


#check finset.univ

#check finset ((fin n) × (fin n))




variable (B : finset D)

#check finset.filter (λ (b : D), b ≠ 0) B




