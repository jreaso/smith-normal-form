import tactic
import data.matrix.basic
import data.matrix.block
import linear_algebra.matrix.block
import linear_algebra.matrix.nonsingular_inverse
import algebra.group.units
import order.well_founded
import algebra.big_operators.basic

-- allows notation for matrix multiplication and summations
open_locale matrix
open_locale big_operators

/-
Currently, whole framework is for a Eucldiean Domains (some results could be weakened to PID or even weaker), and later lemmas have been restriced to nxn matrices rather than nxm
-/

-- # Elementary Matrices
/-
Defines the basis matrix, all zero's except for a 1 in the (i, j)'th entry and three elementary matrices
Left multiplication acts on rows, right multiplication acts on columns, but the effect of the elementary matrices is expressed as lemmas later

* `add_mult n i j a` - is the matrix that (via multiplication) induces the map which adds `a` times row/column `i` to row/column `j`
* `mul_by_unit n i u` - induces a similar map which multiplies row/column `i` by `u`
-/

-- ## Definiton of the Elementary Matrices

namespace elem_matrix

-- Basis Δ (as called in Jacobson)
def basis (R : Type*) [euclidean_domain R] (n : ℕ) (i j : fin n) : matrix (fin n) (fin n) R :=
(λ i' j', if i = i' ∧ j = j' then 1 else 0)

-- Type I: Add multiple of column/row i to j
def add_mult {R : Type*} [euclidean_domain R] (n : ℕ) (i j : fin n) (a : R) (h : i ≠ j) : matrix (fin n) (fin n) R :=
1 + a • (basis R n i j)

-- Type II: Multiply row/column by a unit
def mul_by_unit {R : Type*} [euclidean_domain R] (n : ℕ) (i : fin n) (u : R) (h : is_unit u) : matrix (fin n) (fin n) R :=
matrix.diagonal (λ i', if i' = i then u else 1)
--1 + (u - 1) • (basis R n i i)

-- Type III: Permutation
def perm (R : Type*) [euclidean_domain R] (n : ℕ) (i j : fin n) : matrix (fin n) (fin n) R :=
(equiv.to_pequiv (equiv.swap i j)).to_matrix
-- 1 - (basis R n i i) - (basis R n j j) + (basis R n i j) + (basis R n j i)


-- ## Elementary Matrices are Invertible (units)
/-
Proof all three elementary matrices are invertible, which is expressed as `is_unit M`, by using equivalence between `is_unit M` and `is_unit (det M)`
-/

theorem add_mult_inv {R : Type*} [euclidean_domain R] {n : ℕ} {i j : fin n} {a : R} (h : i ≠ j) : is_unit (add_mult n i j a h) :=
begin
  apply (matrix.is_unit_iff_is_unit_det (add_mult n i j a h)).2,
  by_cases h' : i < j, -- case split to use upper and lower triangular theorems (essentially same argument), could be condensed
  { rw (matrix.det_of_upper_triangular (add_mult n i j a h) _),
    { unfold add_mult,
      unfold basis,
      have h₁ : ∀ (x : fin n), ¬(i = x ∧ j = x),
      { simp [h.symm] },
      simp [h₁] },
    intros k l hlk,
    unfold add_mult,
    unfold basis,
    have h₂ : ¬ (i = k ∧ j = l),
    { rintro ⟨rfl, rfl⟩,
      exact asymm h' hlk },
    simp [h₂, (ne_of_lt hlk).symm] },
  rw (matrix.det_of_lower_triangular (add_mult n i j a h) _),
  { unfold add_mult,
    unfold basis,
    have h₁ : ∀ (x : fin n), ¬(i = x ∧ j = x),
    { simp [h.symm] },
    simp [h₁] },
  intros k l hkl,
  unfold add_mult,
  unfold basis,
  have h₂ : ¬ (i = k ∧ j = l),
  { rintro ⟨rfl, rfl⟩,
    exact h (false.rec (i = j) (h' hkl)) },
  simp [h₂, (ne_of_lt hkl)],
end

theorem mul_by_unit_inv {R : Type*} [euclidean_domain R] {n : ℕ} {i : fin n} {u : R} {h : is_unit u} : is_unit (mul_by_unit n i u h) := 
begin
  apply (matrix.is_unit_iff_is_unit_det (mul_by_unit n i u h)).2,
  unfold mul_by_unit,
  simp [matrix.det_diagonal, finset.prod_ite],
  exact is_unit.pow (finset.filter (λ (x : fin n), x = i) finset.univ).card h,
end

theorem perm_inv {R : Type*} [euclidean_domain R] {n : ℕ} {i j : fin n} : is_unit (perm R n i j) := 
begin
  apply (matrix.is_unit_iff_is_unit_det (perm R n i j)).2, -- has determinant -1
  unfold perm,
  rw matrix.det_permutation,
  by_cases h : i = j,
  { rw equiv.perm.sign_swap',
    simp [h] },
  rw equiv.perm.sign_swap,
  { use -1,
    simp },
  exact h,
end

-- ## Lemmas About The Elementary Matrices
/-
ADD TO LIBRARY IN `data.matrix.pequiv`
This lemma fills in a missing lemma in `data.matrix.pequiv` which is necessary for proof of the effect of the permutation matrix
There are two different expressions of the theorem below, with the second one (using `matrix.submatrix`) being used
-/

/--
variables {m n α : Type*} 

lemma to_pequiv_matrix_mul [fintype n] [decidable_eq n] [semiring α] (f : n ≃ n) (M : matrix m n α): 
(M ⬝ f.to_pequiv.to_matrix) = λ i j, M i (f.symm j) :=
matrix.ext $ λ i j, by rw [pequiv.matrix_mul_apply, ←equiv.to_pequiv_symm, equiv.to_pequiv_apply]
-/

lemma pequiv.to_pequiv_matrix_mul {m n α : Type*} [fintype n] [decidable_eq n] [semiring α]
  (f : n ≃ n) (M : matrix m n α) : (M ⬝ f.to_pequiv.to_matrix) = M.submatrix id (f.symm) :=
matrix.ext $ λ i j, by rw [pequiv.matrix_mul_apply, ←equiv.to_pequiv_symm,
                           equiv.to_pequiv_apply, matrix.submatrix_apply, id.def]
-- necessary for later lemmas

-- ### Effect of Permutation Matrix
/-
Effect of left and right multiplication by the permutation matrix expressed in two ways each
-/

lemma perm_mul {R : Type*} [euclidean_domain R] {n : ℕ} (A : matrix (fin n) (fin n) R) (k l : fin n) : ∀ (i j : fin n), A i j = ((elem_matrix.perm R n k l) ⬝ A) (ite (i = k) l (ite (i = l) k i)) j
:= λ i j, by { unfold elem_matrix.perm, simp [pequiv.to_pequiv_mul_matrix, ←equiv.swap_apply_def] }

lemma perm_mul' {R : Type*} [euclidean_domain R] {n : ℕ} (A : matrix (fin n) (fin n) R) (k l : fin n) : ∀ (i j : fin n), ((elem_matrix.perm R n k l) ⬝ A) i j = A (ite (i = k) l (ite (i = l) k i)) j 
:= λ i j, by { unfold elem_matrix.perm, simp [pequiv.to_pequiv_mul_matrix, equiv.swap_apply_def] }

lemma mul_perm {R : Type*} [euclidean_domain R] {n : ℕ} (A : matrix (fin n) (fin n) R) (k l : fin n) : ∀ (i j : fin n), A i j = (A ⬝ (elem_matrix.perm R n k l)) i (ite (j = k) l (ite (j = l) k j))
:= λ i j, by { unfold elem_matrix.perm, simp [pequiv.to_pequiv_matrix_mul, ←equiv.swap_apply_def] }

lemma mul_perm' {R : Type*} [euclidean_domain R] {n : ℕ} (A : matrix (fin n) (fin n) R) (k l : fin n) : ∀ (i j : fin n), (A ⬝ (elem_matrix.perm R n k l)) i j = A i (ite (j = k) l (ite (j = l) k j))
:= λ i j, by { unfold elem_matrix.perm, simp [pequiv.to_pequiv_matrix_mul, equiv.swap_apply_def] }

lemma perm_eq_id {R : Type*} [euclidean_domain R] {n : ℕ} : ∀ {i : fin n}, elem_matrix.perm R n i i = (1 : matrix (fin n) (fin n) R) :=
begin
  intro i,
  unfold perm,
  simp,
end

-- ### Effect of Add Mult Matrix

-- Left Mult
lemma add_mult_mul {R : Type*} [euclidean_domain R] {n : ℕ} (A : matrix (fin n) (fin n) R) (i j : fin n) (c : R) (h : i ≠ j) : ((add_mult n i j c h) ⬝ A) i j  = (A i j) + c * (A j j)  :=
begin
  rw matrix.mul_apply,
  unfold add_mult basis,
  simp,
  ring_nf,
  rw finset.sum_add_distrib,
  rw fintype.sum_eq_add_sum_compl i,
  simp,
  rw finset.sum_eq_zero _,
  intros x hx,
  rw [finset.mem_compl, finset.mem_singleton] at hx,
  simp [matrix.one_apply_ne (ne_comm.mp hx)]
end

-- Right Mult
lemma mul_add_mult {R : Type*} [euclidean_domain R] {n : ℕ} (A : matrix (fin n) (fin n) R) (i j : fin n) (c : R) (h : i ≠ j) : (A ⬝ (add_mult n i j c h)) i j  = (A i j) + c * (A i i) :=
begin
  rw matrix.mul_apply,
  unfold add_mult basis,
  simp,
  ring_nf,
  simp [add_mul],
  rw finset.sum_add_distrib,
  rw fintype.sum_eq_add_sum_compl j,
  simp,
  rw finset.sum_eq_zero _,
  { ring_nf },
  intros x hx,
  rw [finset.mem_compl, finset.mem_singleton] at hx,
  simp [matrix.one_apply_ne hx]
end

/-
No lemmas about the effect of the `unit_mul` elementary matrix since it isn't used in the restriced snf definition (where we don't require diagonal entries successively divide)
-/

end elem_matrix



-- # Equivalence of m x n matrices
/-
Basic Framework for the equivalence of matrices, that this is an equivalence relation and that left and right multiplication by invertable (`is_unit`) matrices preserves equivalence
-/

namespace matrix_equiv_rel

-- ## Equivalence Definition
-- two mxn matrices A and B are quivalent if A = M B N and M and N are invertible
def r (R : Type*) [euclidean_domain R] (m n : ℕ) : (matrix (fin m) (fin n) R) → (matrix (fin m) (fin n) R) → Prop :=
λ A, (λ B, ∃ (M : matrix (fin m) (fin m) R) (N : matrix (fin n) (fin n) R), (is_unit M) ∧ (is_unit N) ∧ ( A = M ⬝ B ⬝ N ))

-- ## Matrix Equivalence is an Equivalence Relation

lemma r_refl {R : Type*} [euclidean_domain R] {m n : ℕ} : reflexive (r R m n) :=
begin
  intro A,
  use [1,1],
  finish,
end

lemma r_symm {R : Type*} [euclidean_domain R] {m n : ℕ} : symmetric (r R m n) :=
begin
  rintros A B ⟨M, N, hM, hN, h⟩,
  use [M⁻¹, N⁻¹],
  simp [matrix.nonsing_inv_eq_ring_inverse, hM, hN] ,
  simp [← matrix.nonsing_inv_eq_ring_inverse],
  calc
    B = (M⁻¹ ⬝ M) ⬝ B ⬝ (N ⬝ N⁻¹) : by {simp [matrix.mul_nonsing_inv N ((matrix.is_unit_iff_is_unit_det N).mp hN), matrix.nonsing_inv_mul M ((matrix.is_unit_iff_is_unit_det M).mp hM)]}
    ... = M⁻¹ ⬝ (M ⬝ B ⬝ N) ⬝ N⁻¹ : by {simp [matrix.mul_assoc]}
    ... = M⁻¹ ⬝ A ⬝ N⁻¹ : by {rw h}
end

lemma r_trans {R : Type*} [euclidean_domain R] {m n : ℕ} : transitive (r R m n) :=
begin
  rintros A B C ⟨M₁, N₁, hM₁, hN₁, h₁⟩ ⟨M₂, N₂, hM₂, hN₂, h₂⟩,
  use [M₁ ⬝ M₂, N₂ ⬝ N₁],
  split,
  { exact is_unit.mul hM₁ hM₂ },
  split,
  { exact is_unit.mul hN₂ hN₁ },
  calc
    A = M₁ ⬝ B ⬝ N₁ : h₁
    ... = M₁ ⬝ (M₂ ⬝ C ⬝ N₂) ⬝ N₁ : by {rw h₂}
    ... = M₁ ⬝ M₂ ⬝ C ⬝ (N₂ ⬝ N₁) : by {simp only [matrix.mul_assoc]}
end

theorem r_equiv {R : Type*} [euclidean_domain R] {m n : ℕ} : equivalence (r R m n) := ⟨r_refl, r_symm, r_trans⟩




-- ## Basic Equivalence Lemmas

-- left and right multiplication by invertible matrix preserves equivalence (in particular the elementary matrices)

lemma unit_mul {R : Type*} [euclidean_domain R] {m n : ℕ} (M : matrix (fin m) (fin n) R) (A : matrix (fin m) (fin m) R) (h : is_unit A) : r R m n M (A ⬝ M) :=
begin
  use [A⁻¹, 1],
  simp [matrix.nonsing_inv_eq_ring_inverse, h, ← matrix.mul_assoc, ← matrix.mul_eq_mul, (ring.inverse_mul_cancel A h)]
end

lemma mul_unit {R : Type*} [euclidean_domain R] {m n : ℕ} (M : matrix (fin m) (fin n) R) (A : matrix (fin n) (fin n) R) (h : is_unit A) : r R m n M (M ⬝ A) :=
begin
  use [1, A⁻¹],
  simp [matrix.nonsing_inv_eq_ring_inverse, h, matrix.mul_assoc, ← matrix.mul_eq_mul, (ring.mul_inverse_cancel A h)]
end

end matrix_equiv_rel


-- # Smith Normal Form

-- Notation for euclidean_domain.r, the well_founded relation to replace euclidean valuation function
local infix ` ≺ `:50 := euclidean_domain.r

-- If `δ` was the euclidean valuation function, as in Jacobson book, then we have the following equivalence `a ≺ b  ↔  δ(a) < δ(b)`

namespace smith_norm_form

-- ## Definitions

-- Simple version of smith normal form, without division condition, and limited to nxn
-- See full definition in comments at bottom
def snf {n : ℕ} {R : Type*} [euclidean_domain R] [decidable_eq R] (A : matrix (fin n) (fin n) R) : Prop :=
∃ (d : (fin n) → R) (r : ℕ), (A = matrix.diagonal d) ∧ (∀ (i : fin n), ↑i ≥ r ↔ d i = 0 ) --∧ (∀ (i j : fin n), (i ≤ j) → ↑j < r → (d i) ∣ (d j))

-- desired form for induction step
def simple_block_diag {R : Type*} [euclidean_domain R] {n : ℕ} (a : R) (A : matrix (fin n) (fin n) R) : matrix (fin (n + 1)) (fin (n + 1)) R :=
matrix.reindex (fin_sum_fin_equiv.trans fin_add_flip) (fin_sum_fin_equiv.trans fin_add_flip) (matrix.from_blocks (a • (1 : matrix (fin 1) (fin 1) R)) 0 0 A)
-- use `matrix.submatrix` instead?
/-
a 0 0 0
0 (   )
0 | A |
0 (   )
-/

-- An element of a matrix (over a ED) is minimal if it's non zero and has minimal valuation (excluding zeros)
def is_minimal {R : Type*} [euclidean_domain R] {n : ℕ} (A : matrix (fin n) (fin n) R) (k l : fin n) : Prop := (A k l ≠ 0) ∧ (∀ (i j : fin n), A i j ≠ 0 → ¬((A i j) ≺ (A k l)))


-- ## Lemmas Setting Up Main Result

-- Every non-zero matrix has an element with minimal valuation
-- this lemma specifically can give the indices of the minimal element
lemma min_valuation_of_mat {R : Type*} [euclidean_domain R] [decidable_eq R] {n : ℕ} (A : matrix (fin n) (fin n) R) (hA0 : A ≠ 0) : ∃ (k l : fin n), is_minimal A k l :=
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
  -- A' has a minimal element since ≺ is well founded
  rcases (well_founded.has_min euclidean_domain.r_well_founded (↑A') hA'ne) with ⟨m, hm, hmin⟩,
  rcases ((finset.mem_image₂).mp (finset.mem_of_mem_filter m hm)) with ⟨k, l, _, _, hmin'⟩,
  use [k, l],
  split,
  { rw hmin',
    exact (finset.mem_filter.mp hm).2 },
  intros i j h,
  have h'' : (A i j) ∈ A',
  { dsimp [A'],
    rw finset.mem_filter,
    split,
    { rw finset.mem_image₂,
      use [i, j],
      simp },
    exact h },
  rw hmin',
  exact hmin (A i j) h''
end


-- Moves minimal element to top left
lemma minimal_element_to_00 {R : Type*} [euclidean_domain R] [decidable_eq R] {n : ℕ} (A : matrix (fin (n + 1)) (fin (n + 1)) R)  (hA0 : A ≠ 0) : ∃ (B : matrix (fin (n + 1)) (fin (n + 1)) R), is_minimal B 0 0 ∧ matrix_equiv_rel.r R (n + 1) (n + 1) A B :=
begin
  rcases (min_valuation_of_mat A hA0) with ⟨i, j, h⟩, -- A i j is minimal elt of A
  use ((elem_matrix.perm R (n + 1) 0 i) ⬝ A ⬝ (elem_matrix.perm R (n + 1) 0 j)),
  split,
  { -- minimal element is at 0 0
    have aux : ∀ (k : fin (n + 1)), (ite (k = 0) k (ite (k = k) 0 k)) = 0,
      { have hj : j = 0 ∨ j ≠ 0, by tauto,
        cases hj;
        simp [hj] },
    have h₁ : A i j = ((elem_matrix.perm R (n + 1) 0 i) ⬝ A ⬝ (elem_matrix.perm R (n + 1) 0 j)) 0 0,
    { have H₁ := (elem_matrix.mul_perm ((elem_matrix.perm R (n + 1) 0 i) ⬝ A) 0 j) 0 j,
      rw [aux j] at H₁,
      rw [← H₁, ((elem_matrix.perm_mul A 0 i) i j), aux i] },
    have h₂ : ∀ (i' j' : fin (n + 1)), ∃ (k l : fin (n + 1)), A k l = ((elem_matrix.perm R (n + 1) 0 i) ⬝ A ⬝ (elem_matrix.perm R (n + 1) 0 j)) i' j',
    { intros i' j',
      -- Very manual solution
      have hi' : i' = 0 ∨ i' = i ∨ (i' ≠ 0 ∧ i' ≠ i), by tauto,
      have hj' : j' = 0 ∨ j' = j ∨ (j' ≠ 0 ∧ j' ≠ j), by tauto,
      have hi : i = 0 ∨ i ≠ 0, by tauto,
      have hj : j = 0 ∨ j ≠ 0, by tauto,
      cases hi;
      cases hj,
      { rw [hi, hj, elem_matrix.perm_eq_id],
        use [i', j'],
        simp },
      { rw [hi, elem_matrix.perm_eq_id],
        simp,
        rcases hj' with hj' | hj' | ⟨hj'₁, hj'₂⟩,
        { use [i', j],
          rw [hj', (elem_matrix.mul_perm A 0 j) i' j, aux j] },
        { use [i', 0],
          simp [hj', (elem_matrix.mul_perm A 0 j) i' 0] },
        { use [i', j'],
          simp [(elem_matrix.mul_perm A 0 j) i' j', hj'₁, hj'₂] } },
      { rw [hj, elem_matrix.perm_eq_id],
        simp,
        rcases hi' with hi' | hi' | ⟨hi'₁, hi'₂⟩,
        { use [i, j'],
          rw [hi', (elem_matrix.perm_mul A 0 i) i j', aux i] },
        { use [0, j'],
          simp [hi', (elem_matrix.perm_mul A 0 i) 0 j'] },
        { use [i', j'],
          simp [(elem_matrix.perm_mul A 0 i) i' j', hi'₁, hi'₂] } },
      { have H₁ := elem_matrix.mul_perm ((elem_matrix.perm R (n + 1) 0 i) ⬝ A) 0 j,
        have H₂ := elem_matrix.perm_mul A 0 i,
        rcases hi' with hi' | hi' | ⟨hi'₁, hi'₂⟩;
        rcases hj' with hj' | hj' | ⟨hj'₁, hj'₂⟩,
        { rw [hi', hj'] at *,
          use [i, j],
          have H₁' := H₁ 0 j,
          rw [aux j] at H₁',
          rw [← H₁', (H₂ i j), aux i] },
        { rw [hi', hj'] at *,
          use [i, 0],
          have H₁' := H₁ 0 0,
          simp at H₁',
          rw [← H₁', (H₂ i 0), aux i] },
        { rw [hi'] at *,
          use [i, j'],
          have H₁' := H₁ 0 j',
          simp [hj'₁, hj'₂] at H₁',
          rw [← H₁', (H₂ i j'), aux i] },
        { rw [hi', hj'] at *,
          use [0, j],
          have H₁' := H₁ i j,
          rw [aux j] at H₁',
          simp [← H₁', (H₂ 0 j)] },
        { rw [hi', hj'] at *,
          use [0, 0],
          have H₁' := H₁ i 0,
          simp at H₁',
          simp [← H₁', (H₂ 0 0)] },
        { rw hi' at *,
          use [0, j'],
          have H₁' := H₁ i j',
          simp [hj'₁, hj'₂] at H₁',
          simp [← H₁', (H₂ 0 j')] },
        { rw hj' at *,
          use [i', j],
          have H₁' := H₁ i' j,
          rw aux j at H₁',
          simp [← H₁', (H₂ i' j), hi'₁, hi'₂] },
        { rw hj' at *,
          use [i', 0],
          have H₁' := H₁ i' 0,
          simp at H₁',
          simp [← H₁', (H₂ i' 0), hi'₁, hi'₂] },
        { use [i', j'],
          have H₁' := H₁ i' j',
          simp [hj'₁, hj'₂] at H₁',
          simp [← H₁', (H₂ i' j'), hi'₁, hi'₂] } } },
    unfold is_minimal at h ⊢,
    rw ← h₁,
    split,
    { exact h.1 },
    intros i' j' H,
    rcases h₂ i' j' with ⟨k, l, h'⟩,
    rw ← h' at H ⊢,
    exact h.2 k l H },
  -- matrices are equivalent
  have h₁ := matrix_equiv_rel.unit_mul A (elem_matrix.perm R (n + 1) 0 i) elem_matrix.perm_inv,
  have h₂ := matrix_equiv_rel.mul_unit ((elem_matrix.perm R (n + 1) 0 i) ⬝ A) (elem_matrix.perm R (n + 1) 0 j) elem_matrix.perm_inv,
  exact matrix_equiv_rel.r_trans h₁ h₂,
end

-- Assume B 0 0 doesn't divide all elements in row 1 or column 1, then perform EA to give a new (smaller) minimal element
lemma temp1 {R : Type*} [euclidean_domain R] [decidable_eq R] {n : ℕ} (A : matrix (fin (n + 1)) (fin (n + 1)) R)  (hA0 : A ≠ 0) (h00 : is_minimal A 0 0) (i : fin (n + 1)) (H : ¬(A 0 0 ∣ A i 0) ∨ ¬(A 0 0 ∣ A 0 i) ) : ∃ (B : matrix (fin (n + 1)) (fin (n + 1)) R), ((B i 0 ≺ A 0 0) ∨ (B 0 i ≺ A 0 0)) ∧ matrix_equiv_rel.r R (n + 1) (n + 1) A B :=
begin
  have hi : i ≠ 0,
    { intro hc,
      rw hc at H,
      cases H;
      contradiction },
  cases H,
  -- Argument for column 0 and row 0 are almost identical but do have small differences
  -- column 0
  { let B := (elem_matrix.add_mult (n + 1) i 0 (-((A i 0) / (A 0 0))) hi),
    have h' : is_unit B,
    { exact @elem_matrix.add_mult_inv R _inst_1 (n + 1) i 0 (-((A i 0) / (A 0 0))) hi },
    use [B ⬝ A],
    split,
    { left,
      -- minimal valuation is lower
      have h : (B ⬝ A) i 0 = (A i 0) % (A 0 0),
      { simp [euclidean_domain.mod_eq_sub_mul_div],
        rw elem_matrix.add_mult_mul A i 0 (-((A i 0) / (A 0 0))) hi,
        ring_nf },
      rw h,
      exact euclidean_domain.remainder_lt (A i 0) h00.1 },
    -- matrices are equivalent
    -- unfold matrix_equiv_rel.r,
    use [B⁻¹, 1],
    simp,
    split,
    { cases h' with u h',
      use u⁻¹,
      simp [h'] },
    simp [← matrix.mul_assoc, matrix.nonsing_inv_mul B ((matrix.is_unit_iff_is_unit_det B).1 h')] },
  -- row zero
  let B := (elem_matrix.add_mult (n + 1) 0 i (-((A 0 i) / (A 0 0))) hi.symm),
  have h' : is_unit B,
    { exact @elem_matrix.add_mult_inv R _inst_1 (n + 1) 0 i (-((A 0 i) / (A 0 0))) hi.symm },
  use [A ⬝ B],
  split,
  { right,
    -- minimal valuation is lower
    have h : (A ⬝ B) 0 i = (A 0 i) % (A 0 0),
    { simp [euclidean_domain.mod_eq_sub_mul_div],
      rw elem_matrix.mul_add_mult A 0 i (-((A 0 i) / (A 0 0))) hi.symm,
      ring_nf },
    rw h,
    exact euclidean_domain.remainder_lt (A 0 i) h00.1 },
  -- matrices are equivalent
  -- unfold matrix_equiv_rel.r,
  use [1, B⁻¹],
  simp,
  split,
  { cases h' with u h',
    use u⁻¹,
    simp [h'] },
  have := ((matrix.is_unit_iff_is_unit_det B).1 h'),
  simp [matrix.mul_assoc, matrix.mul_nonsing_inv B ((matrix.is_unit_iff_is_unit_det B).1 h')]
end

-- __1__ Assume B 0 0 does divide all elements in row 1 or column 1, then can make them all into zero's __For Loop Implementation__


-- __2__ We will always be in one of the above cases, if first one, there will be finitely many steps to second case (using well founded tactics, see extended EA and gcd processes proof) By The Equation Compiler and __Using_Well_Founded__


-- inductive steps between n and (n + 1)
-- __3__ 
lemma equiv_simple_block_diag {R : Type*} [euclidean_domain R] {n : ℕ} (h : n > 0) (A : matrix (fin (n + 1)) (fin (n + 1)) R) : ∃ (B : matrix (fin n) (fin n) R) (b : R), matrix_equiv_rel.r R (n + 1) (n + 1) A (simple_block_diag b B) :=
begin
  unfold simple_block_diag,
  sorry
end
-- use `matrix.submatrix`?


-- __4__ 
lemma temp2 {R : Type*} [euclidean_domain R] [decidable_eq R] {n : ℕ} (hn : n > 0) (A : matrix (fin n) (fin n) R) (B : matrix (fin n) (fin n) R) (hB : snf B) (hA : matrix_equiv_rel.r R n n A B) {a : R} : ∃ (C : matrix (fin (n + 1)) (fin (n + 1)) R), matrix_equiv_rel.r R (n + 1) (n + 1) (simple_block_diag a A) C ∧ snf C := sorry

-- Show that any zero matrix is in smith normal form
-- show that any non-zero 1x1 matrix is in smith normal form




/-
__Miscellaneous Defintions of SNF not currently implemented__

def smith_norm_form {n : ℕ} {D : Type*} [euclidean_domain D] (A : matrix (fin n) (fin n) D) : Prop :=
∃ (d : (fin n) → D) (r : ℕ), (A = matrix.diagonal d) ∧ (∀ (i : fin n), ↑i ≥ r ↔ d i = 0 ) ∧ (∀ (i j : fin n), (i ≤ j) → ↑j < r → (d i) ∣ (d j))



-- # Smith Normal Form (limited to nxn matrices)

def smith_norm_form {n : ℕ} {D : Type*} [euclidean_domain D] (A : matrix (fin n) (fin n) D) : Prop :=
∃ (d : (fin n) → D) (r : ℕ), (A = matrix.diagonal d) ∧ (∀ (i : fin n), ↑i ≥ r ↔ d i = 0 ) ∧ (∀ (i j : fin n), (i ≤ j) → ↑j < r → (d i) ∣ (d j))

-- # Main Theorem

theorem mat_equiv_to_smith_norm_mat {n : ℕ} {D : Type*} {D : Type*} [euclidean_domain D] (A : matrix (fin n) (fin n) D) : ∃ (B : matrix (fin n) (fin n) D), smith_norm_form B ∧ (matrix_equiv_rel.R D n n A B) :=
begin
  sorry
end

-/


end smith_norm_form