import tactic
import data.matrix.basic
import data.matrix.block
import linear_algebra.matrix.block
import linear_algebra.matrix.nonsingular_inverse
import algebra.group.units
import order.well_founded

open_locale matrix
open_locale big_operators










-- # Elementary Matrices

-- ## Definiton of the Elementary Matrices

namespace elem_matrix

-- Basis Δ
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
    simp [h₁] }, --duplicate block to above
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

-- ADD TO LIBRARY IN `data.matrix.pequiv`
lemma pequiv.to_pequiv_matrix_mul {m n α : Type*} [fintype n] [decidable_eq n] [semiring α] (f : n ≃ n) (M : matrix m n α): 
(M ⬝ f.to_pequiv.to_matrix) = λ i j, M i (f.symm j) :=
by {  ext i j, rw [pequiv.matrix_mul_apply, ←equiv.to_pequiv_symm, equiv.to_pequiv_apply]}
-- necessary for later lemmas

-- ### Effect of Permutation Matrix

lemma perm_mul {R : Type*} [euclidean_domain R] {n : ℕ} (A : matrix (fin n) (fin n) R) (k l : fin n) : ∀ (i j : fin n), A i j = ((elem_matrix.perm R n k l) ⬝ A) (ite (i = k) l (ite (i = l) k i)) j
:= λ i j, by { unfold elem_matrix.perm, simp [pequiv.to_pequiv_mul_matrix, ←equiv.swap_apply_def] }

lemma perm_mul' {R : Type*} [euclidean_domain R] {n : ℕ} (A : matrix (fin n) (fin n) R) (k l : fin n) : ∀ (i j : fin n), ((elem_matrix.perm R n k l) ⬝ A) i j = A (ite (i = k) l (ite (i = l) k i)) j 
:= λ i j, by { unfold elem_matrix.perm, simp [pequiv.to_pequiv_mul_matrix, equiv.swap_apply_def] }

lemma mul_perm {R : Type*} [euclidean_domain R] {n : ℕ} (A : matrix (fin n) (fin n) R) (k l : fin n) : ∀ (i j : fin n), A i j = (A ⬝ (elem_matrix.perm R n k l)) i (ite (j = k) l (ite (j = l) k j))
:= λ i j, by { unfold elem_matrix.perm, simp [pequiv.to_pequiv_matrix_mul, ←equiv.swap_apply_def] }

lemma mul_perm' {R : Type*} [euclidean_domain R] {n : ℕ} (A : matrix (fin n) (fin n) R) (k l : fin n) : ∀ (i j : fin n), (A ⬝ (elem_matrix.perm R n k l)) i j = A i (ite (j = k) l (ite (j = l) k j))
:= λ i j, by { unfold elem_matrix.perm, simp [pequiv.to_pequiv_matrix_mul, equiv.swap_apply_def] }


end elem_matrix












-- # Equivalence of m x n matrices

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

-- Notation for euclidean_domain.r
local infix ` ≺ `:50 := euclidean_domain.r

namespace smith_norm_form

-- ## Definitions

-- Simple version of smith normal form, without division condition, and limited to nxn
def snf {n : ℕ} {R : Type*} [euclidean_domain R] [decidable_eq R] (A : matrix (fin n) (fin n) R) : Prop :=
∃ (d : (fin n) → R) (r : ℕ), (A = matrix.diagonal d) ∧ (∀ (i : fin n), ↑i ≥ r ↔ d i = 0 ) --∧ (∀ (i j : fin n), (i ≤ j) → ↑j < r → (d i) ∣ (d j))

-- desired form for induction step
def simple_block_diag {R : Type*} [euclidean_domain R] {n : ℕ} (a : R) (A : matrix (fin n) (fin n) R) : matrix (fin (n + 1)) (fin (n + 1)) R :=
matrix.reindex (fin_sum_fin_equiv.trans fin_add_flip) (fin_sum_fin_equiv.trans fin_add_flip) (matrix.from_blocks (a • (1 : matrix (fin 1) (fin 1) R)) 0 0 A)
/-
a 0 0 0
0 |   |
0 | A |
0 |   |
-/

-- An element of a matrix (over a ED) is minimal if it's non zero and has minimal valuation (excluding zeros)
def is_minimal {R : Type*} [euclidean_domain R] {n : ℕ} (A : matrix (fin n) (fin n) R) (k l : fin n) : Prop := (A k l ≠ 0) ∧ (∀ (i j : fin n), A i j ≠ 0 → ¬((A i j) ≺ (A k l)))

-- ## Lemmas Setting Up Main Result

-- Every non-zero matrix has an element with minimal valuation
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


-- Move minimal element to top left
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
      -- Very manual solution, return to later and use `aux` and similar results
      have H₁ := elem_matrix.mul_perm ((elem_matrix.perm R (n + 1) 0 i) ⬝ A) 0 j,
      have H₂ := elem_matrix.perm_mul A 0 i,
      have hi' : i' = 0 ∨ i' = i ∨ (i' ≠ 0 ∧ i' ≠ i), by tauto,
      have hj' : j' = 0 ∨ j' = i ∨ (j' ≠ 0 ∧ j' ≠ i), by tauto,
      have hi0 : i = 0 ∨ i ≠ 0, by tauto,
      rcases hi' with hi' | hi' | ⟨hi'₁, hi'₂⟩;
      rcases hj' with hj' | hj' | ⟨hj'₁, hj'₂⟩,
      { rw [hi', hj'] at *,
        use [i, i],
        have H₁' := H₁ 0 i,
        rw [aux i] at H₁',
        rw [← H₁', (H₂ i i), aux i] },
      { rw [hi', hj'] at *,
        use [j', 0],
        have H₁' := H₁ 0 0,
        simp at H₁',
        rw [← H₁', (H₂ j' 0)],
        cases hi0;
        simp [hi', hj', hi0] },
      { rw [hi'] at *,
        use [i, j'],
        have H₁' := H₁ 0 j',
        simp [hj'₁, hj'₂] at H₁',
        rw [← H₁', (H₂ i j')],
        cases hi0;
        simp [hi0] },
      { rw [hi', hj'] at *,
        use [0, i],
        have H₁' := H₁ i i,
        rw [aux i] at H₁',
        rw [← H₁', (H₂ 0 i)],
        simp },
      { rw [hi', hj'] at *,
        use [0, 0],
        have H₁' := H₁ i 0,
        simp at H₁',
        rw [← H₁', (H₂ 0 0)],
        simp },
      { rw hi' at *,
        use [0, j'],
        have H₁' := H₁ i j',
        simp [hj'₁, hj'₂] at H₁',
        rw [← H₁', (H₂ 0 j')],
        simp },
      { rw hj' at *,
        use [i', i],
        have H₁' := H₁ i' i,
        rw aux i at H₁',
        rw [← H₁', (H₂ i' i)],
        simp [hi'₁, hi'₂] },
      { rw hj' at *,
        use [i', 0],
        have H₁' := H₁ i' 0,
        simp at H₁',
        rw [← H₁', (H₂ i' 0)],
        simp [hi'₁, hi'₂] },
      { use [i', j'],
        have H₁' := H₁ i' j',
        simp [hj'₁, hj'₂] at H₁',
        rw [← H₁', (H₂ i' j')],
        simp [hi'₁, hi'₂] } },
    unfold is_minimal at h ⊢,
    rw ← h₁,
    split,
    { exact h.1 },
    intros i' j' H,
    rcases h₂ i' j' with ⟨k, l, h'⟩,
    rw ← h' at H ⊢,
    exact h.2 k l H,
  },
  -- matrices are equivalent
  have h₁ := matrix_equiv_rel.unit_mul A (elem_matrix.perm R (n + 1) 0 i) elem_matrix.perm_inv,
  have h₂ := matrix_equiv_rel.mul_unit ((elem_matrix.perm R (n + 1) 0 i) ⬝ A) (elem_matrix.perm R (n + 1) 0 j) elem_matrix.perm_inv,
  exact matrix_equiv_rel.r_trans h₁ h₂,
end





-- Assume B 0 0 doesn't divide all elements in row 1 or column 1, then perform EA to give a new (smaller) minimal element


-- Assume B 0 0 does divide all elements in row 1 or column 1, then can make them all into zero's __Difficult__


-- We will always be in one of the above cases, if first one, there will be finitely many steps to second case (using well founded tactics, see extended EA and gcd processes proof) __Difficult__











-- inductive step between n and (n + 1)
theorem equiv_simple_block_diag {R : Type*} [euclidean_domain R] {n : ℕ} (h : n > 0) (A : matrix (fin (n + 1)) (fin (n + 1)) R) : ∃ (B : matrix (fin n) (fin n) R) (b : R), matrix_equiv_rel.r R (n + 1) (n + 1) A (simple_block_diag b B) :=
begin

  unfold simple_block_diag,
  sorry
end




-- ## Main Result








/-

def prelim_smith_norm_form {n : ℕ} {D : Type*} [euclidean_domain D] (A : matrix (fin n) (fin n) D) : Prop :=
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