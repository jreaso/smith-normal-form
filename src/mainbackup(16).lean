import tactic
import data.matrix.basic
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.block
import algebra.group.units

open_locale matrix
open_locale big_operators


-- # Definiton of the Elementary Matrices

namespace elem_matrix

-- Basis Δ
def basis (D : Type*) [euclidean_domain D] (n : ℕ) (i j : fin n) : matrix (fin n) (fin n) D :=
(λ i' j', if i = i' ∧ j = j' then 1 else 0)

-- Type I: Add multiple of column/row i to j
def add_mult {D : Type*} [euclidean_domain D] (n : ℕ) (i j : fin n) (a : D) (h : i ≠ j) : matrix (fin n) (fin n) D :=
1 + a • (basis D n i j)

-- Type II: Multiply row/column by a unit
def mul_by_unit {D : Type*} [euclidean_domain D] (n : ℕ) (i : fin n) (u : D) (h : is_unit u) : matrix (fin n) (fin n) D :=
matrix.diagonal (λ i', if i' = i then u else 1)
--1 + (u - 1) • (basis D n i i)

-- Type III: Permutation
def perm (D : Type*) [euclidean_domain D] (n : ℕ) (i j : fin n) : matrix (fin n) (fin n) D :=
(equiv.to_pequiv (equiv.swap i j)).to_matrix
-- 1 - (basis D n i i) - (basis D n j j) + (basis D n i j) + (basis D n j i)


-- # Elementary Matrices are Invertible (units)

section
variables {D : Type*} [euclidean_domain D]
variables {n : ℕ} {i j : fin n}

theorem add_mult_inv {a : D} (h : i ≠ j) : is_unit (add_mult n i j a h) :=
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

theorem mul_by_unit_inv {u : D} (h : is_unit u) : is_unit (mul_by_unit n i u h) := 
begin
  apply (matrix.is_unit_iff_is_unit_det (mul_by_unit n i u h)).2,
  unfold mul_by_unit,
  simp [matrix.det_diagonal, finset.prod_ite],
  exact is_unit.pow (finset.filter (λ (x : fin n), x = i) finset.univ).card h,
end

theorem perm_inv : is_unit (perm D n i j) := 
begin
  apply (matrix.is_unit_iff_is_unit_det (perm D n i j)).2, -- has determinant -1
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

end
end elem_matrix

-- # Additional matrix definition for PID case

/-
def temp (D : Type*) [euclidean_domain D] (n : ℕ) (hn : n ≥ 2) (A : matrix (fin 2) (fin 2) D) (hA : is_unit A) : matrix (fin n) (fin n) D :=
(A 0 0) + (matrix.diagonal (λ i, if ↑i ≤ 1 then 0 else 1))
-/


-- # Equivalence of m x n matrices

-- two mxn matrices A and B are quivalent if A = M B N and M and N are invertible (mxm and nxn)
def R (D : Type*) [euclidean_domain D] (m n : ℕ) : (matrix (fin m) (fin n) D) → (matrix (fin m) (fin n) D) → Prop :=
λ A, (λ B, ∃ (M : matrix (fin m) (fin m) D) (N : matrix (fin n) (fin n) D), (is_unit M) ∧ (is_unit N) ∧ ( A = M ⬝ B ⬝ N ))



lemma R_refl {D : Type*} [euclidean_domain D] {m n : ℕ} : reflexive (R D m n) :=
--lemma R_refl {D : Type*} [euclidean_domain D] {m n : ℕ} : ∀ (A : matrix (fin m) (fin n) D), R D m n A A :=
begin
  intro A,
  use [1,1],
  finish,
end

lemma R_symm {D : Type*} [euclidean_domain D] {m n : ℕ} : symmetric (R D m n) :=
--lemma R_symm {D : Type*} [euclidean_domain D] {m n : ℕ} : ∀ (A B : matrix (fin m) (fin n) D), R D m n A B → R D m n B A :=
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

lemma R_trans {D : Type*} [euclidean_domain D] {m n : ℕ} : transitive (R D m n) :=
--lemma R_trans {D : Type*} [euclidean_domain D] {m n : ℕ} : ∀ (A B C : matrix (fin m) (fin n) D), R A B → R B C → R A C :=
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

theorem equiv_R {D : Type*} [euclidean_domain D] {m n : ℕ} : equivalence (R D m n) := ⟨R_refl, R_symm,  R_trans⟩


-- # Experimenting prior to proof of main result

-- left multiplication by invertible matrix preserves equivalence
example (D : Type*) [euclidean_domain D] (m n : ℕ) (M : matrix (fin m) (fin n) D) (A : matrix (fin m) (fin m) D) (h : is_unit A) : R M (A ⬝ M) :=
begin
  use [A⁻¹, 1],
  --simp [matrix.nonsing_inv_eq_ring_inverse, h, ← matrix.mul_assoc, ← matrix.mul_eq_mul, (ring.inverse_mul_cancel A h)],  --can just use one simp
  simp [matrix.nonsing_inv_eq_ring_inverse, h],
  rw [← matrix.mul_assoc, ← matrix.mul_eq_mul, (ring.inverse_mul_cancel A h)],
  simp
end

-- # Lemmas for proof of main result

--


-- # Smith Normal Form (Preliminary form for nxn matrices)

def smith_norm_form' {n : ℕ} {D : Type*} [euclidean_domain D] (A : matrix (fin n) (fin n) D) : Prop :=
∃ (d : (fin n) → D) (r : ℕ), (A = matrix.diagonal d) ∧ (∀ (i : fin n), ↑i ≥ r ↔ d i = 0 ) ∧ (∀ (i j : fin n), (i ≤ j) → ↑j < r → (d i) ∣ (d j))


--Examples

-- 7x7 identity matrix has smith normal form
example {D : Type*} [euclidean_domain D] : smith_norm_form' (1 : matrix (fin 7) (fin 7) D) :=
begin
  use [(λ (i : fin 7), 1), 7],
  simp,
  intro i,
  exact fin.is_lt i,
end


def mymat := matrix.diagonal (λ (i : fin 9), if i < 5 then (3 : ℤ) else (if i < 7 then (9 : ℤ) else (0 : ℤ)))
#check mymat
#eval mymat
/-
[3, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 3, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 3, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 3, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 3, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 9, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 9, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0;
 0, 0, 0, 0, 0, 0, 0, 0, 0]
-/

example : smith_norm_form' mymat :=
begin
  use [(λ (i : fin 9), if i < 5 then (3 : ℤ) else (if i < 7 then (9 : ℤ) else (0 : ℤ))), 7],
  split,
  { refl },
  split,
  { intro i,
    split,
    { intro h,
      sorry },
    sorry },
  intros i j hij hj6,
  sorry
end --all the sorrys can be solved ... just tedious and non-productive


example {D : Type*} [euclidean_domain D] {n : ℕ} (A : matrix (fin n) (fin n) D) (h : ∃ (i j : fin n), i ≠ j ∧ A i j ≠ 0) : ¬ smith_norm_form' A :=
begin
  rcases h with ⟨i, j, hij, hAij⟩,
  intro h,
  unfold smith_norm_form' at h,
  rcases h with ⟨d, r, hAdiag, h⟩, clear h, clear r,
  sorry -- shouldn't be too hard to finish, want to prove a false goal with hypothesis that A is diagonal but also that an off-diagonal entry is non-zero (contra)
end

-- # Main Theorem (preliminary version for nxn)

theorem temp {n : ℕ} {D : Type*} {D : Type*} [euclidean_domain D] (A : matrix (fin n) (fin n) D) : ∃ (B : matrix (fin n) (fin n) D), smith_norm_form' B ∧ R A B :=
begin
  
  sorry
end