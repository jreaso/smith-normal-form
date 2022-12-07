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
