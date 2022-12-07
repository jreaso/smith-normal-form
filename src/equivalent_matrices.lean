import tactic -- delete later if never use
import data.matrix.basic
import linear_algebra.matrix.nonsingular_inverse
import algebra.group.units
--import linear_algebra.matrix.block

open_locale matrix
--open_locale big_operators


/-- Equivalence class for a binary relation -/
--def equivalence_class {X : Type} (R : X → X → Prop) (x : X) := {y : X | R x y}


-- # Equivalence of m x n matrices
-- two mxn matrices A and B are quivalent if A = M B N and M and N are invertible (mxm and nxn)

def equiv_mat {D : Type*} [euclidean_domain D] {m n : ℕ}  (A B : matrix (fin m) (fin n) D) : Prop :=
∃ (M : matrix (fin m) (fin m) D) (N : matrix (fin n) (fin n) D), (is_unit M.det) ∧ (is_unit N.det) ∧ ( A = M ⬝ B ⬝ N )

variables (D : Type*) [euclidean_domain D] (m n : ℕ)

/-def R : (matrix (fin m) (fin n) D → matrix (fin m) (fin n) D → Prop) := 
λ A, (λ B, ∃ (M : matrix (fin m) (fin m) D) (N : matrix (fin n) (fin n) D), (is_unit M) ∧ (is_unit N) ∧ ( A = M ⬝ B ⬝ N ))-/


lemma equiv_mat_refl {D : Type*} [euclidean_domain D] {m n : ℕ} : ∀ (A : matrix (fin m) (fin n) D), equiv_mat A A :=
begin
  intro A,
  use [1,1],
  finish,
end

lemma equiv_mat_symm {D : Type*} [euclidean_domain D] {m n : ℕ} : ∀ (A B : matrix (fin m) (fin n) D), equiv_mat A B → equiv_mat B A :=
begin
  rintros A B ⟨M, N, hM, hN, h⟩,
  use [M⁻¹, N⁻¹],
  split,
  { rw matrix.det_inv_of,
    sorry },
  split,
  sorry,
  calc
    B = (M⁻¹ ⬝ M) ⬝ B ⬝ (N ⬝ N⁻¹) : by {simp [matrix.mul_nonsing_inv N hN, matrix.nonsing_inv_mul M hM]}
    ... = M⁻¹ ⬝ (M ⬝ B ⬝ N) ⬝ N⁻¹ : by {simp [matrix.mul_assoc]}
    ... = M⁻¹ ⬝ A ⬝ N⁻¹ : by {rw h}
end



variables (A B : (matrix (fin 7) (fin 3) ℤ))

example : equivalent_matrix A A := 
begin
  unfold equivalent_matrix,
  use [1,1],
  finish,
end


theorem R_equivalence_class : equivalence (R D m n) :=
begin
  have reflexive (R),

  exact mk_equivalence R _ _ _,
  sorry
end

