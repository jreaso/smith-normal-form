import tactic
import data.matrix.basic
import data.matrix.block
import linear_algebra.matrix.block
import linear_algebra.matrix.nonsingular_inverse
import algebra.group.units
import order.well_founded

variables {R : Type*} [euclidean_domain R] (n m : ℕ) (A : matrix (fin n) (fin n) R) (B : matrix (fin n) (fin n) R) (b : R)


#check (@fin_sum_fin_equiv 1 n).trans


example (n : ℕ) : fin 1 ⊕ fin n ≃ fin (1 + n) :=
begin
  exact fin_sum_fin_equiv,
end

example (n : ℕ) : fin 1 ⊕ fin n ≃ fin (n + 1) := (fin_sum_fin_equiv.trans fin_add_flip)




#check matrix.reindex (fin_sum_fin_equiv.trans fin_add_flip).symm (fin_sum_fin_equiv.trans fin_add_flip).symm (1 : matrix (fin (n + 1)) (fin (n + 1)) ℤ)


#check (matrix.from_blocks (b • (1 : matrix (fin 1) (fin 1) R)) 0 0 B)

#check (matrix.reindex (fin_sum_fin_equiv.trans fin_add_flip) (fin_sum_fin_equiv.trans fin_add_flip) (matrix.from_blocks (b • (1 : matrix (fin 1) (fin 1) R)) 0 0 B))

--#check matrix.reindex


--(matrix.from_blocks (b • (1 : matrix (fin 1) (fin 1) R)) 0 0 B)

def simple_block_diag {R : Type*} [euclidean_domain R] {n : ℕ} (a : R) (A : matrix (fin n) (fin n) R) : matrix (fin (n + 1)) (fin (n + 1)) R :=
matrix.reindex (fin_sum_fin_equiv.trans fin_add_flip) (fin_sum_fin_equiv.trans fin_add_flip) (matrix.from_blocks (a • (1 : matrix (fin 1) (fin 1) R)) 0 0 A)

#check simple_block_diag