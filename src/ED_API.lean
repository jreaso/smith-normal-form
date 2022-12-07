import algebra.euclidean_domain
import order.well_founded

local infix ` ≺ `:50 := euclidean_domain.r

--open classical -- do i use it?

namespace euclidean_domain_temp
universe u
open euclidean_domain

lemma zero_lt_one {R : Type u} [euclidean_domain R] : (0 : R) ≺ 1 := by {rw [← zero_mod (1 : R)], exact mod_lt 0 zero_ne_one.symm}

lemma lt_one_iff {R : Type u} [euclidean_domain R] : ∀ {a : R}, a ≺ 1 ↔ a = 0 := 
λ a, ⟨lt_one a, λ h, h.symm ▸ zero_lt_one⟩

lemma unit_not_lt_one {R : Type u} [euclidean_domain R] {u : R} (h : is_unit u) : ¬ u ≺ 1 :=
λ h', by exact (is_unit.ne_zero h) (lt_one u h')

lemma one_not_lt_unit {R : Type u} [euclidean_domain R] {u : R} (h : is_unit u) : ¬ 1 ≺ u :=
begin
  intro h',
  
  sorry
end

-- zero is the minimum possible valuation
lemma gt_not_eq_zero {R : Type*} [euclidean_domain R] : ∀ {a b : R}, a ≺ b → b ≠ 0 := λ a b,
begin
  intro h,
  by_contra h',
  rw h' at h,
  -- need transitivity between 0 and 1: a ≺ 0 ≺ 1 → a ≺ 1???
  --intro h,
  --simp at h,
  sorry --`0 % c = 0` (`zero_mod`)
  -- if b ≠ 0 then (`remainder_lt`) → (0 % b = 0) ≺ b

end

lemma lt_trans {R : Type u} [euclidean_domain R] : ∀ {a b c : R}, (a ≺ b) → (b ≺ c) → (a ≺ c) := λ a b c hab hbc,
begin
  have hb := gt_not_eq_zero hab,
  have hc := gt_not_eq_zero hbc,
  
  by_contra,
  sorry
end

lemma irrefl {R : Type*} [euclidean_domain R] : ∀ {a : R}, ¬ (a ≺ a) := λ a,
begin
  by_cases a = 0,
  { intro h,
    have h' := gt_not_eq_zero h,
    contradiction },
  exact euclidean_domain.val_dvd_le a a dvd_rfl h
end

lemma asymm {R : Type*} [euclidean_domain R] : ∀ {a b : R}, (a ≺ b) → ¬(b ≺ a) := λ a b hab,
begin
  
  sorry
end

-- # Euclidean Domains Have a Preorder ≺

-- lt : euclidean_domain.r or ≺
-- te : ≼ : 

def re 



end euclidean_domain_temp





-- define a ≼ relation in obvious way to use as a preorder