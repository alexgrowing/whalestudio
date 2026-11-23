import Mathlib
import Formalism.CMTypeGalois.StatementGroup

namespace Formalism.Q3

open ZMod

lemma kron_odd (q p : ℕ) (hq4 : q % 4 = 3) (hp : p.Prime) (hp2 : p ≠ 2) :
    jacobiSym (p : ℤ) q = jacobiSym (-(q : ℤ)) p := by
  have hpo : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hqo : q % 2 = 1 := by omega
  rw [jacobiSym.neg _ (Nat.odd_iff.mpr hpo)]
  have h := jacobiSym.quadratic_reciprocity_if hpo hqo
  rcases Nat.odd_mod_four_iff.mp hpo with h1 | h3
  · rw [χ₄_nat_one_mod_four h1, one_mul, ← h]
    simp [h1]
  · rw [χ₄_nat_three_mod_four h3, ← h]
    simp [h3, hq4]

theorem kroneckerMeaning : KroneckerMeaning := by
  intro q hq hq4
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  refine ⟨fun p hp hp2 _ => kron_odd q p hq4 hp hp2, ?_, ?_⟩
  · unfold chiQ
    rw [jacobiSym.at_two hqo, χ₈_nat_eq_if_mod_eight]
    rw [if_neg (by omega)]
    by_cases h8 : q % 8 = 7
    · rw [if_pos (Or.inr h8)]; simp [h8]
    · rw [if_neg (by omega)]; simp [h8]
  · unfold chiQ
    rw [jacobiSym.at_neg_one hqo, χ₄_nat_three_mod_four hq4]

lemma sgn_one : sgn 1 = 1 := by
  unfold sgn; rw [if_pos rfl]

lemma cc_not_mem (a b : Gal3) (j : Fin 3) (ha : a j = 1) (hb : b j = 1) :
    cc ∉ Subgroup.closure ({a, b} : Set Gal3) := by
  intro h
  have hle : Subgroup.closure ({a, b} : Set Gal3) ≤ (Pi.evalMonoidHom (fun _ : Fin 3 => ℤˣ) j).ker := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, Pi.evalMonoidHom_apply]; exact ha
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, Pi.evalMonoidHom_apply]; exact hb
  have := hle h
  rw [MonoidHom.mem_ker, Pi.evalMonoidHom_apply] at this
  have h' : (-1 : ℤˣ) = 1 := this
  exact absurd h' (by decide)

end Formalism.Q3
