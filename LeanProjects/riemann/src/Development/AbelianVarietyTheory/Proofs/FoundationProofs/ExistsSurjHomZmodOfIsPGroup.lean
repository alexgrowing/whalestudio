import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_surj_hom_zmod_of_isPGroup :
    ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] [Nontrivial G],
      IsPGroup p G → ∃ χ : G →* Multiplicative (ZMod p), Function.Surjective χ := by
  intro p hp G _ _ _ hG
  obtain ⟨n, hn, hc⟩ := hG.nontrivial_iff_card.1 inferInstance
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) p (n := m)
    (by rw [hc]; exact pow_dvd_pow p (Nat.le_succ m))
  have hi : K.index = p := by
    have := K.card_mul_index
    rw [hK, hc, pow_succ] at this
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos m) this
  haveI : K.Normal := Subgroup.normal_of_index_eq_minFac_card (by
    rw [hi, hc, hp.out.pow_minFac (Nat.succ_ne_zero m)])
  let e : (G ⧸ K) ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq (p := p) (by rw [← hi]; rfl) (by simp)
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' K), ?_⟩
  exact e.surjective.comp (QuotientGroup.mk'_surjective K)

end GlobalTheory.AlmostEt
