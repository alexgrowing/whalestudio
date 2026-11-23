import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime]

theorem ainf_exists_l_mul_of_coeff_zero (a : Ainf l) (h : a.coeff 0 = 0) :
    ∃ b : Ainf l, a = (l : Ainf l) * b := by
  have hv := WittVector.eq_iterate_verschiebung (n := 1) (x := a) (fun i hi => by
    rw [Nat.lt_one_iff.1 hi]; exact h)
  have hsurj : Function.Surjective (WittVector.frobenius : Ainf l → Ainf l) := by
    rw [WittVector.frobenius_eq_map_frobenius]
    exact WittVector.map_surjective _ (frobeniusEquiv (OCb l) l).surjective
  obtain ⟨c, hc⟩ := hsurj (a.shift 1)
  refine ⟨c, ?_⟩
  rw [hv, Function.iterate_one, ← hc, WittVector.verschiebung_frobenius, mul_comm]

theorem coeff_zero_l_mul {R : Type} [CommRing R] [CharP R l] (x : WittVector l R) :
    ((l : WittVector l R) * x).coeff 0 = 0 := by
  change WittVector.constantCoeff ((l : WittVector l R) * x) = 0
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem isUnit_inclW_per_and_saturated : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l),
    bk.IsPer τ → IsUnit (inclW l τ) ∧ (∀ g : GQ l, IsUnit (inclW l (Per.σA g τ))) ∧
      ∀ (k : ℕ) (a : Ainf l), ((l : ℕ) : WCb l) ^ k ∣ inclW l a → ((l : ℕ) : Ainf l) ^ k ∣ a := by
  intro l _ K bk τ hτ
  obtain ⟨-, ε, η, hε, hφ⟩ := hτ
  have hε1 : ε ≠ 1 := by
    rintro rfl
    obtain ⟨-, hu⟩ := hε
    exact hu (by rw [map_one]; simp)
  have hc0 : τ.coeff 0 ≠ 0 := by
    intro h0
    have h1 := congrArg (fun x => WittVector.constantCoeff x) hφ
    change (WittVector.frobenius τ).coeff 0 = _ at h1
    rw [WittVector.coeff_frobenius_charP, h0, zero_pow (Fact.out : l.Prime).ne_zero, map_mul, map_sub, map_one] at h1
    change 0 = WittVector.constantCoeff (η : Ainf l) * ((WittVector.teichmuller l ε).coeff 0 - 1) at h1
    rw [WittVector.teichmuller_coeff_zero] at h1
    have hη : IsUnit (WittVector.constantCoeff (η : Ainf l)) := η.isUnit.map _
    rcases mul_eq_zero.1 h1.symm with h | h
    · exact hη.ne_zero h
    · exact hε1 (sub_eq_zero.1 h)
  have hU : IsUnit (inclW l τ) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    change algebraMap (OCb l) (Cb l) (τ.coeff 0) ≠ 0
    exact (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 hc0
  refine ⟨hU, fun g => ?_, ?_⟩
  · rw [← galW_inclW]
    exact hU.map (galW l g)
  · intro k
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
      intro a ⟨c, hc⟩
      have h0 : a.coeff 0 = 0 := by
        have h1 : (inclW l a).coeff 0 = 0 := by
          rw [hc, pow_succ', mul_assoc]; exact coeff_zero_l_mul _
        change algebraMap (OCb l) (Cb l) (a.coeff 0) = 0 at h1
        exact (map_eq_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).1 h1
      obtain ⟨b, rfl⟩ := ainf_exists_l_mul_of_coeff_zero a h0
      have hl0 : ((l : ℕ) : WCb l) ≠ 0 := fun h => by
        have h1 := congrArg (fun x : WCb l => x.coeff 1) h
        simp [WittVector.coeff_p] at h1
      have hb : ((l : ℕ) : WCb l) ^ k ∣ inclW l b := by
        refine ⟨c, mul_left_cancel₀ hl0 ?_⟩
        rw [← mul_assoc, ← pow_succ', ← hc, map_mul, map_natCast]
      exact pow_succ' ((l : ℕ) : Ainf l) k ▸ mul_dvd_mul_left _ (ih b hb)

end GlobalTheory.BSP
