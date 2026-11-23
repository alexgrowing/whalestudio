import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StRatFibreAvoid
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantSheetCover
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

namespace RatFibreAvoid

theorem exists_poly_mem_span {L : Type} [CommRing L] [IsDomain L] [Algebra ℂ L] {d : ℕ}
    (htr : Algebra.trdeg ℂ L ≤ d) (t : Fin d → L) {g : L} (hg : g ≠ 0) :
    ∃ h : MvPolynomial (Fin d) ℂ, h ≠ 0 ∧ aeval t h ∈ Ideal.span {g} := by
  by_cases ht : AlgebraicIndependent ℂ t
  · have hgalg : IsAlgebraic (Algebra.adjoin ℂ (Set.range t)) g := by
      by_contra hna
      have hind := (AlgebraicIndependent.option_iff (x := t) (a := g)).2 ⟨ht, hna⟩
      have hle := le_trans hind.cardinalMk_le_trdeg htr
      rw [Cardinal.mk_option, Cardinal.mk_fin] at hle
      have : ((d + 1 : ℕ) : Cardinal.{0}) ≤ d := by exact_mod_cast hle
      have := Nat.cast_le.1 this
      omega
    have hne := Ideal.comap_ne_bot_of_algebraic_mem (R := Algebra.adjoin ℂ (Set.range t)) hg (Ideal.mem_span_singleton_self g) hgalg
    obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨h, hh⟩ : ∃ h, aeval (R := ℂ) t h = (s : L) := by
      have key : ∀ v ∈ Algebra.adjoin ℂ (Set.range t), ∃ h, aeval (R := ℂ) t h = v := by
        intro v hv
        rw [Algebra.adjoin_range_eq_range_aeval] at hv
        exact (AlgHom.mem_range _).1 hv
      exact key _ s.2
    refine ⟨h, ?_, ?_⟩
    · rintro rfl
      apply hs0
      ext
      simpa using hh.symm
    · rw [hh]
      exact Ideal.mem_comap.1 hs
  · rw [algebraicIndependent_iff] at ht
    push Not at ht
    obtain ⟨h, h0, hne⟩ := ht
    exact ⟨h, hne, by rw [h0]; exact zero_mem _⟩

theorem proof : RatFibreAvoid.Statement := by
  intro n d J p q f hJ hdim hf
  classical
  by_cases hq : q ∈ J
  · exact Filter.Eventually.of_forall fun y x hx => absurd (hx.1 q hq) hx.2.1
  set A := MvPolynomial (Fin n) ℂ ⧸ J with hA
  have hdom : IsDomain A := Ideal.Quotient.isDomain J
  set a : A := Ideal.Quotient.mk J q with ha_def
  have ha : a ≠ 0 := fun h => hq (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hpow : Submonoid.powers a ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors ha
  have hLdom : IsDomain (Localization.Away a) := IsLocalization.isDomain_localization hpow
  have htrA : Algebra.trdeg ℂ A = d := by
    obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := A)
    rw [hdim] at hs1
    have : s = d := by exact_mod_cast hs1.symm
    rw [hs2, this]
  have htrL : Algebra.trdeg ℂ (Localization.Away a) ≤ d := by
    have : FaithfulSMul ℂ A := (faithfulSMul_iff_algebraMap_injective ℂ A).2 (algebraMap ℂ A).injective
    have : FaithfulSMul A (Localization.Away a) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (IsLocalization.injective _ hpow)
    have : Algebra.IsAlgebraic A (Localization.Away a) := IsLocalization.isAlgebraic (Localization.Away a) (Submonoid.powers a)
    rw [← trdeg_add_eq ℂ A (A := Localization.Away a), trdeg_eq_zero (R := A) (A := Localization.Away a), add_zero, htrA]
  set T : Fin d → Localization.Away a := fun r =>
    algebraMap A _ (Ideal.Quotient.mk J (p r)) * IsLocalization.Away.invSelf a with hTdef
  have hg : algebraMap A (Localization.Away a) (Ideal.Quotient.mk J f) ≠ 0 := by
    intro h0
    apply hf
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact IsLocalization.injective _ hpow (by rw [h0, map_zero])
  obtain ⟨h, hne, hmem⟩ := exists_poly_mem_span htrL T hg
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  have key : ∀ x ∈ zeroSet J, eval x q ≠ 0 → eval x f = 0 → eval (RatChart.ratMap p q x) h = 0 := by
    intro x hx hqx hfx
    let ev : A →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ J (aeval x) (fun g hg => by simpa using hx g hg)
    have hev : ∀ g, ev (Ideal.Quotient.mk J g) = eval x g := fun g => by
      rfl
    have hea : ev a = eval x q := hev q
    have hu : IsUnit (ev a) := by
      rw [hea]
      exact hqx.isUnit
    let φ : Localization.Away a →ₐ[ℂ] ℂ := IsLocalization.Away.liftAlgHom a hu
    have hφ : ∀ z, φ (algebraMap A _ z) = ev z := fun z =>
      IsLocalization.Away.lift_eq (S := Localization.Away a) (g := (ev : A →+* ℂ)) a hu z
    have hinv : φ (IsLocalization.Away.invSelf a) = (eval x q)⁻¹ := by
      have := congrArg φ (IsLocalization.Away.mul_invSelf (S := Localization.Away a) a)
      rw [map_mul, map_one, hφ, hea] at this
      exact eq_inv_of_mul_eq_one_right this
    have hT : (fun r => φ (T r)) = RatChart.ratMap p q x := by
      funext r
      simp only [hTdef, map_mul, hφ, hev, hinv, RatChart.ratMap, div_eq_mul_inv]
    have := congrArg φ hc
    rw [comp_aeval_apply, hT, map_mul, hφ, hev, hfx, mul_zero] at this
    exact this.symm
  have hnull := DiscriminantSheetCover.volume_zero_set h hne
  have hae : ∀ᵐ y : Fin d → ℂ, eval y h ≠ 0 := by
    rw [ae_iff]
    simpa using hnull
  filter_upwards [hae] with y hy x hx hfx
  obtain ⟨hxZ, hqx, hxy⟩ := hx
  exact hy (hxy ▸ key x hxZ hqx hfx)

end RatFibreAvoid

end GroundTheory.Heights₂.Heights
