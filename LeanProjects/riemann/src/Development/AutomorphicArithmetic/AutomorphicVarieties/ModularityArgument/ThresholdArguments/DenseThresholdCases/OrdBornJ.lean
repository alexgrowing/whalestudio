import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.SatOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdFlagJ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdConjUnl
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdExpTor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdConjTor

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
private theorem sat_of_frob {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l n : ℕ}
    [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {ρ : G F Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 F)} {B B' : Multiset ℂˣ}
    (h : Af.FrobEig ι ρ w (Af.algSat n (normV w) B)) (h' : Af.FrobEig ι ρ w (Af.algSat n (normV w) B')) : B = B' := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have e := congrArg Polynomial.roots (((h A hA).2 σ hσ).symm.trans ((h' A hA).2 σ hσ))
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at e
  have hq : (0 : ℝ) < (normV w : ℕ) := Nat.cast_pos.2 (lt_trans one_pos (one_lt_normV w))
  have hc : (((normV w : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq _).ne'
  have e' := Multiset.map_injective (mul_right_injective₀ hc) (a₁ := B.map Units.val) (a₂ := B'.map Units.val)
    (by simpa [Af.algSat, Multiset.map_map] using e)
  exact Multiset.map_injective Units.val_injective e'
theorem UpperTheory.V.Z.Ord.born_j_of_printed_polarization_window :
    _root_.UpperTheory.V.Af.Hypotheses' → ImaginaryQuadraticEtaCharacter.WinOf → BornJ := by
  intro P hO l _ L Ω _ _ _ _ _ _ s n hn V c r ι B Λ J hR hE x h ρ hJ hA hρ hI hc w hl hU
  obtain ⟨π₀, -, hd, ha, he⟩ := hE x h ρ hJ hA hρ hI
  have hl' := (UpperTheory.V.Hi.Pu.l_iff (l := l) w).2 hl
  let v : Vl l L := ⟨w.under (𝓞 (Lp L)), hl'⟩
  have hu : (s.w v.1).under (𝓞 (Lp L)) = v.1 := UpperTheory.V.Hi.Pu.w_under s v.1
  have hsl : ((l : ℕ) : 𝓞 L) ∈ (s.w v.1).asIdeal := (UpperTheory.V.Hi.Pu.l_iff (l := l) _).1 (by rw [hu]; exact hl')
  have hF := _root_.UpperTheory.V.Z.Ord.flagJ_alt P.litN l L Ω s n V c r B Λ J hR x h ρ hJ hA hρ hI v
  obtain ⟨hu1, hu2⟩ := _root_.UpperTheory.V.Z.Ord.conj_unlinked_of_printed_results P L Ω l ι n ρ π₀ hc hd ha (s.w v.1) w hu.symm (s.A v.1) (s.hw v.1) (x.psi v) hF
  obtain ⟨-, hTU, hW⟩ := _root_.UpperTheory.V.Z.Ord.exp_torsion_of_literal_automorphy_n P.litN L Ω l n hn ι (s.A v.1) (s.w v.1) (s.hw v.1) hsl π₀ (x.psi v) (he v)
  have hT : TU π₀ (s.w v.1) := hTU (hu1 hU)
  obtain ⟨t, ht⟩ := hO L n hn π₀
  refine ⟨hu2 (hW t (ht (s.w v.1) hT.1 hT.2)), fun π hπ => ?_⟩
  have e : π₀ = π := GlobalTheory.CuspRep.CuspSub.ext (UpperTheory.V.Af.strongMultOneC L n π₀ π (by
    filter_upwards [ha.2, hπ.2] with u ⟨b, hb, hf⟩ ⟨b', hb', hf'⟩
    obtain rfl := sat_of_frob hf hf'
    exact ⟨b, (CG.hasSat_mk π₀ u b).1 hb, (CG.hasSat_mk π u b).1 hb'⟩))
  exact e ▸ _root_.UpperTheory.V.Z.Ord.conj_torsion_of_printed_results P L n hn π₀ hd (s.w v.1) w hu.symm hT
end
