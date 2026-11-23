import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SplitUnramifiedInduction.PolMix
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Base UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
open scoped Matrix
private theorem alg_closure_of (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (k₀ : IntermediateField ℚ Ω) :
    IsAlgClosure k₀ Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) k₀⟩
private theorem conj_el_ex (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (k₀ : IntermediateField ℚ Ω) [NumberField k₀]
    [IsTotallyReal k₀] : ∃ c : G k₀ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let j : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
  let c : Ω ≃ₐ[ℚ] Ω := τ.restrictNormal Ω
  have hc : ∀ x, algebraMap Ω ℂ (c x) = starRingEnd ℂ (algebraMap Ω ℂ x) := fun x => AlgEquiv.restrictNormal_commutes τ Ω x
  have hfix : ∀ y : k₀, c (y : Ω) = y := fun y => by
    apply (algebraMap Ω ℂ).injective
    rw [hc]
    let φ : k₀ →+* ℂ := (algebraMap Ω ℂ).comp (algebraMap k₀ Ω)
    have hr : ComplexEmbedding.IsReal φ :=
      InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (InfinitePlace.mk φ))
    exact RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 hr) y
  refine ⟨AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun y => hfix y, algebraMap Ω ℂ, fun x => hc x⟩
private theorem pair_two {k : Type} [Field k] (A : Matrix (Fin 2) (Fin 2) k) :
    Aᵀ * !![0, 1; -1, 0] * A = A.det • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
private theorem pairing_two {F Ω k : Type} [Field F] [Field Ω] [Algebra F Ω] [Field k] (r : G F Ω →* GL (Fin 2) k) (c : G F Ω) :
    ∃ P, IsPairing c r ((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω)) P := by
  let J : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
  refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
  have h' : s' = c * s * c⁻¹ := h
  have e : r c⁻¹ * r s' = r s * r c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
  have e' : (r c⁻¹).val * (r s').val = (r s).val * (r c⁻¹).val := congrArg Units.val e
  have hp : (r s).valᵀ * J.val * (r s).val = (r s).val.det • J.val := pair_two _
  have hd : (((Matrix.GeneralLinearGroup.det.comp r).comp (resG F F Ω) s : kˣ) : k) = (r s).val.det := rfl
  rw [hd, Units.val_mul, ← Matrix.smul_mul, ← hp]
  simp only [Matrix.mul_assoc, e']
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.polMix_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.PolMix := by
  intro H Ω _ _ _ l _ k₀ _ _ ι x k t r hd hm
  obtain ⟨m, hm0, hm⟩ := hm
  haveI : IsAlgClosure k₀ Ω := alg_closure_of Ω k₀
  have hdet : ∀ s, Matrix.GeneralLinearGroup.det (r s) = cycBar k₀ Ω l s ^ k * x (resQ k₀ s) := fun s =>
    DFunLike.congr_fun hd.det s
  have hcont : Continuous (Matrix.GeneralLinearGroup.det.comp r) :=
    Matrix.GeneralLinearGroup.continuous_det.comp hd.cont
  have halg : Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp r) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s H k₀ Ω l ι).1 _ hcont fun w _ => ?_
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    refine ⟨A, hA, k, m, hm0, fun s _ => ?_⟩
    have hx : x (resQ k₀ s) ^ m = 1 := by
      have := DFunLike.congr_fun hm (resQ k₀ s)
      simpa using this
    rw [MonoidHom.comp_apply, hdet, zpow_neg, zpow_natCast, mul_comm (cycBar k₀ Ω l s ^ k), mul_inv_cancel_right, hx]
  have hsign : Sol.SameSign (Matrix.GeneralLinearGroup.det.comp r) := by
    intro c c' hc hc'
    have hres : ∀ {a : G k₀ Ω}, IsConjEl a → IsConjEl (resQ k₀ a) := fun ⟨j, hj⟩ => ⟨j, hj⟩
    have hcj : IsConj (resQ k₀ c) (resQ k₀ c') := UpperTheory.complex_conjugations_are_conjugate Ω _ _ (hres hc) (hres hc')
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hdet, hdet, UpperTheory.cyclotomic_char_conj_invariant k₀ Ω l c hc, UpperTheory.cyclotomic_char_conj_invariant k₀ Ω l c' hc',
      isConj_iff_eq.1 (MonoidHom.map_isConj x hcj)]
  obtain ⟨c, hc⟩ := conj_el_ex Ω k₀
  obtain ⟨P, hP⟩ := pairing_two r c
  exact ⟨k₀, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, P, halg, hsign, hc, hP⟩
end
