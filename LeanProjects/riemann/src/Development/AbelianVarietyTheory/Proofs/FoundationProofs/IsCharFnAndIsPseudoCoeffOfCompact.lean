import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace
open scoped ComplexConjugate ContDiff InnerProductSpace

noncomputable section

namespace GlobalTheory.Orb

variable {H : Type} [Group H] [TopologicalSpace H]
  {V U : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] {D : H →* (V →L[ℂ] V)} {π : H →* (U →L[ℂ] U)}

theorem continuous_trace_rep (hD : IsUnitaryRep D) :
    Continuous fun g => LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V) := by
  simp only [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ V)]
  exact continuous_finset_sum _ fun i _ => continuous_const.inner (hD.continuous_apply _)

omit [TopologicalSpace H] in

theorem trace_rep_conj (x s : H) :
    LinearMap.trace ℂ V (D (x⁻¹ * s * x) : V →ₗ[ℂ] V) = LinearMap.trace ℂ V (D s : V →ₗ[ℂ] V) := by
  have h := Representation.char_conj (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp D) s x⁻¹
  rwa [inv_inv] at h

variable [MeasurableSpace H] [BorelSpace H] {μ : Measure H}

theorem hasTrace_repOp_of_finiteDimensional [CompleteSpace V] [IsFiniteMeasureOnCompacts μ] (hD : IsUnitaryRep D)
    {f : H → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    HasTrace (repOp D μ f) (∫ g, f g * LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V) ∂μ) := by
  refine ⟨isTraceClass_of_finiteDimensional _, ?_⟩
  simp only [trace_eq_linearMap_trace, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ V), Finset.mul_sum,
    ContinuousLinearMap.coe_coe, hD.inner_repOp hf hc]
  exact (integral_finsetSum _ fun i _ => (hf.mul (continuous_const.inner
    (hD.continuous_apply _))).integrable_of_hasCompactSupport hc.mul_right).symm

variable [IsTopologicalGroup H] [CompactSpace H] [μ.IsHaarMeasure]

theorem integral_conj_trace_mul_trace (hD : IsUnitaryRep D) (hi : IsTopIrreducible D) :
    ∫ g, conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) * LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V) ∂μ = μ.real univ := by
  let ρ : Representation ℂ H V := ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp D
  have := hi.1
  have : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (α := Submodule ℂ V) (congrArg Subrepresentation.toSubmodule h)⟩
  have : ρ.IsIrreducible := ⟨fun S => (hi.2 S.toSubmodule ⟨S.toSubmodule.closed_of_finiteDimensional,
    fun g v hv => S.apply_mem_toSubmodule g hv⟩).imp (fun h => Subrepresentation.toSubmodule_injective h)
      fun h => Subrepresentation.toSubmodule_injective h⟩
  have h := integral_conj_character_mul_character_self (haarProb H) ρ hD.continuous_apply hD.norm_apply
  conv_lhs => rw [eq_smul_haarProb μ]
  rw [integral_smul_measure]
  exact (congrArg _ h).trans (by simp [Measure.real])

theorem integral_inner_smul_eq_zero [CompleteSpace V] [CompleteSpace U] (hD : IsUnitaryRep D) (hi : IsTopIrreducible D)
    (hπ : IsUnitaryRep π) (hi' : IsTopIrreducible π) (hne : ¬ IsUnitEquiv π D) (e x : V) (v : U) :
    ∫ g, ⟪D g e, x⟫_ℂ • π g v ∂μ = 0 := by
  have hI : ∀ z : V, Integrable (fun g => ⟪D g e, z⟫_ℂ • π g v) μ := fun z =>
    integrable_of_continuous_of_compactSpace μ
      (((hD.continuous_apply e).inner continuous_const).smul (hπ.continuous_apply v))
  let T : V →ₗ[ℂ] U :=
    { toFun := fun x => ∫ g, ⟪D g e, x⟫_ℂ • π g v ∂μ
      map_add' := fun x y => by
        rw [← integral_add (hI x) (hI y)]
        simp [add_smul]
      map_smul' := fun c x => by simp [mul_smul, integral_smul] }
  have hT : LinearMap.toContinuousLinearMap T ∈ AutMult.homIn D π ⊤ := AutMult.mem_homIn_top.2 fun g x => by
    change ∫ k, ⟪D k e, D g x⟫_ℂ • π k v ∂μ = π g (∫ k, ⟪D k e, x⟫_ℂ • π k v ∂μ)
    rw [← integral_mul_left_eq_self _ g, ← (π g).integral_comp_comm (hI x)]
    simp only [map_mul, ContinuousLinearMap.mul_apply, AutMult.inner_map_map hD, map_smul]
  have h0 : AutMult.homIn D π ⊤ = ⊥ := AutMult.multIn_eq_zero_iff.1 (by_contra fun h =>
    hne (AutMult.uEquiv_of_multIn_ne_zero ⟨‹_›, hD, hi⟩ ⟨‹_›, hπ, hi'⟩ h).symm)
  rw [h0, Submodule.mem_bot] at hT
  exact DFunLike.congr_fun hT x

theorem repOp_conj_trace_eq_zero [CompleteSpace V] [CompleteSpace U] (hD : IsUnitaryRep D) (hi : IsTopIrreducible D)
    (hπ : IsUnitaryRep π) (hi' : IsTopIrreducible π) (hne : ¬ IsUnitEquiv π D) (c : ℂ) :
    repOp π μ (fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / c) = 0 := by
  ext v
  rw [hπ.repOp_apply (f := fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / c)
    ((Complex.continuous_conj.comp (continuous_trace_rep hD)).div_const c)
    (HasCompactSupport.of_compactSpace _)]
  simp only [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ V), map_sum, inner_conj_symm, div_eq_inv_mul,
    mul_smul, integral_smul, Finset.sum_smul, ContinuousLinearMap.coe_coe]
  have hI : ∀ e : V, Integrable (fun g => ⟪D g e, e⟫_ℂ • π g v) μ := fun e =>
    integrable_of_continuous_of_compactSpace μ
      (((hD.continuous_apply e).inner continuous_const).smul (hπ.continuous_apply v))
  rw [integral_finsetSum _ fun i _ => hI _]
  simp [integral_inner_smul_eq_zero hD hi hπ hi' hne]

theorem isCharFn_and_isPseudoCoeff_of_compact [T2Space H] [SecondCountableTopology H] [CompleteSpace V]
    {n : Type} [Fintype n] [DecidableEq n] {ι : H →* Matrix n n ℂ} (hι : Continuous (matCoord ι))
    (hD : IsUnitaryRep D) (hi : IsTopIrreducible D)
    (hχ : (fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V))) ∈ CcMat ι) :
    IsCharFn ι μ D (fun g => LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) ∧
      IsPseudoCoeff ι μ D fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / μ.real univ := by
  have h0 : (μ.real univ : ℂ) ≠ 0 := by
    exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨(isOpen_univ.measure_pos μ univ_nonempty).ne', measure_ne_top _ _⟩
  have hc := continuous_trace_rep hD
  have hf : Continuous fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / μ.real univ :=
    (Complex.continuous_conj.comp hc).div_const _
  have hΘ : IsCharFn ι μ D (fun g => LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) :=
    ⟨hc.locallyIntegrable, fun s _ => hc.continuousAt, fun f hf' =>
      hasTrace_repOp_of_finiteDimensional hD (continuous_of_mem_ccSmooth hι hf') hf'.1⟩
  refine ⟨hΘ, ?_, ?_, fun U _ _ _ π hπ hirr _ hne => ?_, fun s _ hT => absurd (isClosed_cent s).isCompact hT,
    _, hΘ, fun s _ hT dt _ _ => ?_⟩
  · simp only [div_eq_inv_mul]
    exact (CcMat ι).smul_mem (μ.real univ : ℂ)⁻¹ hχ
  · convert hasTrace_repOp_of_finiteDimensional (μ := μ) hD hf (HasCompactSupport.of_compactSpace _) using 1
    simp only [div_mul_eq_mul_div, integral_div, integral_conj_trace_mul_trace hD hi, div_self h0]
  · rw [repOp_conj_trace_eq_zero hD hi hπ hirr hne]
    exact ⟨isTraceClass_zero, trace_zero⟩
  · haveI : CompactSpace (cent s) := isCompact_iff_compactSpace.1 hT
    convert hasOrbInt_of_finite (dh := μ) (dt := dt)
      (f := fun g => conj (LinearMap.trace ℂ V (D g : V →ₗ[ℂ] V)) / μ.real univ)
      ((hf.comp (f := fun x => x⁻¹ * s * x) (by fun_prop)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) using 2
    simp only [trace_rep_conj, integral_const, Complex.real_smul]
    field_simp

example [MeasurableSpace Circle] [BorelSpace Circle] (ν : Measure Circle) [ν.IsHaarMeasure] :
    IsPseudoCoeff circleMat ν (charRep (MonoidHom.id Circle)) fun z =>
      conj (LinearMap.trace ℂ ℂ (charRep (MonoidHom.id Circle) z : ℂ →ₗ[ℂ] ℂ)) / ν.real univ := by
  have e : ∀ z i j, matCoord circleMat z i j = z := fun z i j => by
    fin_cases i; fin_cases j; simp [matCoord, circleMat]; rfl
  have h := AutMult.isIrrUnitary_charRep (χ := MonoidHom.id Circle) continuous_id
  refine (isCharFn_and_isPseudoCoeff_of_compact
    (continuous_pi fun i => continuous_pi fun j => by simp only [e]; exact continuous_subtype_val) h.unitary h.irred
    ⟨HasCompactSupport.of_compactSpace _, fun y => conj (y 0 0), ?_, fun z => by simp [e, charRep]⟩).2
  exact Complex.conjCLE.contDiff.comp (by fun_prop)

end GlobalTheory.Orb
