import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

open GlobalTheory.AutomorphicL2Unitary Set

namespace GlobalTheory.Orb

theorem orbInt_comp_conjEquiv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (dh : Measure H)
    [dh.IsHaarMeasure] [dh.IsMulRightInvariant] (γ : H) (dt : Measure (cent γ)) [dt.IsHaarMeasure]
    [dt.IsMulRightInvariant] (g : H) (f : H → ℂ) :
    orbInt dh γ dt (f ∘ conjEquiv g) = orbInt dh γ dt f := by
  let r : Quot (cent γ) ≃ᵐ Quot (cent γ) :=
    { toFun := rmul _ g⁻¹
      invFun := rmul _ g
      left_inv := fun q => by rw [← rmul_mul, inv_mul_cancel, rmul_one]
      right_inv := fun q => by rw [← rmul_mul, mul_inv_cancel, rmul_one]
      measurable_toFun := (measurePreserving_rmul_quotMeas (dt := dt) (dh := dh) (isClosed_cent γ) _).measurable
      measurable_invFun := (measurePreserving_rmul_quotMeas (dt := dt) (dh := dh) (isClosed_cent γ) _).measurable }
  have hr : MeasurePreserving r (quotMeas _ dt dh) (quotMeas _ dt dh) :=
    measurePreserving_rmul_quotMeas (isClosed_cent γ) g⁻¹
  have h3 : descend (cent γ) (conjFn γ (f ∘ conjEquiv g)) = descend (cent γ) (conjFn γ f) ∘ r := funext fun q => by
    conv_rhs => rw [← Quotient.out_eq q]
    refine Eq.trans ?_ ((leftInv_conjFn le_rfl f).descend_mk (q.out * g⁻¹)).symm
    exact congrArg f (show g * _ * g⁻¹ = _ by group)
  rw [orbInt, quotInt, h3]
  exact hr.integral_comp' _

theorem orbitalIntegral_zero_of_derivative_along_conj_curve {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (μ : Measure H) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (s : H) (hs : IsProperOrbit (cent s) s) (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (c : ℝ → H) (hc : Continuous c) (f f' : H → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hf' : Continuous f') (hf'c : HasCompactSupport f') (hd : ∀ (g : H) (u : ℝ), HasDerivAt (fun v : ℝ => f ((c v)⁻¹ * g * c v)) (f' ((c u)⁻¹ * g * c u)) u) : HasOrbInt μ s dt f' 0 := by
  have hO := hs.hasOrbInt (dh := μ) (dt := dt) hf' hf'c
  refine ⟨hO.1, ?_⟩
  change orbInt μ s dt f' = 0
  set ν := quotMeas (cent s) dt μ
  have hcf : ∀ (φ : H → ℂ) (g : H), Continuous φ → Continuous (conjFn s (φ ∘ conjEquiv g)) := fun φ g hφ =>
    hφ.comp ((conjEquiv g).continuous.comp (by fun_prop : Continuous fun x : H => x⁻¹ * s * x))
  have hmeas : ∀ (φ : H → ℂ) (g : H), Continuous φ →
      AEStronglyMeasurable (descend (cent s) (conjFn s (φ ∘ conjEquiv g))) ν := fun φ g hφ =>
    (measurable_descend (leftInv_conjFn le_rfl _) (hcf φ g hφ).measurable).aestronglyMeasurable
  let F : ℝ → Quot (cent s) → ℂ := fun v => descend (cent s) (conjFn s (f ∘ conjEquiv (c v)⁻¹))
  let F' : ℝ → Quot (cent s) → ℂ := fun v => descend (cent s) (conjFn s (f' ∘ conjEquiv (c v)⁻¹))
  have hconst : ∀ v, ∫ q, F v q ∂ν = orbInt μ s dt f := fun v =>
    orbInt_comp_conjEquiv μ s dt (c v)⁻¹ f

  obtain ⟨M, hM⟩ := hf'.bounded_above_of_compact_support hf'c
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  set K : Set H := (fun p : ℝ × H => c p.1 * p.2 * (c p.1)⁻¹) '' (Icc (-1) 1 ×ˢ tsupport f')
  have hK : IsCompact K := (isCompact_Icc.prod hf'c).image (by fun_prop)
  obtain ⟨χ, hχ1, -, hχc, hχI⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  let χC : H → ℂ := fun x => ((χ x : ℝ) : ℂ)
  have hχC : Continuous χC := by fun_prop
  have hχCc : HasCompactSupport χC := HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) hχc Complex.ofReal_zero
  have hχO := hs.hasOrbInt (dh := μ) (dt := dt) hχC hχCc
  let bound : Quot (cent s) → ℝ := fun q => M * ‖descend (cent s) (conjFn s χC) q‖
  have hbound : Integrable bound ν := hχO.1.norm.const_mul M
  have hb : ∀ q, ∀ v ∈ Icc (-1 : ℝ) 1, ‖F' v q‖ ≤ bound q := by
    intro q v hv
    change ‖f' ((c v)⁻¹ * (q.out⁻¹ * s * q.out) * (c v)⁻¹⁻¹)‖ ≤ M * ‖χC (q.out⁻¹ * s * q.out)‖
    rw [inv_inv]
    set y := (c v)⁻¹ * (q.out⁻¹ * s * q.out) * c v
    by_cases hy : y ∈ tsupport f'
    · have hx : q.out⁻¹ * s * q.out ∈ K := ⟨(v, y), ⟨hv, hy⟩, by simp only [y]; group⟩
      have : χC (q.out⁻¹ * s * q.out) = 1 := by simp [χC, hχ1 hx]
      rw [this, norm_one, mul_one]
      exact hM y
    · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
      exact mul_nonneg hM0 (norm_nonneg _)
  have hderiv : ∀ q, ∀ v ∈ Icc (-1 : ℝ) 1, HasDerivAt (fun w => F w q) (F' v q) v := by
    intro q v _
    have e1 : (fun w => F w q) = fun w => f ((c w)⁻¹ * (q.out⁻¹ * s * q.out) * c w) := funext fun w => by
      change f ((c w)⁻¹ * (q.out⁻¹ * s * q.out) * (c w)⁻¹⁻¹) = _
      rw [inv_inv]
    have e2 : F' v q = f' ((c v)⁻¹ * (q.out⁻¹ * s * q.out) * c v) := by
      change f' ((c v)⁻¹ * (q.out⁻¹ * s * q.out) * (c v)⁻¹⁻¹) = _
      rw [inv_inv]
    rw [e1, e2]
    exact hd _ v
  have hF0 : Integrable (F 0) ν :=
    (hs.hasOrbInt (dh := μ) (dt := dt) (f := f ∘ conjEquiv (c 0)⁻¹) (hf.comp (conjEquiv _).continuous)
      (hfc.comp_homeomorph (conjEquiv (c 0)⁻¹).toHomeomorph)).1
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (F := F) (F' := F') (x₀ := (0 : ℝ))
    (s := Icc (-1 : ℝ) 1) (bound := bound) (Icc_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun v => hmeas f _ hf) hF0 (hmeas f' _ hf')
    (ae_of_all _ hb) hbound (ae_of_all _ hderiv)
  have h0 : HasDerivAt (fun v => ∫ q, F v q ∂ν) 0 0 := by
    simp only [hconst]
    exact hasDerivAt_const _ _
  have := h0.unique hmain.2
  rw [← orbInt_comp_conjEquiv μ s dt (c 0)⁻¹ f']
  exact this.symm

theorem hasOrbInt_zero_of_hasDerivAt_conj : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] (μ : Measure H) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (s : H), IsProperOrbit (cent s) s → ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (c : ℝ → H), Continuous c → ∀ (f f' : H → ℂ), Continuous f → HasCompactSupport f → Continuous f' → HasCompactSupport f' → (∀ (g : H) (u : ℝ), HasDerivAt (fun v : ℝ => f ((c v)⁻¹ * g * c v)) (f' ((c u)⁻¹ * g * c u)) u) → HasOrbInt μ s dt f' 0 :=
  fun _ _ _ _ _ _ _ _ _ μ _ _ s hs dt _ _ c hc f f' hf hfc hf' hf'c hd =>
    orbitalIntegral_zero_of_derivative_along_conj_curve μ s hs dt c hc f f' hf hfc hf' hf'c hd

end GlobalTheory.Orb
