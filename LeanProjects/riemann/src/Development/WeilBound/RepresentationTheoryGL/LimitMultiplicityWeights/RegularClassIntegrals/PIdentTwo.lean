import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel

theorem identTwo : IdentTwo := by
  intro H _ _ _ _ _ _ _ _ n ι hc s B hB μ _ _ dt _ _ φ hφc hφs hO h
  have : μ.IsInvInvariant := GlobalTheory.SqIntRep.isInvInvariant_of_unimodular μ
  set f : H → ℂ := fun z => φ (z⁻¹ * s * z) * (B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) : ℂ) with hfdef
  set F : H → ℂ := fun k => φ (k * (h⁻¹ * s * h) * k⁻¹) *
    (B (matCoord ι (k * (h⁻¹ * s * h) * k⁻¹), matCoord ι k) : ℂ) with hFdef
  have hsub : ∫ k, F k ∂μ = ∫ z, f z ∂μ := by
    have h1 := integral_mul_right_eq_self (μ := μ) (fun k => F k) h
    have h2 := integral_inv_eq_self (fun k => F (k * h)) μ
    rw [← h1, ← h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have e : z⁻¹ * h * (h⁻¹ * s * h) * (z⁻¹ * h)⁻¹ = z⁻¹ * s * z := by group
    simp only [hFdef, hfdef, e]
  have hBc : Continuous B := hB.smooth.continuous
  have hfc : Continuous f := by
    have h1 : Continuous fun z : H => z⁻¹ * s * z := by fun_prop
    have h2 : Continuous fun z : H => z⁻¹ * h := by fun_prop
    exact (hφc.comp h1).mul (Complex.continuous_ofReal.comp (hBc.comp ((hc.comp h1).prodMk (hc.comp h2))))
  obtain ⟨K, hK, hKp⟩ := hB.proper (tsupport φ) {h⁻¹ * s * h} hφs isCompact_singleton
  have hfs : HasCompactSupport f := by
    refine HasCompactSupport.intro (hK.image (f := fun k => h * k⁻¹) (by fun_prop)) fun z hz => ?_
    by_contra hne
    apply hz
    have hne' : φ (z⁻¹ * s * z) * (B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) : ℂ) ≠ 0 := hne
    have m1 : z⁻¹ * s * z ∈ tsupport φ := subset_tsupport _ (left_ne_zero_of_mul hne')
    have m2 : B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) ≠ 0 := by
      intro h0; apply hne'; rw [h0]; simp
    have m3 : (z * (z⁻¹ * h))⁻¹ * s * (z * (z⁻¹ * h)) ∈ ({h⁻¹ * s * h} : Set H) := by
      rw [mul_inv_cancel_left]; exact Set.mem_singleton _
    exact ⟨z⁻¹ * h, hKp z (z⁻¹ * h) m1 m3 m2, by group⟩
  have hfi : Integrable f μ := hfc.integrable_of_hasCompactSupport hfs
  have hW := (weil_integral (T := cent s) (dt := dt) (dh := μ) (isClosed_cent s) hfi).2.2
  set κ : ℂ := ∫ t : cent s, (B (matCoord ι s, matCoord ι ((t : H)⁻¹)) : ℂ) ∂dt with hκ
  have hfib : ∀ x, ∫ t : cent s, f (t * x) ∂dt = φ (x⁻¹ * s * x) * κ := by
    intro x
    obtain ⟨t₀, ht₀, hsh⟩ := hB.shift x h 1 1
    have e1 : ∀ t : cent s, ((t : H) * x)⁻¹ * s * ((t : H) * x) = x⁻¹ * s * x := by
      intro t
      have hts := mem_cent.1 t.2
      have : (t : H)⁻¹ * s * t = s := by rw [mul_assoc, ← hts, inv_mul_cancel_left]
      calc ((t : H) * x)⁻¹ * s * ((t : H) * x) = x⁻¹ * ((t : H)⁻¹ * s * t) * x := by group
        _ = x⁻¹ * s * x := by rw [this]
    have e2 : ∀ t : cent s, f (t * x) = φ (x⁻¹ * s * x) *
        (B (matCoord ι s, matCoord ι ((((⟨t₀, ht₀⟩ : cent s)⁻¹ * t : cent s) : H)⁻¹)) : ℂ) := by
      intro t
      have hs' := hsh (t : H)⁻¹ (inv_mem t.2)
      simp only [inv_one, one_mul, mul_one] at hs'
      have hco : (t : H)⁻¹ * t₀ = ((((⟨t₀, ht₀⟩ : cent s)⁻¹ * t : cent s) : H))⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv]
      simp only [hfdef, e1]
      rw [show ((t : H) * x)⁻¹ * h = x⁻¹ * (t : H)⁻¹ * h by group, hs', hco]
    simp_rw [e2]
    rw [integral_const_mul]
    congr 1
    exact integral_mul_left_eq_self (fun t : cent s => (B (matCoord ι s, matCoord ι ((t : H))⁻¹) : ℂ)) _
  have hfun : (fun x => ∫ t : cent s, f (t * x) ∂dt) = fun x => conjFn s φ x * κ := funext fun x => hfib x
  show ∫ k, F k ∂μ = 0
  rw [hsub, ← hW, hfun]
  have h0 := hO.2
  unfold quotInt descend at h0 ⊢
  show ∫ q, conjFn s φ q.out * κ ∂quotMeas (cent s) dt μ = 0
  rw [integral_mul_const, h0, zero_mul]

end MainStatements.WeightKernel

end
