import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IteratedHeckeBounds.LemBound

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.JoinReconstruction

open PositivityTheory.KB

theorem lem_Lz {L : Type} [Field L] [NumberField L] {N k : ℕ} (d : Dom L N) {ω' ωb : Form (HS L N) (k + 1)}
    (hω'c : ContinuousOn ω' (Pos L N)) (hωbc : ContinuousOn ωb (Pos L N))
    (hγ : ∀ γ, FInv (ω' - ωb) (emb L N γ)) (hs : ∀ s, FInv (ω' - ωb) (scal L N s))
    (hωbfr : ∀ x, fr ωb x = (d.μ.real d.D)⁻¹ • ∫ y in d.D, fr ω' (ofS L N y) ∂d.μ)
    (hint' : IntegrableOn (fun x => fr ω' (ofS L N x)) d.D d.μ)
    (hsq' : IntegrableOn (fun x => ‖fr ω' (ofS L N x)‖ ^ 2) d.D d.μ) (u : Fin (k + 1) → HS L N) :
    Lz d (fun x => fr (ω' - ωb) x u) := by
  let E : (HS L N [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (k + 1) => HS L N) ℝ u).comp
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ)
  have hE : ∀ F, E F = F u := fun F => rfl
  have hf : IntegrableOn (fun y => fr ω' (ofS L N y) u) d.D d.μ := E.integrable_comp hint'
  set c : ℝ := (d.μ.real d.D)⁻¹ * ∫ y in d.D, fr ω' (ofS L N y) u ∂d.μ with hcdef
  have hc : ∀ x, fr ωb x u = c := by
    intro x
    rw [hωbfr x, ContinuousAlternatingMap.smul_apply, smul_eq_mul, ← hE,
      ← ContinuousLinearMap.integral_comp_comm E hint']
    rfl
  have hfun : ∀ x, fr (ω' - ωb) x u = fr ω' x u - c := by
    intro x
    rw [fr_sub, ContinuousAlternatingMap.sub_apply, hc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fr_comp_cont (hω'c.sub hωbc) u
  · intro γ x
    simp only [fr_inv (hγ γ) x]
  · intro s x
    simp only [fr_inv (hs s) x]
  · simp only [hfun]
    have hg : IntegrableOn (fun x => 2 * ‖E‖ ^ 2 * ‖fr ω' (ofS L N x)‖ ^ 2 + 2 * c ^ 2) d.D d.μ :=
      (hsq'.const_mul (2 * ‖E‖ ^ 2)).add (integrableOn_const d.fin.ne)
    refine Integrable.mono' hg ?_ ?_
    · exact ((continuous_id.sub continuous_const).pow 2).comp_aestronglyMeasurable
        (E.integrable_comp hint').aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have h1 : |E (fr ω' (ofS L N x))| ≤ ‖E‖ * ‖fr ω' (ofS L N x)‖ := by
        rw [← Real.norm_eq_abs]
        exact E.le_opNorm _
      have h2 : (fr ω' (ofS L N x) u) ^ 2 ≤ (‖E‖ * ‖fr ω' (ofS L N x)‖) ^ 2 := by
        rw [← hE, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg (fr ω' (ofS L N x) u + c)]
  · simp only [hfun]
    rw [integral_sub hf (integrableOn_const d.fin.ne), setIntegral_const, smul_eq_mul]
    rcases eq_or_ne (d.μ.real d.D) 0 with h0 | h0
    · have hz : d.μ d.D = 0 := (measureReal_eq_zero_iff d.fin.ne).mp h0
      rw [setIntegral_measure_zero _ hz, h0, zero_mul, sub_zero]
    · rw [hcdef, mul_inv_cancel_left₀ h0, sub_self]

end PositivityTheory.KB.JoinReconstruction

end
