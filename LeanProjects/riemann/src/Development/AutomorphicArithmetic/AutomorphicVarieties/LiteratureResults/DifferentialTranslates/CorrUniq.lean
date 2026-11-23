import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.EvFacts

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

private theorem mat_cancel {E : Type} [Field E] {a : ℕ} (Ξ : AlgRep E a) (g : GL (Fin a) (Cinf E))
    {v v' : Fin Ξ.d → ℂ} (h : Ξ.mat g *ᵥ v = Ξ.mat g *ᵥ v') : v = v' := by
  have h2 := congrArg (fun z => Ξ.mat g⁻¹ *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec] using h2

private theorem sand_surj {E : Type} [Field E] [NumberField E] {a : ℕ} (g : GL (Fin a) (Cinf E)) (v : HV E a) :
    (2 : ℝ) • sand g (hv (hv.symm ((2 : ℝ)⁻¹ • sand g⁻¹ v))) = v := by
  rw [LinearEquiv.apply_symm_apply, map_smul, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul,
    ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem corrUniq : CorrUniq := by
  intro E _ _ _ a ho U Ξ q
  refine ⟨fun α α' w h h' => ?_, fun α w w' h h' => ?_⟩
  · refine AlternatingMap.ext fun X => (evFacts E a Ξ.d).1 (funext fun g => ?_)
    rw [← infGL_mul_finGL g]
    exact mat_cancel Ξ _ ((h _ _ X).symm.trans (h' _ _ X))
  · refine Subtype.ext (funext fun s => funext fun p => ?_)
    by_cases hp : p ∈ cone E a
    · obtain ⟨g, rfl⟩ := hp
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
      refine ContinuousAlternatingMap.ext fun v => ?_
      have e := (h g x fun i => hv.symm ((2 : ℝ)⁻¹ • sand g⁻¹ (v i))).trans
        (h' g x fun i => hv.symm ((2 : ℝ)⁻¹ • sand g⁻¹ (v i))).symm
      simp only [sand_surj] at e
      exact e
    · rw [(w.2 s).2 p hp, (w'.2 s).2 p hp]

end UpperTheory.V.Lit.Dr
