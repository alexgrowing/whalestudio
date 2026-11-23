import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InclRMulPtAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertUnitFrame

theorem exists_frame_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ → G.IsGood B → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ (h : w.under (𝓞 F) = v) (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∃ A : GL (Fin a') (w.adicCompletion E), IsFrameAt w G.V'.L A ∧
      (A : Matrix (Fin a') (Fin a') (w.adicCompletion E))ᵀ * G.V'.J.map (algebraMap E (w.adicCompletion E)) *
        (A : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL = 1 := by
  intro F E _ _ _ _ _ σ B a a' G hB hG v w hw h σL hc
  have hX := hG.hV'
  have hd : (G.V'.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hX
  have hJ : IsHermND σ G.V'.Jᵀ :=
    ⟨fun i j => by simp only [Matrix.transpose_apply]; exact hX.herm j i, hd⟩
  have hs : IsSelfDualAt σ G.V'.Jᵀ G.V'.L v :=
    GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B a' G.V' _ _ hB hX v
  obtain ⟨f, hf, ef⟩ := InertChart.exists_frame_antiJ hB.cm hJ hX.lat.fg hX.lat.span_eq_top hw hc hs
  obtain ⟨ϖ, hU⟩ := InertChart.exists_isUnramInv hB.cm hw hc
  obtain ⟨k, hk, ek⟩ := InertChart.exists_congr_antiJ hU (B := 1) (one_mem _) (by exact Formalism.UG.cT_one _)
  refine ⟨f * k⁻¹, (InertChart.isFrameAt_mul hf (inv_mem hk)).1, ?_⟩
  have key : Formalism.UG.cT σL (f * k⁻¹).1 * (G.V'.Jᵀ).map (algebraMap E (w.adicCompletion E)) * (f * k⁻¹).1 = 1 := by
    rw [Units.val_mul, Formalism.UG.cT_mul, Units.val_one, Matrix.mul_one] at *
    calc Formalism.UG.cT σL (k⁻¹).1 * Formalism.UG.cT σL f.1 * (G.V'.Jᵀ).map (algebraMap E (w.adicCompletion E)) * (f.1 * (k⁻¹).1)
        = Formalism.UG.cT σL (k⁻¹).1 * (Formalism.UG.cT σL f.1 * (G.V'.Jᵀ).map (algebraMap E (w.adicCompletion E)) * f.1) * (k⁻¹).1 := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT σL (k⁻¹).1 * Formalism.UG.cT σL k.1 * (k.1 * (k⁻¹).1) := by
          rw [ef, ← ek]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [← Formalism.UG.cT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Formalism.UG.cT_one, Matrix.one_mul]
  have := congrArg Matrix.transpose key
  simpa [Formalism.UG.cT, Matrix.transpose_mul, Matrix.transpose_map, Matrix.mul_assoc] using this

end GlobalTheory.InertUnitFrame
