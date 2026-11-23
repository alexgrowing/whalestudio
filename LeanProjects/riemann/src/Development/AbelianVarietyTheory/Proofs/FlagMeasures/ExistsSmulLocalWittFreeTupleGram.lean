import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtendFreeTupleGramHermitianFrameStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardFrameGramDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmulRatTupEq

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalWittFree

theorem exists_smul_ratTup_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ J y = (gramE σ J (F0 P)).map (inclR (Fv F v)) → ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y := by
  intro F E _ _ _ _ _ σ hcm n J hJ v r P T hP y hy hgram

  obtain ⟨f, hf⟩ := GlobalTheory.T.extend_free_tuple_gram_hermitian_frame F E σ hcm n J hJ v r P T hP y hy hgram

  have hdet := (GlobalTheory.FrameGram.std_frame_gram F E σ hcm n J hJ r P T hP).1

  obtain ⟨g, hg⟩ := GlobalTheory.LocalWittND.exists_smul_ratTup_eq F E σ hcm n J hJ v (r + 1 + r)
    (tupH P) hdet (Fin.append y f) hf
  refine ⟨g, funext fun i => ?_⟩

  have hF : (fun j => tupH P (Fin.castAdd r j)) = F0 P :=
    funext fun j => by simp [tupH, Fin.append_left]
  have h1 : (g • ratTup (F := F) (Fv F v) (tupH P)) (Fin.castAdd r i) =
      (g • ratTup (F := F) (Fv F v) (F0 P)) i := by
    rw [← hF]; rfl
  rw [← h1, hg, Fin.append_left]

end GlobalTheory.LocalWittFree
