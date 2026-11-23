import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFirstApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
import Development.AutomorphicArithmetic.LocalEmbeddings.SplitLin
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

theorem _root_.GlobalTheory.T.local_functional_triple_translate_equivariant : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v) (ι₀ : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a') ) (Fv F v) → ℂ)), G.M'.IsLinBar B.ψ t 1 1 ι₀ →
  ∀ h ∈ UAt σ G.W (evFin F v), ∀ h₀ : GL (Fin (a + a')) (Fv F v), (mat h).map (piW t) = h₀.1 → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
    (∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁) ∧ ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ →
      ι₀ φ₁ = ((chrW X.α t (GlobalTheory.SplitFlip.gdet h₀) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h₀) ((a' : ℂ) / 2)) •
        fun Y => ι₀ φ (Y * h₀.1) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v _ t ι₀ hι h hh h₀ hh₀ φ hφ
  obtain ⟨S, hS, -⟩ := GlobalTheory.WeilTransferW.local_weil_operator_second_space hP F E σ B a a' G X om om' hT v h hh
  refine ⟨⟨S φ, hS φ hφ⟩, fun φ₁ hφ₁ hA => ?_⟩
  have hone : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := fun u _ => by simp [mat]
  have e := GlobalTheory.SplitLin.OppLagr.act_linBar hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' G.q (a' - G.q)
    (a + a' - (G.p + G.q)) (G.p + G.q) (GlobalTheory.ThK.Inhab.pairV' hT) v t 1 1 ι₀ hι 1 hone h hh φ hφ φ₁ hφ₁ hA
  have hl : GlobalTheory.KSplit.locMat t 1 h = h₀ := Units.ext (by rw [GlobalTheory.KSplit.locMat_val, hh₀]; simp)
  rw [e, hl, map_one]
  funext Y
  simp [GlobalTheory.SplitFlip.omB]

end
