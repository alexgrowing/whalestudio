import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorMulOfPublished

noncomputable section

namespace GlobalTheory.ThK.LemF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem locOp_comm (hP : GlobalTheory.FunPr.Hypotheses₂) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (v : Pl F) (g : UA σ X.J) (h : UA σ W.J),
    g ∈ UAt σ X (evFin F v) → h ∈ UAt σ W (evFin F v) → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      locOp v (om (g, 1)) (locOp v (om (1, h)) φ) = locOp v (om (1, h)) (locOp v (om (g, 1)) φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair v g h hg hh φ hφ
  have h1X : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := (UAtSub σ X (evFin F v)).one_mem
  have h1W : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := (UAtSub σ W (evFin F v)).one_mem
  have hm := locOpMul hP
  have e1 := hm F E σ B n d X W M χX χW om r s r' s' hPair v (g, 1) (1, h) hg h1W h1X hh φ hφ
  have e2 := hm F E σ B n d X W M χX χW om r s r' s' hPair v (1, h) (g, 1) h1X hh hg h1W φ hφ
  have hc : ((g, 1) : UA σ X.J × UA σ W.J) * (1, h) = (1, h) * (g, 1) := by
    ext <;> simp
  rw [← e1, ← e2, hc]

end GlobalTheory.ThK.LemF

end
