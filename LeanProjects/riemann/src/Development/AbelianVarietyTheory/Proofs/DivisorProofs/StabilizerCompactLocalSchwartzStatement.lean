import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCompactLocalSchwartz
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_compact_local_schwartz : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ (v : Pl F), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      IsCompact (KAt K (evFin F v) : Set (UA σ G.V.J)) ∧
        IsLocallyConstant (fun k : KAt K (evFin F v) => locOp v (om (k.1, 1)) φ) := by
  first | exact @GlobalTheory.KFin.kFinite | exact GlobalTheory.KFin.kFinite | (intros; apply GlobalTheory.KFin.kFinite <;> assumption)
