import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCompactSubgroupTopology
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_compact_subgroup_topology : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F),
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    CompactSpace (KAt K (evFin F v)) ∧ SecondCountableTopology (KAt K (evFin F v)) ∧ T2Space (KAt K (evFin F v)) := by
  first | exact @GlobalTheory.ThK.LemF.QuotInv.KAtCompact.kAt_compact_secondCountable_t2 | exact GlobalTheory.ThK.LemF.QuotInv.KAtCompact.kAt_compact_secondCountable_t2 | (intros; apply GlobalTheory.ThK.LemF.QuotInv.KAtCompact.kAt_compact_secondCountable_t2 <;> assumption)
