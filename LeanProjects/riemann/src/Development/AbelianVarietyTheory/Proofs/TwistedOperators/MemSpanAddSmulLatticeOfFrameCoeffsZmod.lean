import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDat
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BSlotD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

namespace GlobalTheory

open Formalism.L2.SG.Pf.BunEx.Unip Formalism.L2.SG.Pf.unitaryCongruence in
theorem mo_of_coef_mod : ∀ (I : AutInst) (g : ℕ) {r k : ℕ} (e0 f0 : Fin r → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Af I.F), Formalism.L2.SG.Pf.BunEx.Unip.FH I g e0 f0 z0 bw bwd ew → ∀ v ∈ I.Lf, ∀ (Se : Set (Fin r)) (Sb : Set (Fin k)), (∀ a, a ∉ Se → ZMod' I g (hA I (f0 a) v)) → (∀ a, ZMod' I g (hA I (e0 a) v)) → ZMod' I g (hA I z0 v) → (∀ i, i ∉ Sb → ZMod' I g (hA I (bwd i) v)) → (∀ i, ZMod' I g (hA I (bw i) v)) → v ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo I g (e0 '' Se ∪ bw '' Sb) := by
  intro I g r k e0 f0 z0 bw bwd ew h v hv Se Sb hf he hz hbd hb
  have hm := h.mem
  refine mem_Mo_of (exp h v hv) ?_
  classical
  unfold Rc
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · refine Submodule.sum_mem _ fun a _ => ?_
    by_cases ha : a ∈ Se
    · exact span_Mo (smul_span I (Formalism.L2.SG.Pf.unitaryCongruence.hA_int I (hm.1 a).2 hv) (Or.inl ⟨a, ha, rfl⟩))
    · exact mL_Mo I (Zv I g (hf a ha) (hm.1 a).1)
  · exact mL_Mo I (sumZ I g _ _ _ (fun a _ => he a) (fun a _ => (hm.1 a).2))
  · exact mL_Mo I (Zv I g hz hm.2.1)
  · refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ Sb
    · exact span_Mo (smul_span I (Formalism.L2.SG.Pf.unitaryCongruence.hA_int I (hm.2.2 i).2 hv) (Or.inr ⟨i, hi, rfl⟩))
    · exact mL_Mo I (Zv I g (hbd i hi) (hm.2.2 i).1)
  · exact mL_Mo I (sumZ I g _ _ _ (fun i _ => hb i) (fun i _ => (hm.2.2 i).2))

end GlobalTheory
