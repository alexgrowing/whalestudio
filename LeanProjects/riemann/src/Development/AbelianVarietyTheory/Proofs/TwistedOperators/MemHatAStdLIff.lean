import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeLatticeVacuumTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HformZeroRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TensColRead

variable {D : D7}

def embInf (D : D7) : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem embInf_add_emb (w : AE D) :
    embInf D (Formalism.L2.Theta.infPart D w) + GlobalTheory.TensLatMove.emb D (Formalism.L2.Theta.finPart D w) = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, map_add, map_add, map_add]
    conv_rhs => rw [← ha, ← hb]
    abel
  | tmul a e =>
    have e1 : embInf D (Formalism.L2.Theta.infPart D (a ⊗ₜ[D.host.F] e)) =
        (pairA D.host.F (fstA D.host.F a) 0) ⊗ₜ[D.host.F] e := rfl
    have e2 : GlobalTheory.TensLatMove.emb D (Formalism.L2.Theta.finPart D (a ⊗ₜ[D.host.F] e)) =
        (pairA D.host.F 0 (sndA D.host.F a)) ⊗ₜ[D.host.F] e := rfl
    rw [e1, e2, ← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext (add_zero _) (zero_add _)

theorem emb_finPart (w : AE D) (h : Formalism.L2.Theta.infPart D w = 0) :
    GlobalTheory.TensLatMove.emb D (Formalism.L2.Theta.finPart D w) = w := by
  have := embInf_add_emb w
  rwa [h, map_zero, zero_add] at this

theorem col_iff {S T : HSp D} (L : Lt D.host.E T.rank) (x : WO S T) (k : Fin S.rank) :
    (fun c => Formalism.L2.Theta.finPart D (x c k)) ∈ hatV L ↔
      (fun c => toEAf D (x c k)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L :=
  GlobalTheory.LevSplit.latHat_iff L _

def colHom (S T : HSp D) (k : Fin S.rank) : WO S T →+ (Fin T.rank → AfE D) where
  toFun x := fun c => Formalism.L2.Theta.finPart D (x c k)
  map_zero' := by funext c; simp
  map_add' x y := by funext c; simp

theorem toAf_single_mem (n : ℕ) (k : Fin n) : toAf (Pi.single k (1 : D.host.E)) ∈ hatV (stdL D.host.E n) :=
  AddSubgroup.subset_closure ⟨1, GlobalTheory.TensLatMove.intAf_one, Pi.single k 1,
    Submodule.subset_span ⟨k, rfl⟩, rfl⟩

theorem mem_hatA_stdL_iff : ∀ (D : D7) (S T : HSp D) (L : Lt D.host.E T.rank) (x : WO S T), IsFinPt x → (x ∈ hatA S T (tens (stdL D.host.E S.rank) L) ↔ ∀ k : Fin S.rank, (fun c => toEAf D (x c k)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L) := by
  intro D S T L x hx
  constructor
  · intro hmem k
    rw [← col_iff]
    have hle : hatA S T (tens (stdL D.host.E S.rank) L) ≤ (hatV L).comap (colHom S T k) := by
      rw [hatA, AddSubgroup.closure_le]
      rintro _ ⟨α, hα, y, hy, rfl⟩
      exact AddSubgroup.subset_closure ⟨α, hα, y k, (GlobalTheory.SW.TensLat.mem_tens_stdL L y).1 hy k, rfl⟩
    exact hle hmem
  · intro h
    have hu : ∀ k, (fun c => Formalism.L2.Theta.finPart D (x c k)) ∈ hatV L := fun k => (col_iff L x k).2 (h k)
    have e : x = ∑ k, GlobalTheory.TensLatMove.outer S T (toAf (Pi.single k 1)) (fun c => Formalism.L2.Theta.finPart D (x c k)) := by
      ext c k'
      have hc : Formalism.L2.Theta.infPart D (x c k') = 0 := by
        have := congrFun (congrFun hx c) k'
        simpa using this
      rw [Matrix.sum_apply]
      simp only [GlobalTheory.TensLatMove.outer, Matrix.of_apply, toAf]
      rw [← map_sum, Finset.sum_eq_single k']
      · rw [Pi.single_eq_same, ← Algebra.TensorProduct.one_def, mul_one]
        exact (emb_finPart _ hc).symm
      · intro j _ hj
        rw [Pi.single_eq_of_ne (Ne.symm hj), TensorProduct.tmul_zero, mul_zero]
      · intro h'; exact absurd (Finset.mem_univ k') h'
    rw [e]
    exact sum_mem fun k _ => GlobalTheory.TensLatMove.outer_mem S T _ L _ (toAf_single_mem _ k) _ (hu k)

end GlobalTheory.TensColRead

end
