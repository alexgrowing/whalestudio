import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthDecSumLatticeSelfDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocalModelSliceSourceLine
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreFrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem rat_mulVec_sec (q : SplitPt D k) {a b : ℕ} (Q : Matrix (Fin a) (Fin b) D.host.E) (w : Fin b → k) :
    rat Q *ᵥ (fun i => q.sec (w i)) =
      fun i => q.sec ((Q.map (GlobalTheory.SliceModel.prH (GlobalTheory.LocMod.ofSplit q)) *ᵥ w) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact GlobalTheory.SliceModel.ι_mul_left (GlobalTheory.LocMod.ofSplit q) (w j) (incA D (Q i j))

theorem qB_iA_k (p : GlobalTheory.LocMod.Place D k) {ρ : ℕ} (B : BesLev D ρ) :
    B.o.qB.map (GlobalTheory.SliceModel.prH p) * B.o.iA.map (GlobalTheory.SliceModel.prH p) = 0 := by
  rw [← Matrix.map_mul, B.o.qB_iA, Matrix.map_zero _ (map_zero _)]

theorem qB_iB_k (p : GlobalTheory.LocMod.Place D k) {ρ : ℕ} (B : BesLev D ρ) :
    B.o.qB.map (GlobalTheory.SliceModel.prH p) * B.o.iB.map (GlobalTheory.SliceModel.prH p) = 1 := by
  rw [← Matrix.map_mul, B.o.qB_iB, Matrix.map_one _ (map_zero _) (map_one _)]

theorem qB_β {p : GlobalTheory.LocMod.Place D k} {ρ : ℕ} {B : BesLev D ρ} {s : k} {n : Type} [Fintype n] [DecidableEq n]
    {FA : GlobalTheory.LocMod.Frame k B.A.rank n} {C : GlobalTheory.LocMod.Frame k B.V₀.rank (n ⊕ Unit)} (h : p.IsCoreFrame B s FA C) :
    B.o.qB.map (GlobalTheory.SliceModel.prH p) * C.β =
      fromCols 0 (Matrix.of fun i (_ : Unit) => s * GlobalTheory.SliceModel.prH p (B.ζ i)) := by
  rw [GlobalTheory.SliceModel.β_eq h, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, qB_iA_k, qB_iB_k, Matrix.one_mul,
    Matrix.zero_mul, zero_add]

end GlobalTheory.CoreFrameLat
