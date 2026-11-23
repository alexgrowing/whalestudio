import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertInnerRowFormsEqLevelClassSum
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_inner_rowForms_eq_level_class_sum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (x y : Fin (rDim D A (F.lvl b).P (F.lvl b).ψ t) → D.what₂.LL), (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) * ⟪R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t x), R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A (F.lvl b).P (F.lvl b).ψ t) x y) := by
  first | exact @GlobalTheory.Mem.TopGram.topGram | exact GlobalTheory.Mem.TopGram.topGram | (intros; apply GlobalTheory.Mem.TopGram.topGram <;> assumption)
