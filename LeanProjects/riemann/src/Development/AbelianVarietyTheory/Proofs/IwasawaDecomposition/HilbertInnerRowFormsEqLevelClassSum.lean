import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.TopGram

set_option maxHeartbeats 4000000 in

theorem topGram : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (x y : Fin (rDim D A (F.lvl b).P (F.lvl b).ψ t) → D.what₂.LL), (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) * ⟪R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t x), R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A (F.lvl b).P (F.lvl b).ψ t) x y) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hW b t x y
  have hHX := (hW.models.HX t).2.2
  have hjX := hW.models.jX t
  rw [hHX, hjX, hjX]
  have hiso := (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.R t).pres).2.2
  have key : ∀ f f' : A.fam.amb.FR t, Bridge.adInner (Bridge.ratF D.sp.X') (levEnv D.sp.X' R.βX (R.datXt t)).J
      (R.B.R t).pres.y (R.B.jR t f) (R.B.jR t f') = D.what₂.embLL ((A.fam.R t).S.csum f f') := fun f f' => hiso f f'
  have hr : ∀ z, rowForm A (F.lvl b).P (F.lvl b).ψ t z =
      GlobalTheory.Mem.LiftForms.lvlForm (A.fam.R t).S (A.fam.R t).r (A.fam.lvl (F.lvl b).P (F.lvl b).ψ).P
        (A.fam.lvl (F.lvl b).P (F.lvl b).ψ).ψ z := fun z => rfl
  refine (congrArg (fun z => (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) * z) (key (rowForm A (F.lvl b).P (F.lvl b).ψ t x) (rowForm A (F.lvl b).P (F.lvl b).ψ t y))).trans ?_
  rw [hr, hr, GlobalTheory.Mem.LiftForms.csum_lvlForm]
  have hc : (Nat.card ↥(A.fam.lvl (F.lvl b).P (F.lvl b).ψ).P : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos).ne'
  have hn : (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) = ((Nat.card ↥(A.fam.lvl (F.lvl b).P (F.lvl b).ψ).P : ℂ))⁻¹ := by
    rw [Complex.ofReal_inv]
    rfl
  rw [map_mul, map_natCast, hn, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rfl

end GlobalTheory.Mem.TopGram
