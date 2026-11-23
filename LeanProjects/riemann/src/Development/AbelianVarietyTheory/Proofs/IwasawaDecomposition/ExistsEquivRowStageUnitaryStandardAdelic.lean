import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryGroupsEquivUnitFormGramOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.RowStdGrp

open GlobalTheory.Mem.R3.RowAd GlobalTheory.Mem.R3.RowDeco GlobalTheory.Mem.R3.LiftBrg

theorem ptE_eq_castGL (X : Stages) (h : Bridge.Gf X.toD7.sp.X') :
    ptE X h = castGL (rank_X' X) (Formalism.UG.bc (swapAE X.toD7) h.1) := rfl

def ptHom (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok) :
    Bridge.Gf X.toD7.sp.X' →* Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) where
  toFun h := ⟨ptE X h, ptE_mem_UAd X I hI h⟩
  map_one' := Subtype.ext (by
    show ptE X 1 = 1
    exact mul_left_cancel (a := ptE X 1) (by rw [← ptE_mul, mul_one, mul_one]))
  map_mul' a b := Subtype.ext (ptE_mul X a b)

theorem ptHom_val (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok) (h : Bridge.Gf X.toD7.sp.X') :
    (ptHom X I hI h).1 = ptE X h := rfl

theorem ptHom_injective (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok) :
    Function.Injective (ptHom X I hI) := by
  intro a b hab
  have h1 := congrArg Subtype.val hab
  simp only [ptHom_val, ptE_eq_castGL] at h1
  have h2 := (castGL (rank_X' X)).injective h1
  exact Subtype.ext (StdGroups.bc_injective _ (Algebra.TensorProduct.comm _ _ _).injective h2)

theorem ptHom_surjective (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok) :
    Function.Surjective (ptHom X I hI) := by
  intro x
  have hy : castGL (rank_X' X).symm x.1 ∈ Formalism.L2.DIV.UA X.toD7.sp.cm X.toD7.sp.X'.gram := by
    rw [gram_X'_eq_one X I hI]
    exact castGL_mem_UA_std _ _ _ x.2
  refine ⟨⟨finHom X.toD7.sp.X' (GlobalTheory.StdFrameExist.liftF X.toD7.sp.X' _ hy), _, rfl⟩, Subtype.ext ?_⟩
  rw [ptHom_val, ptE_eq_castGL]
  have e := GlobalTheory.StdFrameExist.finE_liftF X.toD7.sp.X' _ hy
  change castGL (rank_X' X) (finE X.toD7.sp.X' (GlobalTheory.StdFrameExist.liftF X.toD7.sp.X' _ hy)) = _
  rw [e, StdGroups.castGL_symm_castGL']

theorem ptE_equiv : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok →
    ∃ e : Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* Bridge.Gf X.toD7.sp.X',
      ∀ x, RowAd.ptE X (e x) = x.1 := by
  intro X px I hI
  let e0 := MulEquiv.ofBijective (ptHom X I hI) ⟨ptHom_injective X I hI, ptHom_surjective X I hI⟩
  refine ⟨e0.symm, fun x => ?_⟩
  have h := e0.apply_symm_apply x
  exact congrArg Subtype.val h

end GlobalTheory.Mem.R3.RowStdGrp
