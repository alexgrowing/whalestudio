import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XEUpdSZeroLam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherRowsUpdatedScalars
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartAtUpdSReFace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadUpdSKeep
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3

set_option maxHeartbeats 1000000 in

theorem reFace_zero_parts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3), Pins R F cG → Holds R F → (∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) → ∃ kap lam err, Pins ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) cG ∧ Holds ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ ErrEq ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ kap = R.kap ∧ (∀ i t p v, R.EEp3 p ≠ ⊥ → lam i t p v = R.lam3 i t p v) ∧ ∃ (Y' : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Y'.PW Y.PW ∧ HEq Y'.eE Y.eE ∧ HEq Y'.mj.eW Y.mj.eW ∧ HEq Z'.eRR Z.eRR ∧ HEq Z'.jW Z.jW := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Dc Sp Zsc hP hH hZ
  have h1 := pins_updS R F cG (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc) hP (scal_zeroLam R F Dc Sp Zsc hZ hP.char.scal)
  have h2 := prim_updS R F (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) hH.prim (zeroLam_pos R F (Zsc (R.toCx3 F).zs).l6m hH.prim.posScal.2)
    (thmB_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hZ hH.prim.thmB) (thmA_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hH.prim.thmA) (galD_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hH.prim.scalConj)
  have h3 := Holds.mk (reFace_prim (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc) h2)
    (further_face_statements_independent_of_error (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc) (furtherRows_updatedScalars R F (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) hH.aux)) hH.ok hH.sep
  have h4 := reFace_errEq (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc
  have h5 : ∀ i t p v, R.EEp3 p ≠ ⊥ → zeroLam R F (Zsc (R.toCx3 F).zs).l6m i t p v = R.lam3 i t p v :=
    fun i t p v hp => zeroLam_of_ne R F _ (hZ p hp i).1 fun hv => (hZ p hp i).2 v hv
  have h6 := read_updS_keep R F (zeroLam R F (Zsc (R.toCx3 F).zs).l6m) Dc Sp Zsc (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc)
    (XE_updS_zeroLam R F (Zsc (R.toCx3 F).zs).l6m hP.char hH.prim hH.ok hH.sep hZ) X0 Y Z
  refine ⟨R.kap, (zeroLam R F (Zsc (R.toCx3 F).zs).l6m), (reFaceErr (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)) F Dc Sp Zsc), ?_, ?_, ?_, rfl, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h1 :))
  · exact (by with_unfolding_all exact (h3 :))
  · exact (by with_unfolding_all exact (h4 :))
  · exact (by with_unfolding_all exact (h5 :))
  · exact (by with_unfolding_all exact (h6 :))

end GlobalTheory.Mem.R3

end
