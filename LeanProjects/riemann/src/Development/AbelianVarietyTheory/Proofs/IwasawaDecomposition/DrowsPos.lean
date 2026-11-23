import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

theorem drows_pos : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → 0 < D.what₂.Drows := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z _ hH _
  have e1 : Module.finrank D.what₂.LL D.div.RR.V = Fintype.card D.div.RR.ι :=
    Module.finrank_eq_card_basis D.div.RR.b
  have e2 : Module.finrank ℂ D.what₂.EE = Fintype.card D.div.RR.ι :=
    Module.finrank_eq_card_basis (Module.Basis.mk D.jEE_basis.1 (le_of_eq D.jEE_basis.2.symm))
  have e3 : Module.finrank ℂ D.what₂.EE = D.what₂.Drows := by
    simpa using Module.finrank_eq_card_basis D.what₂.onb.toBasis
  have h2 : Module.finrank D.what₂.LL D.div.RR.V = ((R.toCx3 F).data F.cr true).D := by
    rw [← Z.eRR.finrank_eq, Module.finrank_fin_fun]
  have h3 : 0 < ((R.toCx3 F).data F.cr true).D := hH.prim.pos true
  omega

end GlobalTheory.Mem.R3
