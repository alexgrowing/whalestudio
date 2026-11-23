import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem scalConj_base_facts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → 0 < R.kap → (∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.toRealDat.LUnif → R.PLevW F → R.PThmA → (R.toCx3 F).PartsW false → (R.toCx3 F).H5 F.cr false ∧ (R.toCx3 F).RATth F.cr false ∧ (R.toCx3 F).H3W F.cr false ∧ (lv (F.fc (R.toCx3 F).zs) false).Proviso := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F s hOk hsep hC hR hL hH hU hE hblk hrt hlt hltb honto hk hl hun hlev hA hsum
  have kR := RealDat3.kFormR_of (F := F) hC.base.models
  have kL := RealDat3.kFormL_of (F := F) hC.base.models
  have jR := RealDat3.jIsoR_of (F := F) hC.base.models
  have jL := RealDat3.jIsoL_of (F := F) hC.base.models
  have thR := hH.1.choose_spec
  have thL := hH.2.choose_spec
  have st : (R.toCx3 F).zs.Stable := CxData.cutStable (R.toCx3 F) kR kL
    (Formalism.IndefR.CxPass.definite_kernel_stable kR hE.1 thR) (Formalism.IndefR.CxPass.lift_kernel_stable kL hE.2 thL)
    (definite_adjoint_closed hOk hR kR jR) (lift_adjoint_closed hOk hL kL jL)
  have wf := A3.side_well_formed hOk F.P0 F.ψ0 (R.toCx3 F).zs st hblk hsep
  have rz : (R.toCx3 F).RatZ := Formalism.IndefR.Rat.ratZOfTests (R.toCx3 F) (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) kR kL jR jL hrt hlt
  have eig0 := (U2.unitary_two_package A3 (R.toCx3 F) s F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc hH.2.choose (R.gWx F) hOk kR kL jR jL hrt hlt hL thL hU.2 hE.2 hlev hsum (honto _ thL)).1
  have kf := RealDat3.kForm_of (F := F) hun false
  let X' : CxData A3.fam3.amb3 := { R.toCx3 F with lam := fun j t p _ => (R.toCx3 F).lam j t p A3.fam3.base3.v0 }
  have h5 : (R.toCx3 F).H5 F.cr false := (CxData.cutLifts X' (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) false wf
    ⟨fun _ => hk, fun j t p _ => hl j t p, RealDat.nP_pos⟩ kf
    (lift_isometry_of_norms hOk jL ⟨rfl, rfl⟩ false) (lift_coordinates_in_subspaces (R.toCx3 F) false) (lift_coordinates_in_good_part_family (R.toCx3 F) false)
    (Formalism.IndefR.CxPass.lift_rationality_of_equivariance hOk kL jL rz hU.2 hE.2 false)
    (Formalism.IndefR.CxPass.lift_descent_at_lower_type hOk kL jL rz hU.2 hE.2 hlev)
    (Formalism.IndefR.CxPass.upper_level_lift_at_lower_type hOk kL jL hU.2 hE.2 hlev)
    (RealDat3.thmAop_of hC.phase hA false) hsum).1
  exact ⟨h5, Formalism.IndefR.Rat.ratThOfLiftTest (R.toCx3 F) _ false hltb h5 kf (RealDat3.ewNorm false) (RealDat.nP_pos false),
    lift_equivariance_of_primitive F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc kL st hOk thL false,
    proviso_of_lift_eigenvalues A3 (R.toCx3 F) hOk (fun j => hL j A3.A.fam.μ0) F.P0 F.ψ0 eig0⟩

end GlobalTheory
