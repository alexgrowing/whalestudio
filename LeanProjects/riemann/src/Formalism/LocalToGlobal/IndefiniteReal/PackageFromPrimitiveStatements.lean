import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartFamily
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
import Formalism.LocalToGlobal.IndefiniteReal.MajAtEqZeroOfMemQpOfNe
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RangeAdjointRat
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatMuOfRowTest
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatThOfLiftTest
import Formalism.LocalToGlobal.IndefiniteReal.FinrankISupLeSum
import Formalism.LocalToGlobal.IndefiniteReal.CutPassage
import Formalism.LocalToGlobal.IndefiniteReal.IsometricPeriodsOfUnitHypotheses

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

section CoreR3

variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {X : CxData A3.fam3.amb3} {s : ℕ}
  {C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop}
  {eV : ∀ t, (Fin ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Df1.nV t) → K) →ₗ[K] A3.fam3.amb3.FR t}
  {sEE : X.EE →ₗ⋆[ℂ] (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH} {C CH : ℝ}
  {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)}
  {gE : Representation ℂ G X.EE} {gW : ∀ j, Representation ℂ G (X.W j)} {cf : ConvFace A3.fam3.base3}

theorem ComplexDataConditionsBaseLevel.stable (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) : X.zs.Stable :=
  CxData.cutStable X hC.kFormR hC.kFormL
    (Formalism.IndefR.CxPass.definite_kernel_stable hC.kFormR hC.gEquiv hC.thetaR)
    (Formalism.IndefR.CxPass.lift_kernel_stable hC.kFormL hC.gEquivL hC.thetaL)
    (definite_adjoint_closed hC.ok hC.heckeR hC.kFormR hC.jIsoR) (lift_adjoint_closed hC.ok hC.heckeL hC.kFormL hC.jIsoL)

theorem ComplexDataConditionsBaseLevel.wf (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) :
    ∀ b, (lv (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).WF := fun b => match b with
  | false => A3.side_well_formed hC.ok P0 ψ0 X.zs hC.stable hC.inBlock hC.sep
  | true => A3.side_well_formed hC.ok P1 ψ1 X.zs hC.stable hC.inBlock hC.sep

theorem ComplexDataConditionsBaseLevel.ratZ (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) : X.RatZ :=
  Formalism.IndefR.Rat.ratZOfTests X (cvOf3 A3 P0 ψ0 P1 ψ1) hC.kFormR hC.kFormL hC.jIsoR hC.jIsoL hC.rowTest hC.liftTest

theorem ComplexDataConditionsBaseLevel.levs (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (b : Bool) :
    X.RatLev (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) b ∧ X.DnLev (cvOf3 A3 P0 ψ0 P1 ψ1) b ∧
      X.UpLev (cvOf3 A3 P0 ψ0 P1 ψ1) b :=
  ⟨Formalism.IndefR.CxPass.rationality_at_level_of_equivariance hC.ok hC.kFormR hC.jIsoR hC.ratZ hC.gUnit hC.gEquiv b,
    Formalism.IndefR.CxPass.descent_of_types hC.ok hC.kFormR hC.jIsoR hC.ratZ hC.gUnit hC.gEquiv hC.h2P hC.lev0 hC.lev1 b,
    Formalism.IndefR.CxPass.upper_level_of_types hC.ok hC.kFormR hC.jIsoR hC.gUnit hC.gEquiv hC.lev0 hC.lev1 b⟩

theorem ComplexDataConditionsBaseLevel.what₂ (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (b : Bool) :
    X.H2 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b ∧ X.H4 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b :=
  cutRows (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) b (hC.wf b) hC.h4pos
    (definite_isometry_of_norms hC.ok hC.jIsoR hC.npTie b) (definite_coordinates_in_subspaces X b) (definite_coordinates_in_good_part X b) (hC.levs b).1 (hC.levs b).2.1 (hC.levs b).2.2
    (hC.thmBop b) (hC.partsE b)

theorem ComplexDataConditionsBaseLevel.ratMu (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (b : Bool) :
    X.RATmu (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b :=
  Formalism.IndefR.Rat.ratMuOfRowTest X (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b hC.rowTest (hC.what₂ b).1

theorem ComplexDataConditionsBaseLevel.partsOrth (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (b : Bool) :
    X.PartsOrth b (fc := faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) := by
  cases b
  · exact fun v _ p q hpq x hx y hy =>
      majAt_eq_zero_of_mem_Qp_of_ne A3 X hC.ok (hC.heckeR A3.A.fam.μ0) hC.stable P0 ψ0 v p q hpq x hx y hy
  · exact fun v _ p q hpq x hx y hy =>
      majAt_eq_zero_of_mem_Qp_of_ne A3 X hC.ok (hC.heckeR A3.A.fam.μ0) hC.stable P1 ψ1 v p q hpq x hx y hy

theorem ComplexDataConditionsBaseLevel.rowHyp (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (b : Bool) :
    X.RowHyp (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b :=
  ⟨hC.wf b, hC.h4pos, (hC.what₂ b).1, hC.ratMu b,
    definite_equivariance_of_primitive P0 ψ0 P1 ψ1 Dc Sp Zsc hC.kFormR hC.stable hC.ok hC.thetaR b, (hC.what₂ b).2, hC.partsOrth b⟩

theorem ComplexDataConditionsBaseLevel.lifts0 (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) :
    X.H5 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false ∧ X.ThmA (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false :=
  CxData.cutLifts X (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) false (hC.wf false) hC.h4pos hC.kForm
    (lift_isometry_of_norms hC.ok hC.jIsoL hC.npTie false) (lift_coordinates_in_subspaces X false) (lift_coordinates_in_good_part_family X false)
    (Formalism.IndefR.CxPass.lift_rationality_of_equivariance hC.ok hC.kFormL hC.jIsoL hC.ratZ hC.gUnitL hC.gEquivL false)
    (Formalism.IndefR.CxPass.lift_descent_at_lower_type hC.ok hC.kFormL hC.jIsoL hC.ratZ hC.gUnitL hC.gEquivL hC.lower_level_lift_type)
    (Formalism.IndefR.CxPass.upper_level_lift_at_lower_type hC.ok hC.kFormL hC.jIsoL hC.gUnitL hC.gEquivL hC.lower_level_lift_type)
    hC.thmAop hC.partsW

theorem ComplexDataConditionsBaseLevel.ratTh (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) :
    X.RATth (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false :=
  Formalism.IndefR.Rat.ratThOfLiftTest X (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false hC.base_lift_test hC.lifts0.1 hC.kForm hC.ewNorm
    (hC.h4pos.2.2 false)

theorem ComplexDataConditionsBaseLevel.liftHyp0 (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) :
    X.LiftHyp (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false :=
  ⟨hC.lifts0.1, hC.ratTh, hC.kForm, hC.ewNorm, hC.lifts0.2, hC.galD,
    lift_equivariance_of_primitive P0 ψ0 P1 ψ1 Dc Sp Zsc hC.kFormL hC.stable hC.ok hC.thetaL false, hC.mLat⟩

theorem ComplexDataConditionsBaseLevel.types0 (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) :
    (lv (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) false).Types :=
  types_of_lift_eigenvalues A3 X hC.ok hC.sep hC.stable P0 ψ0 hC.eig0 hC.typ0

theorem ComplexDataConditionsBaseLevel.proviso0 (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) :
    (lv (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) false).Proviso :=
  proviso_of_lift_eigenvalues A3 X hC.ok (fun j => hC.heckeL j A3.A.fam.μ0) P0 ψ0 hC.eig0

theorem PrimitiveStatementsBaseLiftsOnly.cols (hC : PrimitiveStatementsBaseLiftsOnly A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 eV sEE C CH hE hW gE gW cf) :
    ∃ ζ : (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Dc.Mem → A3.fam3.base3.Tup → K,
      (X.colOf (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).PairingFactorsThroughPeriods ∧
      (X.colOf (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).L1e :=
  X.exists_zeta_pairing_factors_through_periods (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) eV sEE (hC.wf true) hC.h4pos (hC.what₂ true).1
    (hC.ratMu true) hC.jIsoR (hC.levs true).1 (hC.levs true).2.1 (hC.levs true).2.2 (definite_coordinates_in_good_part X true) hC.evTie hC.seeIso
    hC.miStar

def zetaEps (X : CxData A3.fam3.amb3) (cr : Crd A3.fam3.amb3 (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc))
    (sEE : X.EE →ₗ⋆[ℂ] (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH) :
    (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Dc.Mem → A3.fam3.base3.Tup → K :=
  Classical.epsilon fun ζ => (X.colOf cr (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).PairingFactorsThroughPeriods ∧
    (X.colOf cr (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).L1e

def basePackageFullHecke (hC : PrimitiveStatementsWithPassage A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 eV sEE C CH hE hW gE gW cf) :
    IndefPkgR A3.fam3.amb3 (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) cf C CH :=
  X.cxPkgR (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) cf (X.colDef (fun u t => (zetaEps X (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) sEE u t)⁻¹) sEE) C CH
    hC.stable hC.inBlock (hC.rowHyp false) hC.liftHyp0 hC.pos hC.proviso0 hC.types0 hC.h0
    (CxData.cutDims X (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false (hC.wf false) hC.h4pos hC.kForm hC.ewNorm hC.types0
      (hC.what₂ false).1 (hC.ratMu false) (hC.rowHyp false).h3 hC.lifts0.1 hC.ratTh hC.liftHyp0.h3W (hC.partsE false)
      hC.partsW hC.dimParts)
    hC.l3 hC.on (hC.rowHyp true) hC.l6 (Classical.epsilon_spec hC.cols).1 (Classical.epsilon_spec hC.cols).2
    (CxData.cutTuples2 X (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) C CH hC.h0 hC.w1) hC.passage hC.fun0 hC.conv
    (X.heckeB_of (hC.what₂ false).1 hC.kForm hC.ewNorm hC.h4pos hC.heckeRB.some
      hC.heckeWB.some).some
    (X.heckeC_of (hC.what₂ true).1 hC.heckeRC.some).some

end CoreR3

theorem package_from_primitive_statements : PackageFromComplexDataConditions (K := K) (G := G) (Pl0 := Pl0) (I0 := I0) (Ty := Ty) (T := T) (m := m) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC => ⟨basePackageFullHecke hC⟩

end Formalism.IndefR.Cx
