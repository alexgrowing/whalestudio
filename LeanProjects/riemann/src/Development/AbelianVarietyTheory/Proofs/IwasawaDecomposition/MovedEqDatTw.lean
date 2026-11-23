import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KeepSideBMtVPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideBTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.Mem.R3

theorem dat_ext_heq {X : Stages} {px : PreX X.B.toPre} {I : Col2.ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
    {Wt : Set X.B.places.Pl} {d₁ d₂ : Dat X I hX T Wt} (hXg : d₁.Xg = d₂.Xg) (htr : d₁.tr = d₂.tr)
    (hcore : d₁.core = d₂.core) (hR : HEq d₁.R d₂.R) (hcG : HEq d₁.cG d₂.cG) (hgeo : HEq d₁.geo d₂.geo) : d₁ = d₂ := by
  cases d₁ with
  | @mk Xg tr core alg alg_eq R cG geo pins lev idG good mu fieldValues_mem_fixedField Ks_le =>
  cases d₂ with
  | @mk Xg' tr' core' alg' alg_eq' R' cG' geo' pins' lev' idG' good' mu' le_LL0' Ks_le' =>
  dsimp only at hXg htr hcore hR hcG hgeo
  subst hXg htr hcore
  have halg : alg = alg' := Algebra.algebra_ext _ _ fun y => X.B.embLL.injective ((alg_eq y).trans (alg_eq' y).symm)
  subst halg
  cases eq_of_heq hR
  cases eq_of_heq hcG
  cases eq_of_heq hgeo
  rfl

end GlobalTheory.Mem.R3

namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw

theorem coreJ_coreJ {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) (T : Formalism.L2.Pj.CoreJ a.D) :
    coreJ (a := b) c (coreJ b T) = coreJ c T := (by with_unfolding_all exact ((Eq.refl (coreJ c T)) :))

theorem moved_eq_datTw : ∀ {K : GlobalTheory.Mem.Top.Ctx} {B : GlobalTheory.Mem.Base} {f : GlobalTheory.Mem.Top.Fr B.toPre} {T : GlobalTheory.Mem.Top.TwDat B} {w : GlobalTheory.Mem.Top.Bl.ColW B f T} {P : GlobalTheory.Mem.R3.Rw.Pre2 K w} (x : GlobalTheory.Mem.R3.Rw.St P) (N : TwNew (GlobalTheory.HeightCounting.Up.Dof x)) (m : GlobalTheory.Mem.R3.Rw.Moved (GlobalTheory.HeightCounting.Up.oTw x N)), m.Copy → HEq m.z.R (GlobalTheory.Mem.R3.Tr.real3 (a := x.o.Z) (GlobalTheory.HeightCounting.Up.oTw x N).Z (iK := x.m.z.alg) x.m.z.R) → HEq m.z.cG x.m.z.cG → HEq m.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := x.o.Z) (GlobalTheory.HeightCounting.Up.oTw x N).Z (iK := x.m.z.alg) x.m.z.geo) → m.z = GlobalTheory.HeightCounting.Up.datTw x N := by
  intro K B f T w P x N m hc hR hcG hgeo
  have h1 : x.m.z.core = coreJ (a := P.Z₀) x.o.Z P.z.core := (by with_unfolding_all exact ((eq_of_heq x.copy.core) :))
  have h2 : m.z.core = coreJ (a := P.Z₀) (oTw x N).Z P.z.core := (by with_unfolding_all exact ((eq_of_heq hc.core) :))
  have h3 : coreJ (a := x.o.Z) (oTw x N).Z x.m.z.core = coreJ (a := P.Z₀) (oTw x N).Z P.z.core :=
    (congrArg (coreJ (a := x.o.Z) (oTw x N).Z) h1).trans (coreJ_coreJ _ _ _)
  have h4 : HEq (datTw x N).cG x.m.z.cG := (by with_unfolding_all exact ((HEq.refl x.m.z.cG) :))
  exact dat_ext_heq (d₁ := m.z) (d₂ := datTw x N) ((by with_unfolding_all exact ((m.Xg.trans x.m.Xg.symm) :))) ((by with_unfolding_all exact ((m.tr.trans x.m.tr.symm) :)))
    ((by with_unfolding_all exact ((h2.trans h3.symm) :))) ((by with_unfolding_all exact (hR :))) (hcG.trans h4.symm) ((by with_unfolding_all exact (hgeo :)))

end GlobalTheory.HeightCounting.Up
