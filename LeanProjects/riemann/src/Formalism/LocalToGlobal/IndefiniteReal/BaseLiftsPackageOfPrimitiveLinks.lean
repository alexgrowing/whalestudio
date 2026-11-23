import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvTieP
import Formalism.LocalToGlobal.IndefiniteReal.ExistsSumOfMemISup
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.UnitaryTwoPackage
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Formalism.LocalToGlobal.IndefiniteReal.IsometricPeriodsOfUnitHypotheses

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Three2

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.WeilFull

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure HkDat3 (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) where

  Hk : Type

  ev : A3.fam3.base3.Ix → Hk → D.what₂.LL

  ev_inj : Function.Injective ev

namespace RealDat3

variable (R : RealDat3 D A3 Ks) (F : Face3 D A3)

def convOf (H : HkDat3 A3) : ConvFace A3.fam3.base3 where
  primes := R.toRealDat.fam_Sb ∧ R.toRealDat.fam_pl_onto ∧ R.in_onto
  symLevel := R.toRealDat.grp_levels F.lv2
  sg0 := A3.A.v0.embedding
  Hk := H.Hk
  ev := H.ev
  ev_inj := H.ev_inj

def PHecke : Prop := (∃ hE, HeckeIntertwiningDefinite A3 (R.toCx3 F) hE) ∧ ∃ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW

def PGUnit : Prop :=
  (∀ (g : G) (x y : (R.toCx3 F).EE), ⟪R.gEx F g x, R.gEx F g y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
    ∀ j (g : G) (x y : (R.toCx3 F).W j), ⟪R.gWx F j g x, R.gWx F j g y⟫_ℂ = ⟪x, y⟫_ℂ

def PGEquiv : Prop := GEquiv3 A3 (R.toCx3 F) (R.gEx F) ∧ LiftGroupEquivariance A3 (R.toCx3 F) (R.gWx F)

def PLevE : Prop :=
  LevType3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.gEx F) false F.P0 F.ψ0 ∧
    LevType3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.gEx F) true F.P1 F.ψ1

def PrincipalLevelBijective : Prop := PrincipalLevelBijectivity A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc)

def PLevW : Prop :=
  LevelTypeOfLifts A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.gWx F) false F.P0 F.ψ0

def PEig0 : Prop := ∃ C0, LiftsEig3 A3 (R.toCx3 F) F.P0 F.ψ0 C0 ∧ LiftsTyp3 A3 C0

def PPos : Prop := 0 < R.kap ∧ ∀ i t p v, 0 < R.lam3 i t p v

def PThmA : Prop :=
  ∀ i t, Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (R.Wp3 i) fun p => R.lam3 i t p A3.A.v0

def PThmB : Prop := Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 R.lamN R.kap

variable {R F}

theorem conv_of (hC : R.WeakCharacterisation F) (H : HkDat3 A3) : IndefConv A3.fam3.base3 R.mu (R.convOf F H) :=
  ⟨⟨hC.base.fam.Sb, hC.base.fam.pl_onto, hC.inert.onto⟩, hC.tup.mu_used, hC.base.grp.levels, rfl⟩

theorem kFormR_of (hM : R.toRealDat.IsModels) : (R.toCx3 F).KFormR := by
  first
    | exact RealDat.kFormR_of (R := R.toRealDat) (F := F.lv2) hM
    | exact RealDat.kFormR_of hM

theorem kFormL_of (hM : R.toRealDat.IsModels) : (R.toCx3 F).KFormL := by
  first
    | exact RealDat.kFormL_of (R := R.toRealDat) (F := F.lv2) hM
    | exact RealDat.kFormL_of hM

theorem jIsoR_of (hM : R.toRealDat.IsModels) : (R.toCx3 F).JIsoR F.cv := by
  first
    | exact RealDat.jIsoR_of (R := R.toRealDat) (F := F.lv2) hM
    | exact RealDat.jIsoR_of hM

theorem jIsoL_of (hM : R.toRealDat.IsModels) : (R.toCx3 F).JIsoL F.cv := by
  first
    | exact RealDat.jIsoL_of (R := R.toRealDat) (F := F.lv2) hM
    | exact RealDat.jIsoL_of hM

theorem kForm_of (h : R.toRealDat.LUnif) (b : Bool) : (R.toCx3 F).KForm b := RealDat.kForm (F := F.lv2) h b

theorem ewNorm (b : Bool) : (R.toCx3 F).EWnorm b := by
  first
    | exact RealDat.ewNorm (R := R.toRealDat) (F := F.lv2) b
    | exact RealDat.ewNorm b

theorem height_change_of_D0 (h : R.IsTup) : (R.toCx3 F).H0 := by
  refine ⟨h.mu_conj, fun w => ⟨h.mu_ne w, fun hne => ?_⟩⟩
  by_contra hw
  exact hne (h.mu_off w hw)

theorem prod_lamN (t : T) (p : A3.fam3.base3.Ix) :
    ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p = ∏ j : Fin D.R.m, R.lam3 j t p A3.A.v0 := by
  symm
  refine Finset.prod_bij (fun (i : Fin D.R.m) _ => (i : ℕ) + 1) ?_ ?_ ?_ ?_
  · intro i _
    have := i.isLt
    simp only [Finset.mem_Icc]
    omega
  · intro a₁ _ a₂ _ h
    exact Fin.ext (by omega)
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    exact ⟨⟨b - 1, by omega⟩, Finset.mem_univ _, Nat.sub_add_cancel (by omega)⟩
  · intro a _
    simp [lamN]

theorem adjoint_smul' {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (c : ℂ) (f : E →ₗ[ℂ] F) :
    LinearMap.adjoint (c • f) = starRingEnd ℂ c • LinearMap.adjoint f := map_smulₛₗ LinearMap.adjoint c f

theorem phase_cancel {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] {c : ℂ} (hc : starRingEnd ℂ c * c = 1) (f : E →ₗ[ℂ] F)
    (w : F) : (c • f) (LinearMap.adjoint (c • f) w) = f (LinearMap.adjoint f w) := by
  simp only [adjoint_smul', LinearMap.smul_apply, map_smul, smul_smul]
  rw [hc, one_smul]

private theorem adjoint_tw_map {s : Bool} {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (f : E →ₗ[ℂ] F) :
    LinearMap.adjoint (Tw.map s f) = Tw.map s (LinearMap.adjoint f) := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [Tw.inner_eq, Tw.inner_eq]
  exact congrArg (cj s) (LinearMap.adjoint_inner_left f (Tw.out y) (Tw.out x))

private theorem tw_map_adjoint_apply_of_eigen {s : Bool} {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (f : E →ₗ[ℂ] F)
    (l : ℝ) (e : Tw s F) (he : f (LinearMap.adjoint f (Tw.out e)) = (l : ℂ) • Tw.out e) :
    Tw.map s f (LinearMap.adjoint (Tw.map s f) e) = (l : ℂ) • e := by
  rw [adjoint_tw_map]
  show Tw.mk s (f (LinearMap.adjoint f (Tw.out e))) = cj s (l : ℂ) • Tw.out e
  rw [he, cj_ofReal]
  rfl

private theorem smul_tw_map_adjoint_apply_of_unit_modulus {s : Bool} {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] {c : ℂ}
    (hc : starRingEnd ℂ c * c = 1) (f : E →ₗ[ℂ] F) (l : ℝ) (e : Tw s F)
    (he : f (LinearMap.adjoint f (Tw.out e)) = (l : ℂ) • Tw.out e) :
    (c • Tw.map s f) (LinearMap.adjoint (c • Tw.map s f) e) = (l : ℂ) • e := by
  rw [phase_cancel hc]
  exact tw_map_adjoint_apply_of_eigen f l e he

theorem tw_smul_cancel {s : Bool} {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] {c : ℂ} (hc : starRingEnd ℂ c * c = 1) (f : E →ₗ[ℂ] F)
    (w : Tw s F) : Tw.map s (c • f) (LinearMap.adjoint (Tw.map s (c • f)) w) = Tw.map s f (LinearMap.adjoint (Tw.map s f) w) := by
  have hmap : Tw.map s (c • f) = cj s c • Tw.map s f := by
    ext x
    show c • f (Tw.out x) = cj s (cj s c) • f (Tw.out x)
    rw [cj_cj]
  have hc' : starRingEnd ℂ (cj s c) * cj s c = 1 := by
    rw [← cj_conj, ← map_mul, hc, map_one]
  rw [hmap]
  exact phase_cancel hc' _ w

set_option maxHeartbeats 1000000 in
theorem thmAop_of (hph : R.phase) (h : R.PThmA) (b : Bool) : (R.toCx3 F).ThmAop b := by
  intro j t p w hw
  have hw1 : Tw.out (s := twAt D.what₂.embLL A3.A.v0) w ∈ R.Wp3 j p := (Submodule.mem_inf.mp hw).1
  have hc : starRingEnd ℂ (R.phs j) * R.phs j = 1 := by
    rw [Complex.conj_mul', (hph j).1]; simp
  refine smul_tw_map_adjoint_apply_of_unit_modulus hc (R.thG j t) (R.lam3 j t p A3.A.v0) w ?_
  exact h j t p _ hw1

set_option maxHeartbeats 1000000 in
theorem thmBop_of (h : R.PThmB) (b : Bool) : (R.toCx3 F).ThmBop b := by
  intro t p e he
  have he1 : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) e ∈ R.EEp3 p := he.1
  have key : Tw.map (twAt D.what₂.embLL A3.A.v0) (R.Th t) (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.Th t)) e) =
      ((R.kap * ∏ j : Fin D.R.m, R.lam3 j t p A3.A.v0 : ℝ) : ℂ) • e := by
    rw [Tw.adjoint_map]
    show Tw.mk _ (R.Th t (LinearMap.adjoint (R.Th t) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) e))) = _
    have h2 := h t p (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) e) he1
    rw [LinearMap.comp_apply] at h2
    rw [h2, Tw.mk_smul, cj_ofReal, prod_lamN]
    rfl
  exact key

end RealDat3

structure PrimRows3 (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop where
  heckeR : ∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint
  heckeL : ∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint
  hecke : R.PHecke F
  gUnit : R.PGUnit F
  gEquiv : R.PGEquiv F
  block : (R.toCx3 F).zs.InBlock
  rowTest : Formalism.IndefR.Rat.RowTest (R.toCx3 F)
  liftTest : Formalism.IndefR.Rat.LiftTest (R.toCx3 F)
  liftTestB : Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false
  liftOnto : ∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW
  pos : ∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos
  posScal : R.PPos
  levE : R.PLevE F
  h2P : R.PrincipalLevelBijective F
  thmB : R.PThmB
  sumE : ∀ b, (R.toCx3 F).PartsE b
  unif : R.toRealDat.LUnif
  mLat : (R.toCx3 F).MLat false
  levW : R.PLevW F
  thmA : R.PThmA
  sumW : (R.toCx3 F).PartsW false
  scalConj : (R.toCx3 F).GalD F.cr false
  dimParts : (R.toCx3 F).DimParts false

structure UnusedChoiceStatements (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop where
  ex : R.toRealDat.ExAt
  conj : R.toRealDat.PConj
  levelW : R.toRealDat.LLevelW F.lv2
  integral : R.toRealDat.LIntegral

structure CovolumeOntoIsometryConditions (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (H : HkDat3 A3) (C CH : ℝ) : Prop extends PrimRows3 R F where
  w1 : ∀ w, (R.toCx3 F).W1 F.cr (R.num F C CH) w → w ∈ R.twPl
  covol : ((R.toCx3 F).data F.cr false).L3 (R.num F C CH)
  onto : ((R.toCx3 F).data F.cr false).ON (R.num F C CH)
  lamLow : ((R.toCx3 F).data F.cr true).L6 (R.num F C CH)
  seeIso : (R.toCx3 F).SEEIso sEE
  miStar : (R.toCx3 F).MIstar2 (F.eV (R.toCx3 F).zs) sEE
  fun0 : ((R.toCx3 F).data F.cr false).FUN (R.num F C CH)

theorem complex_data_conditions_base_level_of_primitive_links {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) {R : RealDat3 D A3 Ks} {F : Face3 D A3}
    (hC : R.WeakCharacterisation F) (hP : PrimRows3 R F) :
    ComplexDataConditionsBaseLevel A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F) s (U2.eigensystemChoice A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hP.hecke.2.choose) hP.hecke.1.choose hP.hecke.2.choose (R.gEx F)
      (R.gWx F) where
  kFormR := RealDat3.kFormR_of hC.base.models
  kFormL := RealDat3.kFormL_of hC.base.models
  jIsoR := RealDat3.jIsoR_of hC.base.models
  jIsoL := RealDat3.jIsoL_of hC.base.models
  npTie := ⟨rfl, rfl⟩
  ok := hOk
  sep := hsep
  heckeR := hP.heckeR
  heckeL := hP.heckeL
  thetaR := hP.hecke.1.choose_spec
  thetaL := hP.hecke.2.choose_spec
  gUnit := hP.gUnit.1
  gEquiv := hP.gEquiv.1
  lev0 := hP.levE.1
  lev1 := hP.levE.2
  h2P := hP.h2P
  gUnitL := hP.gUnit.2
  gEquivL := hP.gEquiv.2
  lower_level_lift_type := hP.levW
  inBlock := hP.block
  rowTest := hP.rowTest
  liftTest := hP.liftTest
  pos := hP.pos
  h0 := RealDat3.height_change_of_D0 hC.tup
  h4pos := ⟨fun _ => hP.posScal.1, hP.posScal.2, RealDat.nP_pos⟩
  thmBop := RealDat3.thmBop_of hP.thmB
  partsE := hP.sumE
  kForm := RealDat3.kForm_of hP.unif false
  mLat := hP.mLat
  ewNorm := RealDat3.ewNorm false
  thmAop := RealDat3.thmAop_of hC.phase hP.thmA false
  partsW := hP.sumW
  base_lift_test := hP.liftTestB
  galD := hP.scalConj
  dimParts := hP.dimParts
  eig0 := (U2.unitary_two_package A3 (R.toCx3 F) s F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc hP.hecke.2.choose (R.gWx F) hOk
    (RealDat3.kFormR_of hC.base.models) (RealDat3.kFormL_of hC.base.models) (RealDat3.jIsoR_of hC.base.models)
    (RealDat3.jIsoL_of hC.base.models) hP.rowTest hP.liftTest hP.heckeL hP.hecke.2.choose_spec hP.gUnit.2 hP.gEquiv.2 hP.levW
    hP.sumW (hP.liftOnto _ hP.hecke.2.choose_spec)).1
  typ0 := (U2.unitary_two_package A3 (R.toCx3 F) s F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc hP.hecke.2.choose (R.gWx F) hOk
    (RealDat3.kFormR_of hC.base.models) (RealDat3.kFormL_of hC.base.models) (RealDat3.jIsoR_of hC.base.models)
    (RealDat3.jIsoL_of hC.base.models) hP.rowTest hP.liftTest hP.heckeL hP.hecke.2.choose_spec hP.gUnit.2 hP.gEquiv.2 hP.levW
    hP.sumW (hP.liftOnto _ hP.hecke.2.choose_spec)).2

theorem base_lifts_package_of_primitive_links {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) {R : RealDat3 D A3 Ks} {F : Face3 D A3}
    {sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH} {H : HkDat3 A3} {C CH : ℝ} (hC : R.WeakCharacterisation F)
    (hP : CovolumeOntoIsometryConditions R F sEE H C CH) :
    PrimitiveStatementsBaseLiftsOnly A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F) s (U2.eigensystemChoice A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hP.hecke.2.choose) (F.eV (R.toCx3 F).zs) sEE C CH hP.hecke.1.choose
      hP.hecke.2.choose (R.gEx F) (R.gWx F) (R.convOf F H) where
  kFormR := RealDat3.kFormR_of hC.base.models
  kFormL := RealDat3.kFormL_of hC.base.models
  jIsoR := RealDat3.jIsoR_of hC.base.models
  jIsoL := RealDat3.jIsoL_of hC.base.models
  npTie := ⟨rfl, rfl⟩
  ok := hOk
  sep := hsep
  heckeR := hP.heckeR
  heckeL := hP.heckeL
  thetaR := hP.hecke.1.choose_spec
  thetaL := hP.hecke.2.choose_spec
  gUnit := hP.gUnit.1
  gEquiv := hP.gEquiv.1
  lev0 := hP.levE.1
  lev1 := hP.levE.2
  h2P := hP.h2P
  gUnitL := hP.gUnit.2
  gEquivL := hP.gEquiv.2
  lower_level_lift_type := hP.levW
  inBlock := hP.block
  rowTest := hP.rowTest
  liftTest := hP.liftTest
  eig0 := (U2.unitary_two_package A3 (R.toCx3 F) s F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc hP.hecke.2.choose (R.gWx F) hOk
    (RealDat3.kFormR_of hC.base.models) (RealDat3.kFormL_of hC.base.models) (RealDat3.jIsoR_of hC.base.models)
    (RealDat3.jIsoL_of hC.base.models) hP.rowTest hP.liftTest hP.heckeL hP.hecke.2.choose_spec hP.gUnit.2 hP.gEquiv.2 hP.levW
    hP.sumW (hP.liftOnto _ hP.hecke.2.choose_spec)).1
  typ0 := (U2.unitary_two_package A3 (R.toCx3 F) s F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc hP.hecke.2.choose (R.gWx F) hOk
    (RealDat3.kFormR_of hC.base.models) (RealDat3.kFormL_of hC.base.models) (RealDat3.jIsoR_of hC.base.models)
    (RealDat3.jIsoL_of hC.base.models) hP.rowTest hP.liftTest hP.heckeL hP.hecke.2.choose_spec hP.gUnit.2 hP.gEquiv.2 hP.levW
    hP.sumW (hP.liftOnto _ hP.hecke.2.choose_spec)).2
  pos := hP.pos
  h0 := RealDat3.height_change_of_D0 hC.tup
  w1 := hP.w1
  h4pos := ⟨fun _ => hP.posScal.1, hP.posScal.2, RealDat.nP_pos⟩
  thmBop := RealDat3.thmBop_of hP.thmB
  partsE := hP.sumE
  kForm := RealDat3.kForm_of hP.unif false
  mLat := hP.mLat
  ewNorm := RealDat3.ewNorm false
  thmAop := RealDat3.thmAop_of hC.phase hP.thmA false
  partsW := hP.sumW
  base_lift_test := hP.liftTestB
  galD := hP.scalConj
  dimParts := hP.dimParts
  l3 := hP.covol
  on := hP.onto
  l6 := hP.lamLow
  evTie := EvTie.evTie_of_ok hOk F _
  seeIso := hP.seeIso
  miStar := hP.miStar
  conv := RealDat3.conv_of hC H
  heckeRB := heckeRB_of (complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP.toPrimRows3) _
  heckeWB := heckeWB_of (complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP.toPrimRows3) _
  heckeRC := heckeRC_of (complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP.toPrimRows3) _
  fun0 := hP.fun0

end Three2

section Geo3

open Formalism.L2.Geo Formalism.MainNotions Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Gm : DV.Geo D.what₂.LL} {Lv : Type} {Fam : ShimFam D Gm Lv} (Kp : FormsKPkg Fam) [Algebra Kp.fs.KO D.what₂.LL]

structure GeometricWeakCharacterisation (R : RealDat3 D A3 Kp.fs.KO) (F : Face3 D A3) (e : G ≃* Kp.Hb) : Prop where
  char : R.WeakCharacterisation F
  geo : GeoTied Kp R.toRealDat e
  conj : R.toRealDat.PConj

end Geo3

end Formalism.IndefR.Links

end
