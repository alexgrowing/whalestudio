import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinTypRepCast
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.IrrationalRotationBk
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.StateChecks

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI

theorem holdsLU_of_holdsU (h : UnitaryCaseCondition) : LowerUnitaryCaseCondition :=
  StepW.trans (p := Pinned) h (r := fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I →
    z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → HoldsL z.R z.F)
    (StepW.of_all fun _ _ _ _ _ _ _ H Z hX Wt z a b c d => HoldsL.of_holds (H Z hX Wt z a b c d))

theorem holdsW_of_holdsU (h : UnitaryCaseCondition) : WeightCaseCondition :=
  ((StepW.of_all fun _ _ _ _ _ _ _ s => s.1 : StepW Start Pinned).trans h).trans
    (StepW.of_all fun _ _ _ _ _ _ _ H Z hX Wt z a b _ c d _ _ _ _ => H Z hX Wt z a b c d)

theorem nonzeroPlacesOverPrimes_of_lifts (h : NonzeroPlacesOverPrimesLifts) : NonzeroPlacesOverPrimes :=
  StepW.trans h (StepW.of_all fun _ _ _ _ _ _ _ H Z hX Wt z a b c d => H Z hX Wt z a b c (HoldsL.of_holds d))

theorem bkLaw_of_bkDef (D : D7) (h : WeightDegreeSizes.BkDef D) : BkLaw D := fun a => (WeightDegreeSizes.buR_iff D).2 ⟨a, h⟩

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Wt : Set B.places.Pl}

theorem sideData_same_stages {Z : w.Lt} (p0 : BaseLevelRowSide (w.D Z)) : p0To p0 Z.S Z.G = p0 := (by with_unfolding_all exact ((rfl : p0 = p0) :))

theorem coreJ_self {C : Cols B} (a : Late B C) (c : Formalism.L2.Pj.CoreJ a.D) : coreJ (a := a) a c = c := (by with_unfolding_all exact ((rfl : c = c) :))

theorem realData_heq_self {C : Cols B} (a : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
   {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} (R : RealDat3 a.D A Ks) :
   HEq R (real3 (a := a) a R) := by
  have eY : R.ioY = ((by with_unfolding_all exact ((@RealDat.ioY a.D G _ _ Pl0 T (famM a A.A) Ks _ _ (alg a iK) (real a R.toRealDat)) :)) : type_of% R.ioY) :=
    eq_of_heq ((by with_unfolding_all exact ((real_ioY (a := a) a R.toRealDat) :)))
  have eX : R.ioX = ((by with_unfolding_all exact ((@RealDat.ioX a.D G _ _ Pl0 T (famM a A.A) Ks _ _ (alg a iK) (real a R.toRealDat)) :)) : type_of% R.ioX) :=
    eq_of_heq ((by with_unfolding_all exact ((real_ioX (a := a) a R.toRealDat) :)))
  exact (by with_unfolding_all exact ((heq_of_eq (congrArg₂ (fun (y : type_of% R.ioY) (x : type_of% R.ioX) =>
    ({ R with toRealDat := { R.toRealDat with ioY := y, ioX := x } } : RealDat3 a.D A Ks)) eY eX)) :))

theorem rowsSame_refl {Z : w.Lt} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) : RowsSame t t where
  Xg := rfl
  tr := rfl
  core := (by with_unfolding_all exact ((HEq.refl t.r.z.core) :))
  R := (by with_unfolding_all exact ((realData_heq_self Z (iK := t.r.z.alg) t.r.z.R) :))
  cG := HEq.rfl
  tup := HEq.rfl
  tupT := HEq.rfl
  PY := HEq.rfl
  PW := HEq.rfl
  rep := HEq.rfl
  jE := HEq.rfl
  heq_eigen_embedding_zero := HEq.rfl
  eE := HEq.rfl
  jA := HEq.rfl
  jA0 := HEq.rfl
  eMt := HEq.rfl
  eW := HEq.rfl
  jW := HEq.rfl
  eRR := HEq.rfl
  eRR0 := HEq.rfl

section Types

variable {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 T₀ : Type}
  {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] {A : FamIn a.D.what₂.LL G Pl0 T₀ a.D.R.m}
  {R : RealDat a.D A Ks} (F : Face a.D A) (y : Hd R) (y' : HdB b R) (E : Hs)

abbrev chB : ChainReal b.D := letI := alg b iK; y'.C (face b F)

abbrev lfB : LiftReal b.D (chB b F y') := letI := alg b iK; y'.L (face b F)

theorem ty_chain (j : ℕ) : (E.T →ₗ[ℂ] (chB b F y').Amb j) = (E.T →ₗ[ℂ] (y.C F).Amb j) := (by with_unfolding_all exact ((rfl : (E.T →ₗ[ℂ] (y.C F).Amb j) = _) :))

theorem ty_top : (E.T →ₗ[ℂ] (chB b F y').AmbX) = (E.T →ₗ[ℂ] (y.C F).AmbX) := (by with_unfolding_all exact ((rfl : (E.T →ₗ[ℂ] (y.C F).AmbX) = _) :))

theorem ty_lift (E : ℕ → Hs) : (∀ i : Fin b.D.R.m, (E i).T →ₗ[ℂ] (GA b.D ((lfB b F y').V i) → (lfB b F y').TauV i)) =
    (∀ i : Fin a.D.R.m, (E i).T →ₗ[ℂ] (GA a.D ((y.L F).V i) → (y.L F).TauV i)) := (by with_unfolding_all exact ((rfl : (∀ i : Fin a.D.R.m, (E i).T →ₗ[ℂ] (GA a.D ((y.L F).V i) → (y.L F).TauV i)) = _) :))

theorem ty_model (E : ℕ → Hs) : (letI := alg b iK; ∀ i : Fin b.D.R.m, (E i).T →ₗ[ℂ] ((real b R).HW i (sg0 b.D (famM b A))).H) =
    (∀ i : Fin a.D.R.m, (E i).T →ₗ[ℂ] (R.HW i (sg0 a.D A)).H) := (by with_unfolding_all exact ((rfl : (∀ i : Fin a.D.R.m, (E i).T →ₗ[ℂ] (R.HW i (sg0 a.D A)).H) = _) :))

theorem frames_copy : HEq (rowPsi b y.PY).ψ y.PY.ψ ∧ HEq (fun i => (rowPsi b (y.PW i)).ψ) fun i => (y.PW i).ψ :=
  ⟨(by with_unfolding_all exact ((HEq.refl y.PY.ψ) :)), (by with_unfolding_all exact ((HEq.refl fun i => (y.PW i).ψ) :))⟩

end Types

def copyR {Z : w.Lt} (Z' : w.Lt) {hX : B.fields.Ok} (z : Dat (w.st Z) w.I hX T Wt) :
    @RealDat3 (w.st Z').toD7 _ _ _ _ _ _ (famR (w.st Z') w.I hX (usedOf w.I T Wt) z.Xg z.tr) (coreJ (a := Z) Z' z.core).Q.c.F _ _
      ((by exact @alg B (@ColW.C B f T w) Z Z' (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@ColW.st B f T w Z).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@ColW.st B f T w Z).toD7.R.toFrame (@Host.toHostAx (@ColW.st B f T w Z).toD7.R (@ColW.st B f T w Z).toD7.host))) (@Formalism.HC.HostRaw.instField (@ColW.st B f T w Z).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@ColW.st B f T w Z).toD7.R.toFrame (@Host.toHostAx (@ColW.st B f T w Z).toD7.R (@ColW.st B f T w Z).toD7.host))) (@Formalism.HC.HostRaw.instNF (@ColW.st B f T w Z).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@ColW.st B f T w Z).toD7.R.toFrame (@Host.toHostAx (@ColW.st B f T w Z).toD7.R (@ColW.st B f T w Z).toD7.host))) (Formalism.L2.Pj.instCMHost (@ColW.st B f T w Z).toD7) (@Formalism.L2.Pj.Par.H (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.Core.Q (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@ColW.st B f T w Z).toD7 (@Dat.core (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.Core.Q (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@ColW.st B f T w Z).toD7 (@Dat.core (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.Core.Q (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@ColW.st B f T w Z).toD7 (@Dat.core (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@ColW.st B f T w Z).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@ColW.st B f T w Z).toD7.R.toFrame (@Host.toHostAx (@ColW.st B f T w Z).toD7.R (@ColW.st B f T w Z).toD7.host))) (@Formalism.HC.HostRaw.instField (@ColW.st B f T w Z).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@ColW.st B f T w Z).toD7.R.toFrame (@Host.toHostAx (@ColW.st B f T w Z).toD7.R (@ColW.st B f T w Z).toD7.host))) (@Formalism.HC.HostRaw.instNF (@ColW.st B f T w Z).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@ColW.st B f T w Z).toD7.R.toFrame (@Host.toHostAx (@ColW.st B f T w Z).toD7.R (@ColW.st B f T w Z).toD7.host))) (Formalism.L2.Pj.instCMHost (@ColW.st B f T w Z).toD7) (@Formalism.L2.Pj.Par.H (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.Core.Q (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@ColW.st B f T w Z).toD7 (@Dat.core (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.Core.Q (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@ColW.st B f T w Z).toD7 (@Dat.core (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.Core.Q (@ColW.st B f T w Z).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@ColW.st B f T w Z).toD7 (@Dat.core (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) hX T Wt z)))))) (@Dat.alg (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) hX T Wt z))) :=
  (by with_unfolding_all exact ((real3 (a := Z) Z' (iK := z.alg) z.R) :))

theorem copyR_heq {Z : w.Lt} (Z' : w.Lt) {hX : B.fields.Ok} (z : Dat (w.st Z) w.I hX T Wt) :
    HEq (copyR Z' z) (real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := z.alg) z.R) := (by with_unfolding_all exact ((HEq.refl (copyR Z' z)) :))

theorem exists_bkLaw (D : D7) : ∃ b, BkLaw (GlobalTheory.Survey.IrrationalRotationBlocks.withBk D b) := by
  by_cases h : WeightDegreeSizes.RationalMapValues D
  · obtain ⟨b, hb⟩ := (GlobalTheory.Survey.IrrationalRotationBlocks.exists_bk_iff D).2 fun u φ x => h u φ x
    exact ⟨b, fun _ => hb⟩
  · exact ⟨fun _ => 0, fun h' => absurd h' h⟩

theorem exists_not_bkLaw (D : D7) (h : WeightDegreeSizes.RationalMapValues D) (u : D.what₂.Word) [Nontrivial (D.div.Nu u).V] [Nontrivial D.div.RR.V] :
    ∃ b, ¬ BkLaw (GlobalTheory.Survey.IrrationalRotationBlocks.withBk D b) :=
  let ⟨b, hb⟩ := GlobalTheory.Survey.IrrationalRotationBlocks.exists_not_buRational D u
  ⟨b, fun H => hb (H h)⟩

theorem St.kapDef {P : Pre2 K w} (x : St P) : DV.KapDef (w.D x.o.Z) := x.r.Y.kap

theorem St.gIs {P : Pre2 K w} (x : St P) : GIs2 K w x.o.Z.G := by
  change GIs2 K w x.o.G
  rw [x.G_eq]; exact P.g

def St.rowsAre {P : Pre2 K w} (x : St P) (h : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v) :
    RowsAre (w.st x.o.Z) w.I P.hX T P.Wt (Equiv.refl _) x.s.p0 where
  z := x.m.z
  intersectionNumber_baseChange := x.m.intersectionNumber_baseChange
  Y := x.r.Y
  Z := x.r.Z.full fun j v a b => (h j v a b).trans (x.m.eta j v).symm
  tup_ix t := (congrFun x.r.tup t).trans (x.m.tup t)

theorem Pre2.holdsL (P : Pre2 K w) : HoldsL P.z.R P.z.F := HoldsL.of_holds P.intersectionNumber_baseChange

theorem hasPk_of_hasBare (h : HasBare K B f T w) : HasPk K B f T w := let ⟨P, _⟩ := h; ⟨P⟩

section Std

variable {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok}

def cpR (z : Dat a.st I hX T Wt) :
    @RealDat3 b.st.toD7 _ _ _ _ _ _ (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _ ((by exact @alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@Dat.alg (@Late.st B C a) px I hX T Wt z))) :=
  (by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :))

set_option maxHeartbeats 2000000 in

theorem std_cpR (z : Dat a.st I hX T Wt) (h : z.Std) :
    @BrgStd b.st px I hX (usedOf I T Wt) z.Xg z.tr (coreJ b z.core).Q.c.F _ _ ((by exact @alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@Dat.alg (@Late.st B C a) px I hX T Wt z)))
      (@RealDat3.toRealDat _ _ _ _ _ _ _ _ _ _ _ (kc% (alg b z.alg)) (cpR b z)) := by
  kexactB h

set_option maxHeartbeats 2000000 in

theorem std_of_copy (z₀ : Dat a.st I hX T Wt) (z : Dat b.st I hX T Wt) (h1 : z.Xg = z₀.Xg) (h2 : z.tr = z₀.tr)
    (h3 : HEq z.core (coreJ b z₀.core)) (h4 : HEq z.R (real3 b (iK := z₀.alg) z₀.R)) (h : z₀.Std) : z.Std := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4
  subst h1 h2
  obtain rfl : core = coreJ b z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg b z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((y))).symm : _)))
  subst e
  obtain rfl : R = cpR b z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR b z₀)) :))))
  exact std_cpR b z₀ h

theorem exists_std_pt {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (hG : V.gram = 1) (h : Bridge.Gf V) :
    ∃ x : Formalism.L2.Col.UAd D.sp.cm n, MatEq (matIn V 1 h) (x : GL (Fin n) _) := by
  subst hn
  obtain ⟨_, g, rfl⟩ := h
  have hu : finE V g ∈ UA D.sp.cm (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) :=
    (congrArg (fun J => finE V g ∈ UA D.sp.cm J) hG).mp (GlobalTheory.LevSplit.finE_mem_UA V g)
  refine ⟨⟨finE V g, hu⟩, rfl, fun i j i' j' e e' => ?_⟩
  obtain rfl := Fin.ext e
  obtain rfl := Fin.ext e'
  unfold matIn
  rw [mul_one]
  rfl

end Std

section StdState

theorem St.std {P : Pre2 K w} (x : St P) : x.m.z.Std :=
  std_of_copy (B := B) (C := w.C) (a := P.Z₀) x.o.Z P.z x.m.z x.m.Xg x.m.tr ((by with_unfolding_all exact (x.copy.core :))) ((by with_unfolding_all exact (x.copy.R :))) P.std

theorem Pre2.vStd (P : Pre2 K w) (i) : FWT.VStd (w.st P.Z₀).toD7 i := (P.z.geo.pins i).2.lift.std

theorem gram_X (Z : w.Lt) : (w.st Z).toD7.sp.X'.gram = 1 := by
  obtain ⟨hs, -, h, -⟩ := w.ok.spaces
  change B.sp.X'.gram = 1
  rw [h]
  refine Matrix.ext fun (i j : Fin B.R.rankX') => ?_
  show Examples₂.diagForm (E := B.host.E) B.R.rankX' (fun _ => false) ((Pi.basisFun B.host.E (Fin B.R.rankX')) i) ((Pi.basisFun B.host.E (Fin B.R.rankX')) j) =
    (1 : Matrix (Fin B.R.rankX') (Fin B.R.rankX') B.host.E) i j
  rw [Pi.basisFun_apply, Pi.basisFun_apply, Examples₂.diagForm_single, Matrix.one_apply]
  simp [Examples₂.sgn]

theorem Pre2.std_row (P : Pre2 K w) : (w.st P.Z₀).toD7.sp.X'.rank = B.R.N B.R.m - 1 ∧ (w.st P.Z₀).toD7.sp.X'.gram = 1 ∧
    P.z.R.βX = 1 :=
  ⟨by rw [(w.st P.Z₀).toD7.sp.X'_rank, Formalism.L2.Col.rank_X'_eq]; rfl, gram_X _, P.z.lev.beta.2⟩

theorem Pre2.std_lift (P : Pre2 K w) (i) : (Vc (w.st P.Z₀).toD7 i).rank = B.R.nV ∧ (Vc (w.st P.Z₀).toD7 i).gram = 1 ∧
    P.z.R.βV i = 1 :=
  ⟨(w.st P.Z₀).toD7.sp.V_rank _ (by omega) i.2, (Pre2.vStd P i).1, P.z.lev.beta.1 i⟩

end StdState

end GlobalTheory.Mem.R3.Rw.StateChecks

end
