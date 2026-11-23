import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.WeakCharacterisationWithError
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.BridgeSeed
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalFrameClauses
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.SignsG
import Formalism.LocalToGlobal.IndefiniteReal.ThetaFireRow
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.PsiWeilOfAbsNorm
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import ReciprocityTheory.Automorphisms.Unitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

def SepWith (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m)
    (tr : Fin D.R.m → (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL) : Prop :=
  ∀ (j : Fin D.R.m), ∀ p ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X,
    ∀ p' ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X,
    (∃ k : A3.okI A3.A.μ0 × List ℕ, p.2 (k.1.1, k.2) ≠ p'.2 (k.1.1, k.2)) →
      ∃ k : A3.okI A3.A.μ0 × List ℕ, tr j p.2 (k.1.1, k.2) ≠ tr j p'.2 (k.1.1, k.2)

def errOf {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} (S : IndefData Df)
    (F0 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  max 0 ((∑ j', ((S.Iw j' (S.μ w) w : ℝ) + (S.Iw j' (S.μ w) (Formalism.DivisionValues.conjPl w) : ℝ))) / (S.D : ℝ) -
      ∑ j', 2 * ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * F0 w j') - (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (2 / (Formalism.EigenvalueLevelCeiling.plc w : ℝ) ^ 2)) /
    ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (Fintype.card Bs.J : ℝ))

def swapCast {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) :
    FiniteAdeleRing (𝓞 F1) F1 ⊗[F1] E ≃+* E ⊗[F2] FiniteAdeleRing (𝓞 F2) F2 := by
  subst h
  exact (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E).toRingEquiv

def StdFrame {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) : Prop :=
  (∃ (β : Matrix (Fin V.rank) (Fin n) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))
      (β' : Matrix (Fin n) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)),
      β * β' = 1 ∧ β' * β = 1 ∧
      ∀ κ, finMat D.sp.cm.sig V.gram (P.ψ κ) =
        β * ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (swapCast hF).symm) * β') ∧
  ∀ κ, κ ∈ ReciprocityTheory.Aut.Umax D.host.E n ↔ P.ψ κ ∈ KsphC V ∅

variable {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def reFace (F : Face3 D A3) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) : Face3 D A3 :=
  ⟨F.P0, F.ψ0, F.P1, F.ψ1, Dc, Sp, Zsc⟩

def ErrEq (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop :=
  ∀ w j, ((R.toCx3 F).data F.cr false).err0 w j =
    errOf ((R.toCx3 F).data F.cr false) (F.fc (R.toCx3 F).zs).Z.F0 w

structure Keep (R : RealDat D A3.A Ks) (F : Face D A3.A) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) : Prop where
  std : IsStdChar D R.ψ (-1)
  signs : Mi.SignsAtG R F
  frames : Seed.Frm.FramesExistDiagonal D R.Pg → Seed.Frm.NormalFrameConditionsDiagonal R.Pg R.βY R.βW
  beta : (∀ i, R.βV i = 1) ∧ R.βX = 1
  prX : Seed.PrIso R.MX R.cX R.prX
  grp : ∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧
    (∀ g, D.what₂.embLL ((idemOf A3.A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧
    (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧
    ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)
  psi : PsiPPTie D F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG)
  guard : FWT.QGuard R
  valKs : GlobalTheory.RealGeo.ValKs R
  frameKs : GlobalTheory.RealGeo.FrameKs Ks R.MW
  levKs : GlobalTheory.RealGeo.LevKs (Ks := Ks) F

structure Pins (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) : Prop where
  char : R.WeakCharacterisation F
  keep : Keep (A3 := A3) R.toRealDat F.lv2 cG
  phs : ∀ i, R.phs i = 1
  trSem : (∃ tr, R.TrISem F tr ∧ SepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep

structure Holds (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop where
  prim : PrimRows3 R F
  aux : UnusedChoiceStatements R F
  ok : A3.fam3.Ok3 1
  sep : A3.fam3.TypesSep3

def GeoEx (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL]
    (F : Face D A3.A) : Prop :=
  ∀ (R : RealDat D A3.A C.Q.c.F) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), GlobalTheory.RealGeo.PreChar R → R.grp_levels F → C.pb = R.C.P.pb →
    Keep (A3 := A3) R F cG → ∃ dict mu chiW x₀ cE nW FW,
      (R.upd5 nW FW R.mu R.twPl R.err0).grp_chiW ∧
      Nonempty (@GlobalTheory.RealGeo.GeoHalf D G _ _ Pl0 T A3.A (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE)
        (inferInstanceAs (Algebra C.Q.c.F D.what₂.LL)) (R.upd5 nW FW R.mu R.twPl R.err0) fun _ => 1) ∧
      ∀ i x, ∃ y, (FW i).j (sg0 D A3.A) y = R.thG i A3.A.μ0 (R.jV i A3.A.μ0 x)

def rowForm (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T)
    (x : Fin (rDim D A P ψ t) → D.what₂.LL) : A.fam.amb.FR t :=
  (A.fam.R t).S.basis.equivFun.symm
    (((A.fam.R t).S.lvlE (A.fam.R t).r (A.fam.lvl P ψ).P (A.fam.lvl P ψ).ψ).mulVec x)

def liftForm (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (i : Fin D.R.m) (t : T)
    (x : Fin (lDim D A P ψ i t) → D.what₂.LL) : A.fam.amb.FL i t :=
  (A.fam.L i t).S.basis.equivFun.symm
    (((A.fam.L i t).S.lvlE (A.fam.L i t).r (A.fam.lvlA P ψ).P (A.fam.lvlA P ψ).ψ).mulVec x)

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 4000000 in

structure Read (R : RealDat D A3.A Ks) (F : Face D A3.A) (X0 : BaseLevelRowSide D) : Type 1 where
  tup : T → D.what₂.Tup
  tupT : D.what₂.Tup → T
  tupT_tup : ∀ t, tupT (tup t) = t
  tupTie : ∀ μ, Used0 D μ → tup (tupT μ) = μ
  tup0 : tup A3.A.μ0 = D.what₂.mu0
  muAt : ∀ w, D.what₂.muAt w = tup (R.mu (D.plEq w))
  hm : 0 < D.R.m
  hTop : TopMultH R
  hinj : ∀ i t, Function.Injective (R.extV i t)
  Ish : RowIds (RowSide.sharp D) (toChainReal R F tupT hm hTop) true
  Iz : RowIds X0.s (toChainReal R F tupT hm hTop) false
  IL : LiftIds (toLiftReal R F tupT hm hTop hinj)
  Kc : ColReal D
  PY : principalLevelFrame.RowPsi (Yc D 0) D.R.r
  PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) D.R.r
  eFT : D.what₂.FT ≃ principalLevelFrame.FTR R.θ PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b)))
    (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0)
  ιW : ∀ i, ↥(GfC (Yc D 0)) →* ↥(GfC (Wc D i))
  tied : RecTied D X0 (toChainReal R F tupT hm hTop) Ish Iz (toLiftReal R F tupT hm hTop hinj) IL Kc
  prtE : ∀ π, Ish.prt π = (principalLevelFrame.isotE R.θ PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F true)))
    (levChi _ (R.βY 0) (R.dat0 (R.levR F true))) R.e0 (principalLevelFrame.rowRepR R.θ (eFT π))).map
      (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap
  prtE0 : ∀ π, Iz.prt π = (principalLevelFrame.isotE R.θ PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F false)))
    (levChi _ (R.βY 0) (R.dat0 (R.levR F false))) R.e0 (principalLevelFrame.rowRepR R.θ (eFT π))).map
      (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap
  prtWE : ∀ i π, IL.prtW i π = (principalLevelFrame.isotL R.θ (PW i) (R.MW i (sg0 D A3.A))
    (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A3.A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A3.A))))
    (R.eWf i (sg0 D A3.A)) (principalLevelFrame.rowRepR R.θ (eFT π))).map
      (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap
  xi : ∀ μ, Used0 D μ → Kc.xi μ = R.toLevCh.xi (tupT μ)
  isomFin : ∀ i, principalLevelFrame.IsIsomFin (ιW i)
  frameMatch : ∀ i, principalLevelFrame.FrameMatch PY (PW i) (ιW i)
  hF : D.host.F = maximalRealSubfield D.host.E
  stdPsi : StdFrame hF PY ∧ ∀ i, StdFrame hF (PW i)
  jA : ∀ t, (Fin (rDim D A3.A F.P1 F.ψ1 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb (tup t)
  jA0 : ∀ t, (Fin (rDim D A3.A F.P0 F.ψ0 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X0.s.Amb (tup t)
  eMt : ∀ (i : Fin D.R.m) (t : T),
    (Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)
  formsA : ∀ t, FormsTie D.what₂.embLL (jA t) (rH D A3.A F.P1 F.ψ1 t) (rE D A3.A F.P1 F.ψ1 t) (D.what₂.eOp (tup t))
  latA : ∀ t, OLatTie D.what₂.embLL (D.what₂.Mtilde (tup t)) (jA t) (rNab D A3.A F.P1 F.ψ1 t)
  formsAtBottomLevel : ∀ t, FormsTie D.what₂.embLL (jA0 t) (rH D A3.A F.P0 F.ψ0 t) (rE D A3.A F.P0 F.ψ0 t) (X0.s.eOp (tup t))
  latA0 : ∀ t, OLatTie D.what₂.embLL (X0.s.Mtilde (tup t)) (jA0 t) (rNab D A3.A F.P0 F.ψ0 t)
  formsL : ∀ (i : Fin D.R.m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap)
    (lH D A3.A F.P0 F.ψ0 i t) (lE D A3.A F.P0 F.ψ0 i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1))
  latL : ∀ (i : Fin D.R.m) (t : T), OLatTie D.what₂.embLL (D.what₂.MtLat (tup t) ((i : ℕ) + 1))
    ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lNab D A3.A F.P0 F.ψ0 i t)
  topRead : ∀ t (h : Used0 D (tup t)) x,
    (Ish.jX (tup t) h ((D.what₂.multTop (tup t)).symm (jA t x))).1 =
      R.cX.toMap R.prX ((R.HX t).e (R.jX t (rowForm A3.A F.P1 F.ψ1 t x)))
  topRead0 : ∀ t (h : Used0 D (tup t)) x,
    (Iz.jX (tup t) h ((X0.s.multTop (tup t)).symm (jA0 t x))).1 =
      R.cX.toMap R.prX ((R.HX t).e (R.jX t (rowForm A3.A F.P0 F.ψ0 t x)))
  mtRead : ∀ (i : Fin D.R.m) t (h : Used0 D (tup t)) x,
    (IL.jMt (tup t) h i (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x))).1 =
      R.extV i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x))
  mj : GlobalTheory.RealGeo.MjTie R F
  mjRead : ∀ (i : Fin D.R.m) y, (IL.jMj i y).1 = PiTensorProduct.lift ((R.HW i (sg0 D A3.A)).e (mj.eW i y))
  stable : ∀ μ (a : 𝓞 D.what₂.LL), ∀ y ∈ (D.what₂.Mtilde μ).carrier,
    D.what₂.embLL (a : D.what₂.LL) • y ∈ (D.what₂.Mtilde μ).carrier
  stable0 : ∀ μ (a : 𝓞 D.what₂.LL), ∀ y ∈ (X0.s.Mtilde μ).carrier,
    D.what₂.embLL (a : D.what₂.LL) • y ∈ (X0.s.Mtilde μ).carrier
  eE : D.what₂.EE →ₗ[ℂ] R.HE.H
  eE_read : ∀ x, (Ish.jE x).1 = PiTensorProduct.lift (R.HE.e (eE x))
  dall : D.what₂.Dall = Module.finrank ℂ (Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F true)))
    (levChi _ (R.βY 0) (R.dat0 (R.levR F true))))
  junk : ∀ μ, ¬ Used0 D μ → D.what₂.iota μ = 0
  cen0 : ∀ cG, Keep (A3 := A3) R F cG → CenTie D A3.A X0.s F.P0 F.ψ0 (R.eG.trans cG) tup jA0
  cen1 : ∀ cG, Keep (A3 := A3) R F cG → CenTie D A3.A (RowSide.sharp D) F.P1 F.ψ1 (R.eG.trans cG) tup jA
  lam : DV.LamDef D
  occ : ∀ π, (∃ σ, D.what₂.ft σ = π) ∨ ∃ σ, D.what₂.ft0 σ = π
  kap : DV.KapDef D
  bu : Formalism.BasicNotions.Rows.BuDefQ D.what₂
  ze : ∀ (u : D.what₂.Word) (μ : D.what₂.Tup) (c : ℂ),
    (∀ (φ : D.what₂.Mu u) (x : D.what₂.Amb μ), x ∈ D.what₂.V0 μ →
      D.what₂.perCol u μ φ x = c * D.what₂.Bu u φ (D.what₂.iota μ ((D.what₂.Qsp μ).starProjection x))) →
    (∃ (φ : D.what₂.Mu u) (x : D.what₂.Amb μ), x ∈ D.what₂.V0 μ ∧ D.what₂.perCol u μ φ x ≠ 0) → (∃ z : D.what₂.LL, D.what₂.embLL z = c) →
    D.what₂.zeC u μ = c

open Classical in
set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 4000000 in

structure ReadL (R : RealDat3 D A3 Ks) (F : Face3 D A3) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) : Type where
  eRR : (Fin ((R.toCx3 F).data F.cr true).D → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V
  eRR0 : (Fin ((R.toCx3 F).data F.cr false).D → D.what₂.LL) ≃ₗ[D.what₂.LL] X0.s.RR.V
  jEE : ∀ y, (Y.Ish.jE (D.jEE (eRR y))).1 =
    PiTensorProduct.lift (R.HE.e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y))))
  jEE0 : ∀ y, (Y.Iz.jE (X0.s.jEE (eRR0 y))).1 =
    PiTensorProduct.lift (R.HE.e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr false A3.A.μ0 (cpt A3.A.v0.embedding y))))
  met : ∀ v, v ≠ A3.A.v0 → ∀ x y, Formalism.HermitianLatticesTheory.majAt D.div.RR.b D.div.RR.X v (eRR x) (eRR y) =
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((R.toCx3 F).data F.cr true).XE v x y
  met0 : ∀ v, v ≠ A3.A.v0 → ∀ x y, Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X v (eRR0 x) (eRR0 y) =
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((R.toCx3 F).data F.cr false).XE v x y
  rr : (RowSide.sharp D).RRDef
  rr0 : X0.s.RRDef
  jW : ∀ i : Fin D.R.m, (Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)
  jW_read : ∀ (i : Fin D.R.m) y, Y.mj.eW i (jW i y) =
    (R.FW i).j (sg0 D A3.A) (Fintype.linearCombination D.what₂.LL (R.toRealDat.bL F.lv2 false i) y)
  etaJ : ∀ (i : Fin D.R.m) w, D.what₂.etaJ ((i : ℕ) + 1) w =
    if D.plEq w ∈ R.twPl then A3.A.fam.etaJ F.P0 F.ψ0 (A3.fam3.toSub2 (R.toCx3 F).zs) i (R.mu (D.plEq w)) (D.plEq w) else 0

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure ReadC (R : RealDat3 D A3 Ks) (F : Face3 D A3) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) : Type where
  wU : D.what₂.Word → (F.Dc (R.toCx3 F).zs).Mem
  bij : Function.Bijective wU
  eNu : ∀ u, (Fin ((F.Dc (R.toCx3 F).zs).a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V
  NuC : ∀ x, Submodule (𝓞 D.what₂.LL) (Fin ((F.Dc (R.toCx3 F).zs).a x) → D.what₂.LL)
  nu : ∀ u, HLatTie (D.div.Nu u) (NuC (wU u)) ((F.Dc (R.toCx3 F).zs).Xc (wU u)) (eNu u)
  pt : ∀ (u : D.what₂.Word) (t : T) (x : Fin ((F.Dc (R.toCx3 F).zs).a (wU u)) → D.what₂.LL)
    (f : Fin ((A3.side3 F.P1 F.ψ1 (R.toCx3 F).zs).nV t) → D.what₂.LL),
    D.what₂.embLL ((F.Dc (R.toCx3 F).zs).Pt (wU u) t x f) =
      D.what₂.perCol u (Y.tup t) (D.jN u (eNu u x)) (Y.jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f))

section Ids

variable {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}

abbrev zsOf (R : RealDat3 D A3 Ks) (F : Face3 D A3) : DefSub A3.fam3.amb3 := (R.toCx3 F).zs

def s0Of (R : RealDat3 D A3 Ks) (F : Face3 D A3) : IndefData (A3.side3 F.P0 F.ψ0 (zsOf R F)) := (R.toCx3 F).data F.cr false

def s1Of (R : RealDat3 D A3 Ks) (F : Face3 D A3) : IndefData (A3.side3 F.P1 F.ψ1 (zsOf R F)) := (R.toCx3 F).data F.cr true

def colOf (R : RealDat3 D A3 Ks) (F : Face3 D A3) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) :
    ColData (F.Dc (zsOf R F)) (F.Sp (zsOf R F)) (s1Of R F) :=
  (R.toCx3 F).colOf F.cr ((R.toCx3 F).colDef (fun u t => (zetaEps (R.toCx3 F) F.cr sEE u t)⁻¹) sEE)

def idsOf (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y) :
    DivisionCompatibilityDataThreeSided D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) X0 (F.Dc (zsOf R F)) where
  eG := R.eG.trans cG
  tup := Y.tup
  eRR := Z.eRR
  eRR0 := Z.eRR0
  jA := Y.jA
  jA0 := Y.jA0
  eMt := Y.eMt
  jW := Z.jW
  wU := C.wU
  eNu := C.eNu

open Classical in

def Lam3 (Z : ReadL R F X0 Y) : Prop :=
  ∃ cOf : D.what₂.FT → A3.fam3.base3.Ix,
    (∀ (i : Fin D.R.m) (c : A3.fam3.base3.Ix),
      iSupIndep (fun σ : {σ : D.what₂.FT // cOf σ = c} => D.what₂.isot ((i : ℕ) + 1) σ.1) ∧
      (⨆ σ : {σ : D.what₂.FT // cOf σ = c}, D.what₂.isot ((i : ℕ) + 1) σ.1) =
        Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i c : Set (Fin ((s0Of R F).dW i) → D.what₂.LL)))) ∧
    (∀ (i : Fin D.R.m) (t : T) (σ : D.what₂.FT),
      (Y.tup t = D.what₂.mu0 ∨ ∃ w, Y.tup t = D.what₂.muAt w) → D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ →
      D.what₂.lamP (Y.tup t) ((i : ℕ) + 1) σ = (s0Of R F).lam i t (cOf σ) A3.fam3.base3.v0) ∧
    (∀ c : A3.fam3.base3.Ix,
      ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = c), D.what₂.nRows0 σ = Module.finrank D.what₂.LL ((s0Of R F).Ep c))

end Ids

namespace DatApi

theorem sepWith_trI : SepWith A3 A3.trI ↔ A3.fam3.TrISep := Iff.rfl

section Err

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

end Err

theorem swapCast_one_tmul {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) (x : E) :
    swapCast h (1 ⊗ₜ[F1] x) = x ⊗ₜ[F2] 1 := by
  subst h; rfl

theorem toCx3_reFace (R : RealDat3 D A3 Ks) (F : Face3 D A3) (Dc Sp Zsc) : R.toCx3 (reFace F Dc Sp Zsc) = R.toCx3 F := rfl

theorem rowForm_add (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T) (x y) :
    rowForm A P ψ t (x + y) = rowForm A P ψ t x + rowForm A P ψ t y := by
  unfold rowForm
  exact (congrArg _ (Matrix.mulVec_add _ x y)).trans (map_add _ _ _)

theorem rowForm_smul (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T) (c : D.what₂.LL) (x) :
    rowForm A P ψ t (c • x) = c • rowForm A P ψ t x := by
  unfold rowForm
  exact (congrArg _ (Matrix.mulVec_smul _ c x)).trans (map_smul _ _ _)

theorem liftForm_add (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (i : Fin D.R.m) (t : T) (x y) :
    liftForm A P ψ i t (x + y) = liftForm A P ψ i t x + liftForm A P ψ i t y := by
  unfold liftForm
  exact (congrArg _ (Matrix.mulVec_add _ x y)).trans (map_add _ _ _)

theorem liftForm_smul (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (i : Fin D.R.m) (t : T)
    (c : D.what₂.LL) (x) : liftForm A P ψ i t (c • x) = c • liftForm A P ψ i t x := by
  unfold liftForm
  exact (congrArg _ (Matrix.mulVec_smul _ c x)).trans (map_smul _ _ _)

section Lat

variable {K : Type} [Field K] [NumberField K] {O : Type} [CommRing O] {φ : O →+* ℂ} {σ : K →+* ℂ}
  {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}

theorem sum_mem (M : Rows.OLat O φ W) {ι : Type} (s : Finset ι) (f : ι → W) (h : ∀ i ∈ s, f i ∈ M.carrier) :
    ∑ i ∈ s, f i ∈ M.carrier := by
  refine Finset.sum_induction f (· ∈ M.carrier) ?_ ⟨0, by simp⟩ h
  rintro x y ⟨c, rfl⟩ ⟨c', rfl⟩
  exact ⟨c + c', by rw [← Finset.sum_add_distrib]; simp [add_smul]⟩

end Lat

end DatApi

end GlobalTheory.Mem.R3

end
