import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
import Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsWithPassage
import Formalism.LocalToGlobal.IndefiniteReal.HeckeIndexRange
import Formalism.LocalToGlobal.Columns.HeckeInertComm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Three

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.WeilFull

variable (D) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m)

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure Face3 where

  P0 : Subgroup G

  ψ0 : P0 →* D.what₂.LLˣ

  P1 : Subgroup G

  ψ1 : P1 →* D.what₂.LLˣ

  Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)

  Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)

  Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3

namespace Face3

variable {D A3} (F : Face3 D A3)

abbrev fc : DefSub A3.fam3.amb3 → DefFace A3.fam3.base3 := faceOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc

abbrev cr : Crd A3.fam3.amb3 F.fc := crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc

abbrev cv : CrdV A3.fam3.amb3 := cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1

def lv2 : Face D A3.A where
  P0 := F.P0
  ψ0 := F.ψ0
  P1 := F.P1
  ψ1 := F.ψ1
  Dc _ := ⟨PEmpty, fun u => u.elim, fun u => u.elim, fun u => u.elim⟩
  Sp _ := ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊥⟩
  Zsc _ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def eV (Zs : DefSub A3.fam3.amb3) (t : T) : (Fin ((F.fc Zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A3.fam3.amb3.FR t :=
  ((A3.A.fam.R t).S.basis.equivFun.symm : (Fin (A3.A.fam.R t).S.dim → D.what₂.LL) →ₗ[D.what₂.LL] (A3.A.fam.R t).S.Forms) ∘ₗ
    ((A3.A.fam.R t).vE (A3.A.fam.lvl F.P1 F.ψ1)).mulVecLin

end Face3

variable {D} in

def labIn (n : ℕ) (s : List ℕ) : List ℤ :=
  s.map (fun a => (a : ℤ)) ++ List.replicate (n - 2 * s.length) 0 ++ (s.reverse.map fun a => -(a : ℤ))

variable {D} in

def IsLabElt (V : HSp D) (P : Pl D.host.E) (d : List ℤ) (x : Bridge.Gf V) : Prop :=
  ∃ (e f : AE D) (ϖ : 𝓞 D.host.E) (α : GA D V), IsPrimeIdem P e f ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧ α ∈ GfC V ∧
    (x : GL _ _) = finHom V α ∧ SuppF V f α ∧ DivAt V e (ϖ : D.host.E) d α

variable {D} in

def IsLocElt (V : HSp D) (P : Pl D.host.E) (x : Bridge.Gf V) : Prop :=
  ∃ (e f : AE D) (g : GA D V), IsPrimeIdem P e f ∧ g ∈ GfC V ∧ (x : GL _ _) = finHom V g ∧ SuppF V f g

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RealDat3 (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] extends RealDat D A3.A Ks where

  plI : I0 → Pl D.host.E

  SF : Finset (HeightOneSpectrum (𝓞 D.host.F))

  phs : Fin D.R.m → ℂ

  lam3 : Fin D.R.m → T → A3.fam3.base3.Ix → InfinitePlace D.what₂.LL → ℝ

namespace RealDat3

variable {D A3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)

def EEc (c : Pl D.host.E → List ℤ → ℂ) : Submodule ℂ R.HE.H :=
  (partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) R.SF c).comap R.HE.e

def Wc' (i : Fin D.R.m) (c : Pl D.host.E → List ℤ → ℂ) : Submodule ℂ (R.HW i (sg0 D A3.A)).H :=
  (R.toRealDat.Wat i (sg0 D A3.A) R.triv ⊓
    partFull R.θ (R.MW i (sg0 D A3.A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) R.SF c).comap
      (R.HW i _).e

def Carries (p : A3.fam3.base3.Ix) (c : Pl D.host.E → List ℤ → ℂ) : Prop :=
  R.EEc c ≠ ⊥ ∧ (R.EEc c).map (LinearMap.adjoint (R.Th A3.A.μ0)) ≤
    Submodule.span ℂ (R.jX A3.A.μ0 '' ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1 : Set (A3.A.fam.R A3.A.μ0).S.Forms))

def EEp3 (p : A3.fam3.base3.Ix) : Submodule ℂ R.HE.H := ⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c), R.EEc c

def Wp3 (i : Fin D.R.m) (p : A3.fam3.base3.Ix) : Submodule ℂ (R.HW i (sg0 D A3.A)).H :=
  ⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c), R.Wc' i c

def toCx3 : CxData A3.fam3.amb3 where
  FC t := Tw (twAt D.what₂.embLL A3.A.v0) (R.HX t).H
  jR t := Tw.semi _ R.toRealDat.emb0 (R.jX t)
  EE := Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H
  Θ t := Tw.map _ (R.Th t)
  EEp p := Tw.sub _ (R.EEp3 p)
  EEl b := Tw.sub _ ((R.toRealDat.EEat (R.toRealDat.levR F.lv2 b)).comap R.HE.e)
  FLC i t := Tw (twAt D.what₂.embLL A3.A.v0) (R.HV i t).H
  jL i t := Tw.semi _ R.toRealDat.emb0 (R.jV i t)
  W i := Tw (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H
  θ' i t := R.phs i • Tw.map _ (R.thG i t)
  Wp i p := Tw.sub _ (R.Wp3 i p)
  dW b i := Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b i)
  WC b i v := Tw (twAt D.what₂.embLL v) (R.toRealDat.WS F.lv2 b i (sgAt D.what₂.embLL v))
  bW b i _ k := Tw.mk _ ⟨R.toRealDat.bC F.lv2 b i _ k, Submodule.subset_span ⟨k, rfl⟩⟩
  eW b i := Tw.map _ (((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) • (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).subtype)
  M b i := (R.FW i).Mcoord (F.lv2.lvl b).P (F.lv2.lvl b).ψ⁻¹ (fun g => (idemOf A3.A.X).coeff g) (R.toRealDat.bL F.lv2 b i)
  nP := RealDat.nP F.lv2
  μ := R.mu
  Tw := R.twPl
  κ _ := R.kap
  lam := R.lam3
  err0 := R.err0

def gEx : Representation ℂ G (R.toCx3 F).EE := Tw.rep (E := R.HE.H) _ R.gE

def gWx (i : Fin D.R.m) : Representation ℂ G ((R.toCx3 F).W i) := Tw.rep (E := (R.HW i (sg0 D A3.A)).H) _ (R.gW i (sg0 D A3.A))

abbrev num (C CH : ℝ) : IndefNum A3.fam3.base3 := (F.fc (R.toCx3 F).zs).Z.num C CH

abbrev in_tie : Prop := Bridge.InertTie A3 R.plI (R.Sb : Set (Pl D.host.E)) R.Q

abbrev in_onto : Prop := ∀ PP, Bridge.InertOff PP (R.Sb : Set (Pl D.host.E)) → ∃ Q, R.plI Q = PP

abbrev in_R : Prop :=
  ∀ t, Nonempty (Bridge.HeckeTie (Bridge.ratF D.sp.X') (R.B.R t).pres (A3.heckeRI t)
    (fun i => Formalism.L2.Col.InertTypeOk D.sp.X'.rank i.2) (fun i => IsLabElt D.sp.X' (R.plI i.1) (labIn D.sp.X'.rank i.2))
    fun i => IsLocElt D.sp.X' (R.plI i.1))

abbrev in_L : Prop :=
  ∀ i t, Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc D i)) (R.B.L i t).pres (A3.heckeLI i t)
    (fun k => Formalism.L2.Col.InertTypeOk (Vc D i).rank k.2) (fun k => IsLabElt (Vc D i) (R.plI k.1) (labIn (Vc D i).rank k.2))
    fun k => IsLocElt (Vc D i) (R.plI k.1))

abbrev in_SF : Prop :=
  ∀ v, v ∈ R.SF ↔ ∃ PP ∈ R.Sb, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal

abbrev AllPlaces : Prop := R.Sb = R.Pg

structure IsInert : Prop where
  tie : R.in_tie
  onto : R.in_onto
  hR : R.in_R
  hL : R.in_L
  SF : R.in_SF

abbrev full_Y : Prop :=
  ∀ t k, k + 1 < D.R.m → IsWeilFull R.ψ (Yc D k) (Yc D (k + 1)) (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1
    (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.ωY t k)

abbrev full_X : Prop :=
  ∀ t, IsWeilFull R.ψ (Yc D (D.R.m - 1)) D.sp.X' (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).1
    (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).2 (R.ωX t)

abbrev full_P : Prop :=
  ∀ i t, IsWeilFull R.ψ (Vc D i) (Wc D i) (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1
    (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 (R.ωP i t)

def lamN (t : T) (j : ℕ) (p : A3.fam3.base3.Ix) : ℝ := if h : j - 1 < D.R.m then R.lam3 ⟨j - 1, h⟩ t p A3.A.v0 else 1

def PartAt (i : Fin D.R.m) (p : A3.fam3.base3.Ix) (v : InfinitePlace D.what₂.LL) : Prop :=
  ∃ x, (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p ∧
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx3 F).zs) false).XT i A3.A.μ0) v x x ≠ 0

abbrev eigenvalue_at_base_of_scalar : Prop :=
  ∀ i t p (l : ℝ), R.Wp3 i p ≠ ⊥ → (∀ x ∈ R.Wp3 i p, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x) →
    R.lam3 i t p A3.A.v0 = l

abbrev scal_kap : Prop :=
  ∀ κ : ℝ, Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 R.lamN κ →
    (∃ t p, R.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p ≠ 0) → R.kap = κ

abbrev scal_off : Prop :=
  ∀ i p v (l : ℝ), v ≠ A3.A.v0 → R.PartAt F i p v →
    (∀ x, (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p → ∀ y,
      inner ℂ ((R.toCx3 F).wC false i v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec x)))
          ((R.toCx3 F).wC false i v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec y))) =
        ((l : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx3 F).zs) false).XT i A3.A.μ0) v x y) →
    R.lam3 i A3.A.μ0 p v = l

abbrev zero_part_eigenvalue_convention : Prop := ∀ i t p, R.Wp3 i p = ⊥ → R.lam3 i t p A3.A.v0 = Real.exp ((F.Zsc (R.toCx3 F).zs).l6m i)

abbrev scal_abs : Prop :=
  ∀ i p v, v ≠ A3.A.v0 → ¬ R.PartAt F i p v → R.lam3 i A3.A.μ0 p v = Real.exp ((F.Zsc (R.toCx3 F).zs).l6m i)

abbrev scal_tup : Prop := ∀ i t p v, v ≠ A3.A.v0 → R.lam3 i t p v = R.lam3 i A3.A.μ0 p v

structure IsScal : Prop where
  lam0 : R.eigenvalue_at_base_of_scalar
  kap : R.scal_kap
  off : R.scal_off F
  abs0 : R.zero_part_eigenvalue_convention F
  abs : R.scal_abs F
  tup : R.scal_tup

structure IsTup : Prop where
  mu_off : R.toRealDat.tup_mu_off
  mu_used : R.toRealDat.tup_mu_used
  mu_ne : R.toRealDat.tup_mu_ne
  mu_conj : R.toRealDat.tup_mu_conj
  mu_on : R.toRealDat.tup_mu_on

abbrev phase : Prop :=
  ∀ i, ‖R.phs i‖ = 1 ∧ ((∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, ∃ y, (R.FW i).j (sg0 D A3.A) y = c • R.thG i A3.A.μ0 (R.jV i A3.A.μ0 x)) →
    ∀ x, ∃ y, (R.FW i).j (sg0 D A3.A) y = cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i A3.A.μ0 (R.jV i A3.A.μ0 x))

def TrISem (tr : Fin D.R.m → (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL) : Prop :=
  ∀ j p c, R.Carries p c → ∀ s : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL,
    (∃ x : (A3.A.fam.L j A3.A.μ0).S.Forms, x ∈ BlockGood.goodR (A3.A.fam.L j A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) ∧
      (∀ i, (A3.liftI j A3.A.μ0).opAll i x = s i • x) ∧ R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c ∧
      R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0) →
    ∀ k : (A3.liftI j A3.A.μ0).PlI × List ℕ, s (Sum.inr k) = tr j p.1.2 ((A3.liftI j A3.A.μ0).plI k.1, k.2)

structure Char3 : Prop where
  lev : R.toLevCh.Is A3.A.μ0
  grp : R.toRealDat.IsGrp F.lv2
  fam : R.toRealDat.IsFam
  inert : R.IsInert
  models : R.toRealDat.IsModels
  chain : R.toRealDat.IsChain
  thP : R.toRealDat.IsThP
  fullY : R.full_Y
  fullX : R.full_X
  fullP : R.full_P
  scal : R.IsScal F
  tup : R.IsTup
  phase : R.phase
  allPl : R.AllPlaces

structure WeakCharacterisation : Prop where
  base : R.toRealDat.BaseW F.lv2
  inert : R.IsInert
  fullY : R.full_Y
  fullX : R.full_X
  fullP : R.full_P
  scal : R.IsScal F
  tup : R.IsTup
  phase : R.phase
  allPl : R.AllPlaces

variable {R F}

theorem characterisation_of_weak (h : R.WeakCharacterisation F) (e : R.toRealDat.ExAt) : R.Char3 F :=
  ⟨h.base.lev, h.base.grp, h.base.fam, h.inert, h.base.models, RealDat.chain_of_weak h.base.chain e,
    RealDat.thP_of_weak h.base.thP e, h.fullY, h.fullX, h.fullP, h.scal, h.tup, h.phase, h.allPl⟩

end RealDat3

end Three

end Formalism.IndefR.Links

end
