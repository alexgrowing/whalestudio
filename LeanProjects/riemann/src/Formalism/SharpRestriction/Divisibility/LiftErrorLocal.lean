import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataNChoice
import Formalism.LocalRingCardinality.DataErr
import Formalism.LocalRingCardinality.DataKap
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.LevelLetterCocycles.LocsCoverTw

noncomputable section

namespace Formalism.MainNotions.LiftErrorLocal

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

abbrev Pl (D : D7) : Type := D.what₂.places.Pl

def Over (D : D7) (i : Fin 2) (w : Pl D) : Prop := D.what₂.places.resChar w = D.host.g i

instance instFactG (D : D7) (i : Fin 2) : Fact (D.host.g i).Prime := ⟨D.host.g_prime i⟩

def vG (D : D7) (w : Pl D) (x : D.what₂.LL) : ℝ :=
  (vAdd (D.plEq w) x : ℝ) / (D.what₂.places.ramIdx w : ℝ)

def lifts (D : D7) : Finset ℕ := Finset.Icc 1 D.R.m

def delq (D : D7) : ℝ :=
  (∏ i ∈ Finset.Ico 1 D.R.r, (((D.host.g 0 : ℝ) ^ i - 1) * ((D.host.g 1 : ℝ) ^ i - 1))) ^ D.R.f

def Dpm (D : D7) (j : ℕ) : ℤ :=
  ∑ τ : D.what₂.Tau, ((∑ a, D.what₂.kaBig j τ a) - ∑ a, D.what₂.kaSmall j τ a)

def vDv (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (l : ℕ) (x : R) : ℝ :=
  ((IsDiscreteValuationRing.addVal R x).toNat : ℝ) / ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ)

def lenQ {R W : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup W] [Module R W]
    (l : ℕ) (M N : Submodule R W) : ℝ :=
  IntegralHeckeForms.lenR R l (M ⧸ N.comap M.subtype)

structure GeoX {D : D7} {r j p : ℕ} (Lc : ModuliIntegralCharts.Loc D r j p) where

  sgE : ∀ y : Lc.Pt Lc.Xm, ModuliIntegralCharts.PsiT D × Bool → (D.host.E →+* (Lc.fld y).C)
  sgE_conj : ∀ y τ x, sgE y (τ, true) x = sgE y (τ, false) (D.host.conj x)

  nrm : ∀ y La n, Lc.Sn y La n → ℝ

  pull : ∀ y La n, Lc.Sn y La n →ₗ[(Lc.fld y).C] Lc.Sn y La (p * n)

  inQQ : ∀ y La n, Lc.At y La n → Prop

  Lt : Lc.Pt Lc.Xm → Lc.Unim → Type
  [ltFin : ∀ y La, Fintype (Lt y La)]

  ltype : ∀ y La, Lt y La → ModuliIntegralCharts.PsiT D × Bool

  harm : ∀ y La, MvPolynomial (Lt y La) (Lc.fld y).C → Prop

  harm_plus : ∀ y La (P : MvPolynomial (Lt y La) (Lc.fld y).C),
    (∀ l ∈ P.vars, (ltype y La l).2 = false) → harm y La P

  harm_minus : ∀ y La (P : MvPolynomial (Lt y La) (Lc.fld y).C),
    (∀ l ∈ P.vars, (ltype y La l).2 = true) → harm y La P

  ev : ∀ y La n, MvPolynomial (Lt y La) (Lc.fld y).C → Lc.Sn y La n → (Lc.fld y).C

  evT : ∀ y La n, Lc.Th y La (p * n) → Lc.Sn y La n → MvPolynomial (Lt y La) (Lc.fld y).C → (Lc.fld y).C

  isHT : ∀ y La n, Lc.At y La n → (Lt y La → (Lc.fld y).C) → Prop

attribute [instance] GeoX.ltFin

namespace GeoX

variable {D : D7} {r j p : ℕ} {Lc : ModuliIntegralCharts.Loc D r j p} (G : GeoX Lc)

open Classical in

def typeDeg {y : Lc.Pt Lc.Xm} {La : Lc.Unim} (e : G.Lt y La →₀ ℕ) (σ : ModuliIntegralCharts.PsiT D × Bool) : ℕ :=
  ∑ l ∈ e.support, if G.ltype y La l = σ then e l else 0

def HomT {y : Lc.Pt Lc.Xm} {La : Lc.Unim} (P : MvPolynomial (G.Lt y La) (Lc.fld y).C) : Prop :=
  ∀ e ∈ P.support, ∀ e' ∈ P.support, ∀ σ, G.typeDeg e σ = G.typeDeg e' σ

def IntP {y : Lc.Pt Lc.Xm} {La : Lc.Unim} (P : MvPolynomial (G.Lt y La) (Lc.fld y).C) : Prop :=
  ∀ e, ‖P.coeff e‖ ≤ 1

def nnOf {y : Lc.Pt Lc.Xm} {La : Lc.Unim} (x : D.host.E) (e : G.Lt y La →₀ ℕ) : (Lc.fld y).C :=
  e.prod fun l k => G.sgE y (G.ltype y La l) x ^ k

def IsV {y : Lc.Pt Lc.Xm} {La : Lc.Unim} (x : D.host.E) (l : G.Lt y La) : Prop :=
  ‖G.sgE y (G.ltype y La l) x‖ < 1

open Classical in

def subV {y : Lc.Pt Lc.Xm} {La : Lc.Unim} (x : D.host.E) (yy : G.Lt y La → (Lc.fld y).C)
    (P : MvPolynomial (G.Lt y La) (Lc.fld y).C) : MvPolynomial (G.Lt y La) (Lc.fld y).C :=
  MvPolynomial.bind₁ (fun l => if G.IsV x l then MvPolynomial.C (yy l) else MvPolynomial.X l) P

def INT : Prop :=
  ∀ (y : Lc.Pt Lc.Xm) (La : Lc.Unim), G.nrm y La 1 (Lc.vth y La 1) ≤ 1 ∧
    (∀ n (s : Lc.Sn y La n), G.nrm y La (p * n) (G.pull y La n s) = G.nrm y La n s) ∧
    (∀ n (γ : Lc.Th y La n) (s : Lc.Sn y La n), (∃ k : ℕ, 0 < k ∧ γ ^ k = 1) →
      G.nrm y La n (Lc.act y La n γ s) = G.nrm y La n s) ∧
    (∀ n (s : Lc.Sn y La n), G.nrm y La n s ≤ 1 → ∀ DF, Lc.jet y La n DF s ∈ Lc.intJet y La n DF)

def LemA (x : D.host.E) : Prop :=
  ∀ (y : Lc.Pt Lc.Xm) (La : Lc.Unim) (n' : ℕ), Nat.Coprime n' p → ∀ s : Lc.Sn y La n', G.nrm y La n' s ≤ 1 →
    ∀ γ : Lc.Th y La (p * n'), (∃ k : ℕ, 0 < k ∧ γ ^ k = 1) →
      G.inQQ y La (p * n') (Multiplicative.toAdd (Lc.ovr y La (p * n') γ)) →
    (∀ DF, Lc.jet y La (p * n') DF (Lc.act y La (p * n') γ (G.pull y La n' s)) ∈ Lc.intJet y La (p * n') DF) ∧
    ∀ P : MvPolynomial (G.Lt y La) (Lc.fld y).C, G.IntP P → G.harm y La P → G.HomT P → P.totalDegree + 1 < p →
      ‖G.ev y La (p * n') P (Lc.act y La (p * n') γ (G.pull y La n' s))‖ ≤ 1 ∧
      (∀ e ∈ P.support, G.ev y La (p * n') P (Lc.act y La (p * n') γ (G.pull y La n' s)) =
        G.nnOf x e * G.evT y La n' γ s P) ∧
      (∀ yy, G.isHT y La (p * n') (Multiplicative.toAdd (Lc.ovr y La (p * n') γ)) yy →
        ‖G.ev y La (p * n') P (Lc.act y La (p * n') γ (G.pull y La n' s)) -
          G.ev y La (p * n') (G.subV x yy P) (Lc.act y La (p * n') γ (G.pull y La n' s))‖ ≤ (p : ℝ)⁻¹)

end GeoX

def HTb {D : D7} {r j p : ℕ} (Lc : ModuliIntegralCharts.Loc D r j p) : Prop :=
  ∀ y : Lc.Pt Lc.Xm,
    ModuliIntegralCharts.Ospan (C := (Lc.fld y).C) (Set.range (Lc.ht y)) ≤ Lc.om y ∧
    ∀ x ∈ Lc.om y, ∀ c : (Lc.fld y).C, ‖c‖ ≤ (p : ℝ) ^ (-(1 : ℝ) / ((p : ℝ) - 1)) →
      c • x ∈ ModuliIntegralCharts.Ospan (C := (Lc.fld y).C) (Set.range (Lc.ht y))

def CdOf (D : D7) (CRd : ℝ) (d' : ℕ) : ℝ := WeightFamilies.RRv D CRd * (d' : ℝ) ^ 3

def PhiB {D : D7} {r j p : ℕ} (Lc : ModuliIntegralCharts.Loc D r j p) (CRd : ℝ) : Prop :=
  ∀ (Z : Lc.Mdl) (y : Lc.Pt Z), 0 ≤ Lc.phiCy y ∧ (Lc.phiCy y = 0 ↔ Lc.good y) ∧
    ∀ (a : Lc.Ylat y) (n : ℕ), 0 < n → ∃ z : Lc.Ylat y,
      Lc.be y (a - n • z) (a - n • z) / 2 ≤ (n : ℝ) ^ 2 * ((Lc.dP y : ℝ) * CdOf D CRd (Lc.dP y) * Lc.phiCy y)

def pib {D : D7} (EX : ErrX D) (i : Fin 2) : D.host.E := D.host.conj (EX.piG i : D.host.E)

def plS {D : D7} (nch : NChoice D) (w : Pl D) (b : Bool) : Pl D :=
  if b = nch.sd w then w else D.what₂.places.conj w

theorem plS_self {D : D7} (nch : NChoice D) (w : Pl D) (h : D.what₂.places.conj w = w) (b : Bool) :
    plS nch w b = w := by
  unfold plS
  split_ifs
  · rfl
  · exact h

structure Run (D : D7) (B : WeightFamilies.Prov D) (j : ℕ) where
  S : WeightAlgebra.Scal B
  ka : WeightFamilies.Wt D j
  wL : WeightFamilies.Wt D j
  wF : WeightFamilies.Wt D j
  nP : ℕ
  nW : ℕ
  h0 : ℝ
  n1 : ℕ
  n2 : ℕ
  nus : HeightOneSpectrum (𝓞 B.KO) → ℝ

set_option synthInstance.maxHeartbeats 400000 in

structure Loc (D : D7) (nch : NChoice D) where

  B : WeightFamilies.Prov D

  P6 : ModuliIntegralCharts.Prov D

  W : WeightAlgebra.Prov D B P6

  sig_le : ∀ d : P6.Dat, min (P6.jj d) (P6.rk d - P6.jj d) ≤ D.R.m

  I : TwIn D

  gx : ∀ (d : P6.Dat) (i : Fin 2), GeoX (P6.loc d (D.host.g i))

  cm : ∀ (N : ℕ) (i : Fin 2), ModuliIntegralCharts.Loc D N N (D.host.g i)
  cmx : ∀ (N : ℕ) (i : Fin 2), GeoX (cm N i)

  cm_plus : ∀ N i y La l, ((cmx N i).ltype y La l).2 = false

  TO : ℕ

  run : ∀ j, Run D B j

  ka_big : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ i, ((run j).ka.aP τ i : ℤ) = D.what₂.kaBig j τ i
  ka_small : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ c, ((run j).ka.aM τ c : ℤ) = -D.what₂.kaSmall j τ (Fin.rev c)

  laK : Pl D → HeightOneSpectrum (𝓞 B.KO)
  laK_def : ∀ w (x : 𝓞 B.KO), x ∈ (laK w).asIdeal ↔ 0 < D.what₂.places.val w (D.what₂.OtoLL (B.eO x))

  embK : ∀ (w : Pl D) (_b : Bool), B.KO →+* FractionRing (D.ntw.O (nch.twI w))
  embK_int : ∀ w b (x : B.KO), 0 ≤ vAdd (laK (plS nch w b)) x ↔
    embK w b x ∈ (algebraMap (D.ntw.O (nch.twI w)) (FractionRing (D.ntw.O (nch.twI w)))).range

  toFm : ∀ (w : Pl D) (j : ℕ) (b : Bool), B.Cusp j (run j).ka →ₛₗ[embK w b] D.nexp.Fm (nch.twI w) j b
  toFm_li : ∀ w j b, 1 ≤ j → j ≤ D.R.m → ∀ β : Module.Basis (Module.Free.ChooseBasisIndex B.KO (B.Cusp j (run j).ka)) B.KO
      (B.Cusp j (run j).ka),
    LinearIndependent (FractionRing (D.ntw.O (nch.twI w))) (fun a => toFm w j b (β a))

  toFm_sup : ∀ w j b, 1 ≤ j → j ≤ D.R.m → D.nexp.Bsup (nch.twI w) j b =
    Submodule.span (D.ntw.O (nch.twI w)) (toFm w j b '' (B.Mlat j (run j).ka : Set (B.Cusp j (run j).ka)))

  WWB : ∀ j (_la : HeightOneSpectrum (𝓞 B.KO)) (wt : WeightFamilies.Wt D j) (_n1 _n2 : ℕ), Submodule (𝓞 B.KO) (B.Cusp j wt)

section Lat

variable (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool)

def Mj : Submodule (D.ntw.O i) (D.nexp.Fm i j b) :=
  IntegralHeckeForms.Mall D.nexp i j b ⊓ (IntegralHeckeForms.V0 D.nexp i j b).restrictScalars (D.ntw.O i)

variable {D i j b}

def psiPart (N : Submodule (D.ntw.O i) (D.nexp.Fm i j b)) : Submodule (D.ntw.O i) (D.nexp.Fm i j b) :=
  N ⊓ (IntegralHeckeForms.Fm0 D.nexp i j b).restrictScalars (D.ntw.O i)

def GStab (N : Submodule (D.ntw.O i) (D.nexp.Fm i j b)) : Prop :=
  ∀ (g : G0g D.nd) (x : D.nexp.Fm i j b), x ∈ N → D.nexp.actG i j b g x ∈ N

def GSpan (N : Submodule (D.ntw.O i) (D.nexp.Fm i j b)) : Submodule (D.ntw.O i) (D.nexp.Fm i j b) :=
  ⨆ g : G0g D.nd, N.map ((D.nexp.actG i j b g).toLinearMap.restrictScalars (D.ntw.O i))

def spK (N : Submodule (D.ntw.O i) (D.nexp.Fm i j b)) :
    Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
  Submodule.span (FractionRing (D.ntw.O i)) (N : Set (D.nexp.Fm i j b))

def rkK (N : Submodule (D.ntw.O i) (D.nexp.Fm i j b)) : ℕ :=
  Module.finrank (FractionRing (D.ntw.O i)) (spK N)

end Lat

def vU (D : D7) (i : D.ntw.Tw) : ℝ := (padicValNat (D.ntw.l i) (Nat.card D.nexp.U) : ℝ)

namespace Loc

variable {D : D7} {nch : NChoice D} (X : Loc D nch)

def laOver (i : Fin 2) (la : HeightOneSpectrum (𝓞 X.B.KO)) : Prop := ((D.host.g i : ℕ) : 𝓞 X.B.KO) ∈ la.asIdeal

def ThN (w : Pl D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool) :
    Submodule (D.ntw.O (nch.twI w)) (D.nexp.Fm (nch.twI w) j b) :=
  Submodule.span (D.ntw.O (nch.twI w)) (X.toFm w j b '' {F | (X.W j h1 h2).inc (X.run j).ka F ∈
    (X.W j h1 h2).Theta (X.run j).S (X.run j).ka (X.run j).wL (X.run j).wF X.TO})

def Th0 (w : Pl D) (j : ℕ) (b : Bool) : Submodule (D.ntw.O (nch.twI w)) (D.nexp.Fm (nch.twI w) j b) :=
  IntegralHeckeForms.ThJ D.nexp X.I.E (nch.twI w) j b

def psiW (_X : Loc D nch) (w : Pl D) (b : Bool) : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok (nch.twI w) (nch.k' w))ˣ :=
  BlochKatoReduction.Gen.psiAt b ((BlochKatoReduction.Gen.psiAt (nch.sd w) (nch.psi' w)).comp (D.ntw.art (nch.twI w) (nch.Q w)))

def MjK (_X : Loc D nch) (w : Pl D) (j : ℕ) (b : Bool) :
    Submodule (D.ntw.Ok (nch.twI w) (nch.k' w))
      (D.ntw.Ok (nch.twI w) (nch.k' w) ⊗[D.ntw.O (nch.twI w)] D.nexp.Fm (nch.twI w) j b) :=
  (Mj D (nch.twI w) j b).baseChange (D.ntw.Ok (nch.twI w) (nch.k' w))

def IsgTw (w : Pl D) (j : ℕ) (b : Bool) : ℝ :=
  IntegralHeckeForms.sIdx (D.ntw.l (nch.twI w)) (X.MjK w j b)
    (IntegralHeckeForms.eThPMt D.nexp (nch.twI w) j b (nch.k' w) (nch.Q w) (X.psiW w b))

def IsgBase (w : Pl D) (j : ℕ) (b : Bool) : ℝ :=
  IntegralHeckeForms.sIdx (D.ntw.l (nch.twI w)) (X.MjK w j b) (IntegralHeckeForms.eThPMt D.nexp (nch.twI w) j b (nch.k' w) ∅ 1)

def cB (_X : Loc D nch) (CRd : ℝ) (i : Fin 2) (j DF nW : ℕ) : ℝ :=
  (WeightFamilies.dP D j : ℝ) * CdOf D CRd (WeightFamilies.dP D j) * nW / (D.host.g (1 - i) : ℝ) +
    2 * CdOf D CRd (WeightFamilies.dP D j) * (DF : ℝ) ^ 2 / (D.host.g (1 - i) : ℝ)

def RangeB (_X : Loc D nch) (CRd : ℝ) (i : Fin 2) {j : ℕ} (wt : WeightFamilies.Wt D j) (n1 n2 : ℕ) : Prop :=
  wt.n = n1 + n2 ∧ D.R.r ≤ n1 ∧ D.R.r ≤ n2 ∧ wt.LastPos ∧ (∀ i', 2 * WeightAlgebra.DF wt + 2 < D.host.g i') ∧
    3 * WeightAlgebra.DF wt + 2 ≤ D.host.g (1 - i) ∧
    2 * CdOf D CRd (WeightFamilies.dP D j) * ((WeightAlgebra.DF wt : ℝ) ^ 2 + (n1 + n2 : ℕ)) ≤ (D.host.g (1 - i) : ℝ) ∧
    (WeightFamilies.dP D j : ℝ) ^ 2 * (D.R.f : ℝ) ^ 2 ≤ 4 * D.host.rdE ^ (CRd - 2)

end Loc

def AjMu (D : D7) (μ : D.what₂.Tup) (j : ℕ) (w : Pl D) : ℤ :=
  D.what₂.Ij μ j w + D.what₂.Ij μ j (D.what₂.places.conj w) + D.what₂.jw μ j w

section admitted

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : Loc D nch)

def adm1 : Prop := (∀ d i, (X.gx d i).INT) ∧ ∀ N i, (X.cmx N i).INT

def adm2 : Prop := (∀ d (i : Fin 2), HTb (X.P6.loc d (D.host.g i))) ∧ ∀ N i, HTb (X.cm N i)

def adm3 : Prop := ModuliIntegralCharts.LinkConditions D X.P6

def adm3b (CRd : ℝ) : Prop := ∀ d (i : Fin 2), PhiB (X.P6.loc d (D.host.g i)) CRd

def ArchimedeanSignatureMatching (H : WeightAlgebra.KHyp) (C2 A2 CR CT : ℝ) : Prop := WeightAlgebra.Conclusion1 L X.W H C2 A2 CR CT

def adm5 (C : NChoice D) : Prop := ∀ i0 w, Over D i0 w → ∀ j ∈ lifts D, ∀ b : Bool,
  ∀ B1 B2 : Submodule (D.ntw.O (C.twI w)) (D.nexp.Fm (C.twI w) j b),
    B1.FG → B2 ≤ B1 → spK B2 = spK B1 → GStab B1 → GStab B2 →
    delq D * lenQ (D.ntw.l (C.twI w)) (psiPart B1) (psiPart B2) ≤
      lenQ (D.ntw.l (C.twI w)) B1 B2 + (rkK B1 : ℝ) * vU D (C.twI w)

def adm6 (C : NChoice D) : Prop := ∀ i0 w, Over D i0 w → ∀ j ∈ lifts D, ∀ b : Bool,
  (rkK (D.nexp.Bsup (C.twI w) j b) : ℝ) / delq D ≤
      2 * (Module.finrank (FractionRing (D.ntw.O (C.twI w))) (IntegralHeckeForms.Fm0 D.nexp (C.twI w) j b) : ℝ) ∧
    Module.finrank (FractionRing (D.ntw.O (C.twI w))) (IntegralHeckeForms.V0 D.nexp (C.twI w) j b) = D.what₂.D0 ∧
    (Module.finrank (FractionRing (D.ntw.O (C.twI w))) (IntegralHeckeForms.Fm0 D.nexp (C.twI w) j b) : ℝ) ≤ 2 * D.what₂.D0 ∧
    (D.nexp.Bsup (C.twI w) j b).map (IntegralHeckeForms.AO D.nexp (C.twI w) j b) ≤ D.nexp.Bsup (C.twI w) j b

def TorsionSectionsReflex (C : NChoice D) : Prop := ∀ i0 w, Over D i0 w → ∀ j ∈ lifts D, ∀ b : Bool,
  rkK (IntegralHeckeForms.Mall D.nexp (C.twI w) j b) =
      Module.finrank (FractionRing (D.ntw.O (C.twI w))) (IntegralHeckeForms.Fm0 D.nexp (C.twI w) j b) ∧
    rkK (Mj D (C.twI w) j b) = D.what₂.D0

def twistV0Submodule (C : NChoice D) (w : Pl D) (j : ℕ) (b : Bool) :
    Submodule (D.ntw.Ok (C.twI w) (C.k' w))
      (D.ntw.Ok (C.twI w) (C.k' w) ⊗[D.ntw.O (C.twI w)] D.nexp.Fm (C.twI w) j b) :=
  ((IntegralHeckeForms.V0 D.nexp (C.twI w) j b).restrictScalars (D.ntw.O (C.twI w))).baseChange (D.ntw.Ok (C.twI w) (C.k' w))

def adm7 : Prop := ∀ i0 w, Over D i0 w → ∀ j ∈ lifts D,
  (∀ b : Bool, IntegralHeckeForms.eThPMt D.nexp (nch.twI w) j b (nch.k' w) ∅ 1 ≤ twistV0Submodule D nch w j b ∧
    (D.what₂.Ij D.what₂.muStar j (plS nch w b) : ℝ) ≤
      (D.what₂.places.ramIdx (plS nch w b) : ℝ) * X.IsgBase w j b) ∧
  (TwistedAt D w →
    (∀ b : Bool, IntegralHeckeForms.eThPMt D.nexp (nch.twI w) j b (nch.k' w) (nch.Q w) (X.psiW w b) ≤ twistV0Submodule D nch w j b ∧
      (D.what₂.Ij (D.what₂.muTw w) j (plS nch w b) : ℝ) ≤
        (D.what₂.places.ramIdx (plS nch w b) : ℝ) * X.IsgTw w j b) ∧
    (D.what₂.jw (D.what₂.muTw w) j w : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * (D.what₂.etaJ j w : ℝ))

def SelfConjIdx : Prop :=
  ∀ w, TwistedAt D w → D.what₂.places.conj w = w → ∀ j ∈ lifts D,
    IntegralHeckeForms.eThPMt D.nexp (nch.twI w) j (!nch.sd w) (nch.k' w) (nch.Q w) (X.psiW w (!nch.sd w)) ≤ twistV0Submodule D nch w j (!nch.sd w) ∧
      X.IsgTw w j (!nch.sd w) = X.IsgTw w j (nch.sd w)

def adm8 : Prop := ∀ i0 w, Over D i0 w → TwistedAt D w →
  X.I.Ok (nch.twI w) ∧ TwGoodOne D X.I (nch.twI w) (nch.sd w) (nch.Q w) (nch.k' w) (nch.psi' w)

def adm9 : Prop := ∀ N (i : Fin 2) (y : (X.cm N i).Pt (X.cm N i).Xm) (La : (X.cm N i).Unim) (mm : ℕ),
  Nat.Coprime mm (D.host.g i) → ∀ γ : (X.cm N i).Th y La (mm ^ 2), (∃ k : ℕ, 0 < k ∧ γ ^ k = 1) →
    ∀ DF, (X.cm N i).jet y La (mm ^ 2) DF ((X.cm N i).act y La (mm ^ 2) γ ((X.cm N i).vth y La (mm ^ 2))) ∈
      (X.cm N i).intJet y La (mm ^ 2) DF

def adm10 : Prop :=
  (∀ i0 w, Over D i0 w → ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
    (∀ b : Bool, (D.nexp.Bsup (nch.twI w) j b).FG ∧ GStab (D.nexp.Bsup (nch.twI w) j b) ∧
      X.ThN w j h1 h2 b ≤ D.nexp.Bsup (nch.twI w) j b ∧
      IntegralHeckeForms.InclAt D.nexp (nch.twI w) j b (X.I.E.Dat0 (nch.twI w) j b) (nch.k' w) ∅ 1) ∧
    ∃ c : Bool → D.ntw.O (nch.twI w), (∀ b, c b ≠ 0) ∧
      (∑ b : Bool, vDv (D.ntw.O (nch.twI w)) (D.ntw.l (nch.twI w)) (c b)) = (Dpm D j : ℝ) ∧
      ∀ b, ∀ x ∈ psiPart (GSpan (X.ThN w j h1 h2 b)), ∃ z ∈ X.Th0 w j b,
        ((Nat.card D.nexp.U : ℕ) : D.ntw.O (nch.twI w)) • x = c b • z) ∧
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (i0 : Fin 2) la, X.laOver i0 la →
    ∀ F ∈ X.WWB j la (X.run j).wL (X.run j).n1 (X.run j).n2, ∃ s : 𝓞 X.B.KO, s ∉ la.asIdeal ∧
      s • F ∈ (X.W j h1 h2).WWc (X.run j).S.sW (X.run j).wL

def adm11 (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
  (X.run j).nW = (X.run j).n1 + (X.run j).n2 ∧
  (∀ i0, X.RangeB CRd i0 (X.run j).wL (X.run j).n1 (X.run j).n2 ∧ 2 * WeightAlgebra.DF (X.run j).ka + 2 < D.host.g i0 ∧
    X.cB CRd i0 j (WeightAlgebra.DF (X.run j).wL) (X.run j).nW ≤ WeightAlgebra.cc D L H.Cc H.Ac H.CRc (X.run j).wL ∧
    ∀ la, X.laOver i0 la →
      (X.run j).nus la = (eWL X.B.KO la : ℝ) * (WeightAlgebra.DF (X.run j).wL : ℝ) / ((D.host.g i0 : ℝ) - 1)) ∧
  ((∀ i0 la, X.laOver i0 la → ∀ y : (X.W j h1 h2).Pt la,
      (X.W j h1 h2).depth (X.run j).S.sW (X.run j).wL la y ≤
        (((X.run j).nus la + WeightAlgebra.cc D L H.Cc H.Ac H.CRc (X.run j).wL * (X.W j h1 h2).phiC la y : ℝ) : EReal)) →
    WeightAlgebra.Hyp L (X.W j h1 h2) H C2 A2 CR 0 CT (X.run j).S (X.run j).ka (X.run j).wL (X.run j).wF X.TO
      (X.run j).nP (X.run j).nW (X.run j).h0 (X.run j).nus)

def adm12 : Prop := Formalism.MainNotions.N.LocsCoverTw D

def admitted (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop :=
  adm1 D X ∧ adm2 D X ∧ adm3 D X ∧ adm3b D X CRd ∧ ArchimedeanSignatureMatching D L X H C2 A2 CR CT ∧ adm5 D nch ∧
    adm6 D nch ∧ TorsionSectionsReflex D nch ∧ adm7 D X ∧ adm8 D X ∧ adm9 D X ∧ adm10 D X ∧ adm11 D L X H C2 A2 CR CT CRd ∧
    adm12 D

def AdmLA : Prop := adm1 D X ∧ adm2 D X

def AdmLB (CRd : ℝ) : Prop := adm1 D X ∧ adm2 D X ∧ adm3 D X ∧ adm3b D X CRd

def AdmC : Prop := adm1 D X ∧ adm2 D X ∧ adm9 D X

def AdmA (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop :=
  adm3b D X CRd ∧ ArchimedeanSignatureMatching D L X H C2 A2 CR CT ∧ adm5 D nch ∧ adm6 D nch ∧ TorsionSectionsReflex D nch ∧ adm7 D X ∧ adm8 D X ∧
    adm10 D X ∧ adm11 D L X H C2 A2 CR CT CRd ∧ adm12 D

end admitted

section Conclusion₂

variable (D : D7) (L : SizeData₂ D) (EX : ErrX D) {nch : NChoice D} (X : Loc D nch)

def LemmaOneDefinite : Prop := ∀ N (i : Fin 2) (y : (X.cm N i).Pt (X.cm N i).Xm) (La : (X.cm N i).Unim)
  (s : (X.cm N i).Sn y La 1), (X.cmx N i).nrm y La 1 s ≤ 1 →
  ∀ γ : (X.cm N i).Th y La (D.host.g i * 1), (∃ k : ℕ, 0 < k ∧ γ ^ k = 1) →
    (X.cmx N i).inQQ y La (D.host.g i * 1) (Multiplicative.toAdd ((X.cm N i).ovr y La (D.host.g i * 1) γ)) →
    ∀ e : (X.cmx N i).Lt y La →₀ ℕ, 2 * e.degree + 2 < D.host.g i →
      ‖(X.cmx N i).nnOf (pib EX i) e * (X.cmx N i).evT y La 1 γ s (MvPolynomial.monomial e 1)‖ ≤ 1

def L2BoundAlt : Prop := ∀ (i : Fin 2) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (ζ : R),
  IsPrimitiveRoot ζ (D.host.g i) →
  ∀ φ : (Fin D.R.f × Fin n → ℚ_[D.host.g i]) → R,
    (∀ x, φ x ≠ 0 → ∀ a, ‖x a‖ ≤ 1) →
    (∀ (x : Fin D.R.f × Fin n → ℚ_[D.host.g i]) (z : Fin D.R.f × Fin n → ℤ_[D.host.g i]),
      φ (fun a => x a + (D.host.g i : ℚ_[D.host.g i]) * (z a : ℚ_[D.host.g i])) = φ x) →
    ∃ c : (Fin D.R.f × Fin n → ZMod (D.host.g i)) → R, ∀ x : Fin D.R.f × Fin n → ℚ_[D.host.g i],
      (D.host.g i : R) ^ (D.R.f * n) * φ x =
        open Classical in
        if h : ∀ a, ‖x a‖ ≤ 1 then
          ∑ y : Fin D.R.f × Fin n → ZMod (D.host.g i),
            c y * ζ ^ (∑ a, PadicInt.toZMod (⟨x a, h a⟩ : ℤ_[D.host.g i]) * y a).val
        else 0

def LemmaAGaloisBound : Prop :=
  (∀ d i, (X.gx d i).LemA ((EX.piG i : 𝓞 D.host.E) : D.host.E)) ∧ ∀ N i, (X.cmx N i).LemA (pib EX i)

def LemmaBWeightBound (CRd : ℝ) : Prop := ∀ (i : Fin 2) j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) la, X.laOver i la →
  ∀ (wt : WeightFamilies.Wt D j) (n1 n2 : ℕ), X.RangeB CRd i wt n1 n2 →
  ∀ y : (X.W j h1 h2).Pt la, ∃ F ∈ X.WWB j la wt n1 n2,
    (X.W j h1 h2).vAt la y ((X.W j h1 h2).inc wt F) ≤
      (((eWL X.B.KO la : ℝ) * (WeightAlgebra.DF wt : ℝ) / ((D.host.g i : ℝ) - 1) +
        X.cB CRd i j (WeightAlgebra.DF wt) (n1 + n2) * (X.W j h1 h2).phiC la y : ℝ) : EReal)

def errC : ℝ :=
  (D.R.f : ℝ) * ((D.R.m : ℝ) * (D.R.N D.R.m : ℝ) * ((D.R.N D.R.m : ℝ) + D.R.t) + (D.R.m : ℝ) ^ 3 * L.etaSz)

def Dpi (u : D.what₂.Word) (j : ℕ) : ℝ := ∑ τ : D.what₂.Tau, nuAbs D u j τ

def PropositionCLatticeBound (C1 C2 : ℝ) : Prop :=
  (∀ (i : Fin 2) w, Over D i w → ∀ u : D.what₂.Word, D.what₂.places.resChar w ≠ (D.mem u).A.T → ∀ μ : D.what₂.Tup,
    ∀ φ ∈ DV.MramL D u, ∀ F ∈ (D.what₂.Mtilde μ).carrier, ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u μ (D.jN u φ) F ∧
      (y = 0 ∨ -(∑ j ∈ lifts D, vNN EX i u j w) - C1 * errC D L ≤ vG D w y)) ∧
  (∀ (i : Fin 2) w, Over D i w → ∀ u : D.what₂.Word, D.what₂.places.resChar w ≠ (D.mem u).A.T → ∀ μ : D.what₂.Tup,
    ∀ φ ∈ DV.MramL D u, ∀ φ' ∈ DV.MramL D u, ∀ F ∈ (D.what₂.Mtilde μ).carrier, ∀ F' ∈ (D.what₂.Mtilde μ).carrier, ∀ y y' : D.what₂.LL,
      D.what₂.embLL y = D.what₂.perCol u μ (D.jN u φ) F → D.what₂.embLL y' = D.what₂.perCol u μ (D.jN u φ') F' →
      y ≠ 0 → y' ≠ 0 →
      -(∑ j ∈ lifts D, Dpi D u j) - C2 * errC D L ≤ vG D w y + vG D (D.what₂.places.conj w) y')

def JetConsequence (C1 C2 C3 : ℝ) : Prop :=
  (∀ (i : Fin 2) w, Over D i w → ∀ u : D.what₂.Word, D.what₂.places.resChar w ≠ (D.mem u).A.T → ∀ μ : D.what₂.Tup,
    ∀ φ ∈ DV.MramL D u, ∀ F ∈ (D.what₂.Mtilde μ).carrier, ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u μ (D.jN u φ) F ∧
      (y = 0 ∨ -(∑ j ∈ lifts D, vNN EX i u j w) - C1 * errC D L ≤ vG D w y)) ∧
  (∀ (i : Fin 2) w, Over D i w → ∀ u, ∀ j ∈ lifts D,
    vNN EX i u j w + vNN EX i u j (D.what₂.places.conj w) = Dpi D u j) ∧
  (∀ (i : Fin 2) w, Over D i w → ∀ u : D.what₂.Word, D.what₂.places.resChar w ≠ (D.mem u).A.T → ∀ μ : D.what₂.Tup,
    ∀ φ ∈ DV.MramL D u, ∀ φ' ∈ DV.MramL D u, ∀ F ∈ (D.what₂.Mtilde μ).carrier, ∀ F' ∈ (D.what₂.Mtilde μ).carrier, ∀ y y' : D.what₂.LL,
      D.what₂.embLL y = D.what₂.perCol u μ (D.jN u φ) F → D.what₂.embLL y' = D.what₂.perCol u μ (D.jN u φ') F' →
      y ≠ 0 → y' ≠ 0 →
      -(∑ j ∈ lifts D, Dpi D u j) - C2 * errC D L ≤ vG D w y + vG D (D.what₂.places.conj w) y') ∧
  (∀ u, ∀ j ∈ lifts D,
    (∀ τ, (∀ t : D.host.TT, (D.eTau τ : D.R.GG) ≠ D.R.tau1 t) →
      |nuAbs D u j τ - (D.R.k : ℝ) * wj D j τ| ≤ C3 * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz)) ∧
    (∀ τ (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t →
      |nuAbs D u j τ - ((L.aT t : ℝ) + ((D.R.k : ℝ) - 1) * wj D j τ)| ≤
        C3 * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz + L.sc.b' / L.sc.x)) ∧
    Dpi D u j ≤ (∑ t, (L.aT t : ℝ)) +
      ∑ τ, ((D.R.k : ℝ) * wj D j τ + C3 * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz)))

def rhsA (C : ℝ) (r : HeightOneSpectrum (𝓞 X.B.KO) → ℝ) (j : ℕ) (w : Pl D) : ℝ :=
  -((Dpm D j : ℝ)) * D.what₂.D0 + C * ((X.TO : ℝ) + D.R.f * (D.R.nV : ℝ) ^ 2) * D.what₂.D0 +
    (r (X.laK w) / (eWL X.B.KO (X.laK w) : ℝ) +
      r (X.laK (D.what₂.places.conj w)) / (eWL X.B.KO (X.laK (D.what₂.places.conj w)) : ℝ)) / delq D

def ConjugationNormInvariance (C : ℝ) : Prop := ∃ r : ℕ → HeightOneSpectrum (𝓞 X.B.KO) → ℝ,
  (∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), (∀ la, 0 ≤ r j la) ∧ Summable (fun la => r j la * lw X.B.KO la) ∧
    (∑' la, r j la * lw X.B.KO la) ≤
      (X.W j h1 h2).rk (X.run j).ka (X.B.Mlat j (X.run j).ka) * D.R.f * D.R.m * L.sc.b * L.de2) ∧
  ∀ (i : Fin 2) w, Over D i w →
    (∀ j ∈ lifts D, ((D.what₂.Ij D.what₂.muStar j w + D.what₂.Ij D.what₂.muStar j (D.what₂.places.conj w) : ℤ) : ℝ) ≤
      (D.what₂.places.ramIdx w : ℝ) * rhsA D X C (r j) j w) ∧
    (TwistedAt D w → ∃ ε : ℕ → ℝ, (∀ j, 0 ≤ ε j) ∧ (∑ j ∈ lifts D, ε j) ≤ (D.host.g i : ℝ) ^ (-2 : ℤ) ∧
      ∀ j ∈ lifts D,
        ((D.what₂.Ij (D.what₂.muTw w) j w + D.what₂.Ij (D.what₂.muTw w) j (D.what₂.places.conj w) : ℤ) : ℝ) ≤
          (D.what₂.places.ramIdx w : ℝ) * (rhsA D X C (r j) j w + ε j) ∧
        (AjMu D (D.what₂.muTw w) j w : ℝ) ≤
          (D.what₂.places.ramIdx w : ℝ) * (rhsA D X C (r j) j w + (D.what₂.etaJ j w : ℝ) + ε j))

def ThetaAdjointPositiveScalar (C : ℝ) : Prop := DV.KapDef D → ∀ j ∈ lifts D,
  |(Dpm D j : ℝ) - ∑ τ, ((D.R.k : ℝ) - 1) * wj D j τ| ≤
    C * D.R.f * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * L.etaSz + (D.R.k : ℝ) * ((D.R.N D.R.m : ℝ) + D.R.t))

def Conclusion₂ (CRd C1 C2 C3 CA CD : ℝ) : Prop :=
  LemmaOneDefinite D EX X ∧ L2BoundAlt D ∧ LemmaAGaloisBound D EX X ∧ LemmaBWeightBound D X CRd ∧ PropositionCLatticeBound D L EX C1 C2 ∧ JetConsequence D L EX C1 C2 C3 ∧
    ConjugationNormInvariance D L X CA ∧ ThetaAdjointPositiveScalar D L CD

def Stmt (H : WeightAlgebra.KHyp) (C2h A2 CR CT CRd C1 C2 C3 CA CD : ℝ) : Prop :=
  admitted D L X H C2h A2 CR CT CRd → Conclusion₂ D L EX X CRd C1 C2 C3 CA CD

def LemmasOneTwoAStatement : Prop := AdmLA D X → LemmaOneDefinite D EX X ∧ L2BoundAlt D ∧ LemmaAGaloisBound D EX X

def LemmaBStatementAlt (CRd : ℝ) : Prop := AdmLB D X CRd → LemmaBWeightBound D X CRd

def PropositionCStatement (C1 C2 C3 : ℝ) : Prop := AdmC D X → PropositionCLatticeBound D L EX C1 C2 ∧ JetConsequence D L EX C1 C2 C3

def IntegralityGoodReduction (H : WeightAlgebra.KHyp) (C2h A2 CR CT CRd CA : ℝ) : Prop :=
  AdmA D L X H C2h A2 CR CT CRd → LemmaBWeightBound D X CRd → ConjugationNormInvariance D L X CA

def KappaDegreeStatement (CD : ℝ) : Prop := ThetaAdjointPositiveScalar D L CD

end Conclusion₂

abbrev ObjClass : Type 1 := ∀ {D : D7} (_ : SizeData₂ D) (nch : NChoice D), Loc D nch → Prop

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.ex x hx i).nch)

def AdmF (H : WeightAlgebra.KHyp) (C2h A2 CR CRd : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    admitted (Fm.D x i) (Fm.L x i) (XF x hx i) H C2h A2 CR (Fm.Ct + 1) CRd

def OrbitValuationBound (CRd C1 C2 C3 CA CD : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    Conclusion₂ (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX (XF x hx i) CRd C1 C2 C3 CA CD

def AdmLAF : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, AdmLA (Fm.D x i) (XF x hx i)

def LemmasOneTwoAFamily : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    LemmaOneDefinite (Fm.D x i) (Fm.ex x hx i).errX (XF x hx i) ∧ L2BoundAlt (Fm.D x i) ∧
      LemmaAGaloisBound (Fm.D x i) (Fm.ex x hx i).errX (XF x hx i)

def AdmLBF (CRd : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, AdmLB (Fm.D x i) (XF x hx i) CRd

def LemmaBFamily (CRd : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, LemmaBWeightBound (Fm.D x i) (XF x hx i) CRd

def AdmCF : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, AdmC (Fm.D x i) (XF x hx i)

def familyJetConsequence (C1 C2 C3 : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    PropositionCLatticeBound (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1 C2 ∧ JetConsequence (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1 C2 C3

end Fam

def KudlaFamilyStatement (𝒪 : ObjClass) (H : WeightAlgebra.KHyp) (C2h A2 CR CRd C1 C2 C3 CA CD : ℝ) {eps : ℝ}
    (Fm : Formalism.MainNotions.FamP eps) (_CH : ℝ) : Prop :=
  ∀ XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.ex x hx i).nch,
    (∀ x hx i, 𝒪 (Fm.L x i) (Fm.ex x hx i).nch (XF x hx i)) →
    AdmF Fm XF H C2h A2 CR CRd → OrbitValuationBound Fm XF CRd C1 C2 C3 CA CD

def ClosedAbsoluteShare (𝒪 : ObjClass) (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∃ C1 C2 C3 CA CD : ℝ, Formalism.MainNotions.Closed 𝒞 (fun Fm CH => ∀ (H : WeightAlgebra.KHyp) (C2h A2 CR CRd : ℝ), 2 ≤ CRd →
    KudlaFamilyStatement 𝒪 H C2h A2 CR CRd C1 C2 C3 CA CD Fm CH)

def LemmasOneTwoAFamilyStatement (𝒪 : ObjClass) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (_CH : ℝ) : Prop :=
  ∀ XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.ex x hx i).nch,
    (∀ x hx i, 𝒪 (Fm.L x i) (Fm.ex x hx i).nch (XF x hx i)) → AdmLAF Fm XF → LemmasOneTwoAFamily Fm XF

def ClosedLemmasOneTwoA (𝒪 : ObjClass) (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  Formalism.MainNotions.Closed 𝒞 (fun Fm CH => LemmasOneTwoAFamilyStatement 𝒪 Fm CH)

def LemmaBFamilyStatement (𝒪 : ObjClass) (CRd : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (_CH : ℝ) : Prop :=
  ∀ XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.ex x hx i).nch,
    (∀ x hx i, 𝒪 (Fm.L x i) (Fm.ex x hx i).nch (XF x hx i)) → AdmLBF Fm XF CRd → LemmaBFamily Fm XF CRd

def ClosedLemmaB (𝒪 : ObjClass) (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  Formalism.MainNotions.Closed 𝒞 (fun Fm CH => ∀ CRd : ℝ, 2 ≤ CRd → LemmaBFamilyStatement 𝒪 CRd Fm CH)

def PropositionCFamily (𝒪 : ObjClass) (C1 C2 C3 : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (_CH : ℝ) : Prop :=
  ∀ XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.ex x hx i).nch,
    (∀ x hx i, 𝒪 (Fm.L x i) (Fm.ex x hx i).nch (XF x hx i)) → AdmCF Fm XF → familyJetConsequence Fm C1 C2 C3

def ClosedPropositionC (𝒪 : ObjClass) (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∃ C1 C2 C3 : ℝ, Formalism.MainNotions.Closed 𝒞 (fun Fm CH => PropositionCFamily 𝒪 C1 C2 C3 Fm CH)

end Formalism.MainNotions.LiftErrorLocal

end
