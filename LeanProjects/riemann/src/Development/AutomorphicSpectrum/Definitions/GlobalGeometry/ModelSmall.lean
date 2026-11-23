import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Plug

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CompanionTheory.Ar.Rec

attribute [-instance] GlobalTheory.CompHt.fintypePsi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def reW (u : GlobalTheory.AllWt.Weight Dw) : Top.Wt (CMType H) (Dw.p + Dw.q) := fun τ i => (u τ i : ℝ)

def nOf (u : GlobalTheory.AllWt.Weight Dw) : Option (RootIx Dw) → ℤ
  | some r => -u r.1 r.2
  | none => 0

def degOf (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (u : GlobalTheory.AllWt.Weight Dw) : RM.K → ℤ :=
  (Top.combLine (RM.line 1) (nOf u)).a

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}

def HodgeLe (Or : RootOrigin Y S RM Fx) (u : GlobalTheory.AllWt.Weight Dw) (s : RM.Ω) (R : ℝ) : Prop :=
  ∃ w : MRing RM.ι, Small.IsFormOff (mCoordIdeal RM.y) w ∧ ∀ z ∈ mcPts (mCoordIdeal RM.y), MvPolynomial.aeval z w ≠ 0 →
    Small.ValLe RM.y (degOf RM u) s z (R * ∏ r, (Or.sing r).h z ^ nOf u (some r))

def modelSmall (Or : RootOrigin Y S RM Fx) (u : GlobalTheory.AllWt.Weight Dw) (R : ℝ) : Set RM.Ω :=
  {s | s ∈ chartLatNm RM.y (degOf RM u) 1 ∧ HodgeLe Or u s R}

variable {Or : RootOrigin Y S RM Fx} {Fr : Small.GenFrame Or} {h : GenFrEx Xo c} {Z : Comp Xo c}

def gauge (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw) : RM.Ω :=
  ((∏ i, Rd.t i ^ Rec.exZ Dw (GlobalTheory.AllWt.wtOf Dw u 0).1 i : (RM.Ω)ˣ) : RM.Ω) * ∏ r, Or.e r ^ (-nOf u (some r))

def trOf (Rd : Reading Fr h Z) (u : GlobalTheory.AllWt.Weight Dw) (s : RM.Ω) : Om Z :=
  letI := Rd.φ.toAlgebra
  Algebra.trace (Om Z) RM.Ω (s / gauge Rd u)

variable (E) in

def exTwo (p : ℕ) : ℝ := GlobalTheory.CovHt.htEx E p + if p = 2 then 1 else 0

variable (l) in

def costTwo (B : ℝ) : ℝ := ∑ᶠ p ∈ GlobalTheory.CompHt.htPrimes l B, exTwo E p * Real.log p

variable (Xo c) in

def HTLow : Prop := ∀ (p : ℕ) (la : HeightOneSpectrum (𝓞 c.F)), p.Prime → ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal →
  ∀ w ∈ (GlobalTheory.CompHt.htVals Xo c).1 la, ∃ v ∈ (GlobalTheory.CompHt.recVals Xo c).1 la, ∀ (u : GlobalTheory.AllWt.Weight Dw),
    ∀ f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0),
      v f ≤ w f + (((vLa la (p : c.F) : ℝ) * exTwo E p * GlobalTheory.CovHt.l1 u : ℝ) : EReal)

def DeepStR : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → D.R.m ^ 2 ≤ D.R.k → ∀ j : ℕ, 1 ≤ j → j < D.R.m →
  ∀ (Y : GlobalTheory.CovTop.Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o →
    Y.d.l₂.M'.primeFactors.card ≤ 15 →
      GlobalTheory.CovHt.MeanAll Y.U (xiR D) (GlobalTheory.CovHt.ell D) C

end GlobalTheory.CompanionTheory.Ar.Plug
