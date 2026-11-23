import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.Divisibility.FamilyThetaDenominatorValues
import Formalism.SharpRestriction.Divisibility.CanonicalTranslateJets
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
import Formalism.SharpRestriction.Divisibility.AdmissibleRank.FreeFamilyOfLeavesAndAdmissible

noncomputable section

namespace Formalism.MainNotions.IsotypicCorollary

open Formalism.BasicNotions Formalism.BasicNotions.DV

section TypeMultiplicityNumbers₂

variable (D : D7)

def TypeMultiplicityNumbers : Prop :=
  ∃ X : WeightDegreeSizes.LocE D, WeightDegreeSizes.SmallLevelExtremalVectors D X ∧ WeightDegreeSizes.HolomorphicLowestVectors D X ∧ WeightDegreeSizes.MultiplicityTransfer D X

def IsotypicRank : Prop := Rows.IsotRank D.what₂

def IsotypicPartsInternal : Prop := Rows.IsotInternal D.what₂

def GoodPartRankSmallLevel (C : NChoice D) : Prop :=
  ∀ w : LiftErrorLocal.Pl D, ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool, ThetaNormsAndLinks.dG D (C.twI w) j b = D.what₂.D0

def Stmt : Prop := TypeMultiplicityNumbers D ∧ IsotypicPartsInternal D ∧ ∀ C : NChoice D, GoodPartRankSmallLevel D C

theorem goodPartRank_of_corollary (h : Stmt D) (C : NChoice D) : ThetaNormsAndLinks.EqualGoodMultiplicities D C := h.2.2 C

end TypeMultiplicityNumbers₂

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def KudlaFamilyStatement : Prop := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Stmt (Fm.D x i)

end Family

section Part₂

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.ThetaNormsAndLinks

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)

def IntegralityAtPrimesOverTwiceDiscriminant : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) la,
  laDiv X (2 * (NumberField.discr D.host.E).natAbs) la → Int4 X j h1 h2 la

def ScaledGeneratorRegularity (H : WeightAlgebra.KHyp) : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
  (∀ la, 0 ≤ (X.run j).nus la) ∧ (Function.support (X.run j).nus).Finite ∧
  (∑ᶠ la, |(X.run j).nus la| * (X.W j h1 h2).lN la) ≤ WeightAlgebra.PN D L * (X.run j).wL.size ∧
  ∀ la, (∀ i0, ¬ X.laOver i0 la) → ∀ y : (X.W j h1 h2).Pt la,
    (X.W j h1 h2).depth (X.run j).S.sW (X.run j).wL la y ≤
      (((X.run j).nus la + WeightAlgebra.cc D L H.Cc H.Ac H.CRc (X.run j).wL * (X.W j h1 h2).phiC la y : ℝ) : EReal)

end Part₂

section PartDep

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.PDVN

variable {D : D7} (L : SizeData₂ D) {CH : NChoice D} {Xd : DivX D} (O : ONObj D CH Xd)

def DepthOffTypePrimes (C6 Cd : ℝ) : Prop := OrbitContentCond O C6 →
  ∃ er : ℕ → ℕ → ℝ, (∀ j l, 0 ≤ er j l) ∧
    (∀ j ∈ SizeData₂.lifts D, ∀ S : Finset ℕ, ∑ l ∈ S, Real.log (l : ℝ) * er j l ≤ onBoundJ D L Cd) ∧
    (∀ w, OffG D w → TwistedAt D w → D.what₂.places.resChar w ≠ D.host.pde → DepAt O.X L O.T er w) ∧
    ∀ w, OffG D w → TwistedAt D w → D.what₂.places.resChar w = D.host.pde → DepAt O.X' L O.T er w

end PartDep

section ThetaIntegrality₂

open NumberField Classical Formalism.MainNotions.CanonicalTranslateJets

def ThetaIntegrality (D : D7) (X : DivX D) (G : CanonicalTranslateJets.Loc D X) : Prop :=
  ∀ w i, overG D w i → ∀ j, InR D j → ∀ (y : G.Pt j w) La,
    G.Th j w y La ∈ G.intS j w y La ∧
    (∀ s ∈ G.intS j w y La, ∀ b (γ : G.TG j w y La b),
      G.act j w y La b γ (G.pull j w y La s) ∈ G.intSG j w y La) ∧
    (∀ h ∈ G.intSG j w y La, ∀ Dg P, P ∈ G.intP j w → HarmHom G j Dg P →
      (∑ τ, Dg τ) + 1 < D.host.g i → ‖G.jetG j w y La h P‖ ≤ 1)

end ThetaIntegrality₂

section PartDV20

open Formalism.BasicNotions.TH NumberField IsDedekindDomain Finset MeasureTheory Classical Formalism.MainNotions.InnerProductFormulaField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ChainZetaFactorsAndLowerThetaVanishing (D : D7) (T : ThetaX D) (A : TH.ProvA) (X : InnerProductFormulaField.Loc D) : Prop :=
  Formalism.MainNotions.ZetaProductPairs.WtHyp T →
    (∀ j, 1 ≤ j → j ≤ D.R.m →
      ∃ z : D.what₂.Tau → ℂ, (∀ τ, IsARZ A (z τ)) ∧ ((X.ZChR j : ℝ) : ℂ) = ∏ τ, z τ) ∧
    (∀ j, 1 ≤ j → j ≤ D.R.m → 0 < X.ZSbR j ∧ 0 < X.nT j) ∧
    (∀ (μ : D.what₂.Tup) (i l : ℕ), i < D.R.m → 1 ≤ l → l ≤ (sigYD D.R (i + 1)).2 →
      ∀ (Φ : T.Sch (D.sp.Y i) (T.YsLow D.R.t (i + 1) l)) (G : T.cusp (D.sp.Y i)), IsTypeD T i G →
        thS T μ i _ Φ G = 0)

end PartDV20

section ThetaPathData

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.AbsolutelyIrreducibleSpan

def GivenThetaPathData (D : D7) {V : AbsolutelyIrreducibleSpan.Lev D} {A : AmbForm D V.S} (X : AbsolutelyIrreducibleSpan.LocV D V A) (C : ℝ) : Prop :=
  (∀ μ, AbsolutelyIrreducibleSpan.Used D μ → ∀ Φ, X.T0 μ Φ ∈ X.Good μ hBot ∧
    ∀ F ∈ V.S.V0 μ, X.ev μ hBot (X.T0 μ Φ) F = X.rowUp Φ D.R.m (X.real (V.S.iota μ F))) ∧
  (∀ w Φ, X.T0 (D.what₂.muAt w) Φ ∈ X.IntAt (D.what₂.muAt w) hBot w 0) ∧
  (∀ v Φ, X.T0 D.what₂.mu0 Φ ∈ X.SzAt D.what₂.mu0 hBot v (C * (D.R.m : ℝ) * (X.Nst : ℝ) ^ 2 * X.weightedLogLevelSum))

end ThetaPathData

section ThetaCommutingSquare₂

open Formalism.MainNotions.DIV

def ThetaCommutingSquare {D : D7} {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} (T : ThetaX D) (Lc : Formalism.MainNotions.KudlaSiegelWeil.Loc D T)
    (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) : Prop :=
  ∀ μ, Formalism.MainNotions.AbsolutelyIrreducibleSpan.Used D μ → ∀ h i, Formalism.MainNotions.AbsolutelyIrreducibleSpan.IsPath D.R.m h → Formalism.MainNotions.AbsolutelyIrreducibleSpan.Flippable D.R.m h i →
    4 * D.R.m + 2 < D.R.t + X.s → 2 * D.R.m + 1 < D.R.r + h i * D.R.t + i * X.s →
    (∀ τ (hj : h i < D.R.m), ((2 * (D.R.r + h i * D.R.t + i * X.s) + D.R.t + X.s : ℕ) : ℚ) <
      2 * ((D.hc τ).e ⟨h i, hj⟩ + X.cInf (D.R.m - i) τ)) →
    ∃ Q : SqSett T Lc X μ i (h i), Q.SeeSaw h

end ThetaCommutingSquare₂

end Formalism.MainNotions.IsotypicCorollary
