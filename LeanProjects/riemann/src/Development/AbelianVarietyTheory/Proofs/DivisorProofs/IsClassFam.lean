import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateFieldBounds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TauPlBijective

noncomputable section

namespace GlobalTheory.ColumnNormCompare

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

@[reducible] def numDatumOfParameters (D : D7) (large₂ : SizeData₂ D) : NumDatum where
  R := D.R
  sc := large₂.sc
  H := D.host.toHostAx
  g := D.host.g
  g_prime := D.host.g_prime
  TT := D.host.TT
  Del := ⌊D.s.Del⌋₊
  h0 := ⌈LevelStarExponents.h0 large₂⌉₊
  hc := fun z => D.hc (tauPl D z)

def plRec (D : D7) : RPl D.R ≃ D.what₂.Tau := GlobalTheory.InertCompare.plEquiv D

def codeRec {D : D7} (large₂ : SizeData₂ D) (u : D.what₂.Word) : Code (numDatumOfParameters D large₂) := D.s.letter u

def PageRows {D : D7} (large₂ : SizeData₂ D) (EX : ErrX D) : Prop :=
  (∃ n : ℕ, D.s.Del = n) ∧ (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧ (recPrimes EX).PiGCong

def IsClassFam {G K : Type} [Group G] (Xg : Finset (G → K)) : Prop := ∀ χ ∈ Xg, ∀ s t : G, χ (s * t) = χ (t * s)

section Rec

variable {D : D7} (large₂ : SizeData₂ D) {EX : ErrX D} (Ch : Chars (recFields D) (recPrimes EX) D.R.m)
  (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (eta : Formalism.L2.Host.HChar D.host.E)
  (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))

def Common : Prop :=
  BadPrimesPeriodBound.HostTie EX ∧ BadPrimesPeriodBound.CharTie Ch mu0 eta sel ∧ ConjugateFieldBounds.ParamHyp large₂ EX 25 ∧ PageRows large₂ EX

end Rec

end GlobalTheory.ColumnNormCompare
