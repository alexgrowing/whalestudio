import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedOneSubLeOfMovesIdealCompletion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IpEqZeroOfHeisEigen

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valued_one_sub_le_of_moves_idealCompletion : ∀ {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E) (w : HeightOneSpectrum (𝓞 E)) (c : ℤ) (n : E)
  {a : ℕ} (H : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)), w.valuation E n = 1 → FractionalIdeal.count E w I = -c → 1 ≤ c →
  (∀ (s : FiniteAdeleRing (𝓞 E) E) (i j : Fin a), InHat I s → (∀ k, InHat I (s * H i k)) →
    InHat 1 (algebraMap E (FiniteAdeleRing (𝓞 E) E) n * (s * (1 - H) i j))) →
  ∀ i j, Valued.v ((1 - H) i j w) ≤ WithZero.exp (-c) := by
  first | exact @GlobalTheory.CosetOrth.valued_one_sub_le_of_moves_integral | exact GlobalTheory.CosetOrth.valued_one_sub_le_of_moves_integral | (intros; apply GlobalTheory.CosetOrth.valued_one_sub_le_of_moves_integral <;> assumption)
