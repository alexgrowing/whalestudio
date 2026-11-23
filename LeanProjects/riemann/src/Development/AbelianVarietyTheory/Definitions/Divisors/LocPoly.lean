import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
import GroundTheory.AutomorphicForms.ReductionSplitting
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaPair

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Polynomial GroundTheory.Automorphic UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin)
open UpperTheory.V.TR (Rinf Lie chart infGL pInf toL rmul invSet CuspSub)
open scoped ContDiff

namespace GlobalTheory.HenQ

section Fin

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

abbrev gFin (g : GA K n) : GL (Fin n) (Af K) := GeneralLinearGroup.map (pFin K) g

def absDet (g : GA K n) : ℝ := (Reduction.detModule K n g : ℝ)

def IntAt (w : HeightOneSpectrum (𝓞 K)) (k : GL (Fin n) (Af K)) : Prop := ∀ i j, (GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc K w) k).val i j ∈ Formalism.UG.Ov K w

def UnitOff (S : Set (HeightOneSpectrum (𝓞 K))) (k : GL (Fin n) (Af K)) : Prop := ∀ w ∉ S, GeneralLinearGroup.map (GlobalTheory.CuspRep.pLoc K w) k ∈ GlobalTheory.LFun.KGL w n

def SphOff (S : Set (HeightOneSpectrum (𝓞 K))) (Ψ : GA K n → ℂ) : Prop :=
  ∀ w ∉ S, (∀ g, Ψ g ≠ 0 → IntAt w (gFin g)) ∧
    ∀ g y, IntAt w (gFin g) → IntAt w (gFin g * locGL K n w y) → Ψ (g * finGL K n (locGL K n w y)) = Ψ g

def Shell (w : HeightOneSpectrum (𝓞 K)) (n k : ℕ) : Set (GL (Fin n) (w.adicCompletion K)) :=
  {y | (∀ i j, y.val i j ∈ Formalism.UG.Ov K w) ∧ ‖y.val.det‖ = ((Ideal.absNorm w.asIdeal : ℝ) ^ k)⁻¹}

def locPoly (B : Multiset ℂˣ) : ℂ[X] := (B.map fun b => (1 - C (b : ℂ) * X : ℂ[X])).prod

end Fin

section Inf

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def detAt (v : InfinitePlace K) (x : Lie K n) : ℝ := (Matrix.of x).det v

def detWt (u : InfinitePlace K → ℂ) (x : Lie K n) : ℂ := ∏ v, ((|detAt v x| : ℝ) : ℂ) ^ u v

open Classical in

def pdL (v : InfinitePlace K) (i j : Fin n) (F : Lie K n → ℂ) (x : Lie K n) : ℂ :=
  fderiv ℝ F x (toL (Matrix.single i j (Pi.single v 1)))

open Classical in

def rdL (v : InfinitePlace K) (i j : Fin n) (F : Lie K n → ℂ) (x : Lie K n) : ℂ :=
  fderiv ℝ F x (rmul (toL (Matrix.single i j (Pi.single v 1))) x)

def detD (v : InfinitePlace K) (F : Lie K n → ℂ) (x : Lie K n) : ℂ :=
  ∑ p : Equiv.Perm (Fin n), (((Equiv.Perm.sign p : ℤˣ) : ℤ) : ℂ) * (List.finRange n).foldr (fun j G => pdL v (p j) j G) F x

def detDD (F : Lie K n → ℂ) : Lie K n → ℂ :=
  (Finset.univ : Finset (InfinitePlace K)).toList.foldr (fun v G => detD v (detD v G)) F

def IsTest (Φ : Lie K n → ℂ) : Prop := ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ invSet K n

def fourL (Φ : Lie K n → ℂ) (y : Lie K n) : ℂ := ∫ x, Φ x * (Real.fourierChar (-∑ v, (Matrix.of x * Matrix.of y).trace v) : ℂ)

variable [IsTotallyReal K]

def mInf (g : GA K n) : Lie K n := toL (GeneralLinearGroup.map (pInf K) g).val

def tens (Φ : Lie K n → ℂ) (Ψ : GL (Fin n) (Af K) → ℂ) (g : GA K n) : ℂ := Φ (mInf g) * Ψ (gFin g)

end Inf

def zInt {K : Type} [Field K] [NumberField K] {n : ℕ} (Ψ f : GA K n → ℂ) (s : ℂ) (g : GA K n) : ℂ :=
  Ψ g * f g * ((absDet g : ℝ) : ℂ) ^ (s + ((n : ℂ) - 1) / 2)

end GlobalTheory.HenQ
