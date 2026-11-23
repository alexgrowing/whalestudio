import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet
import GroundTheory.AutomorphicForms.FourierWhittaker

noncomputable section

open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def whit (F : GA E a → ℂ) (g : GA E a) : ℂ := GroundTheory.Automorphic.FourierWhittaker.whittaker F g

variable (E a) in

def NA : Set (GA E a) :=
  {u | (∀ i j : Fin a, j < i → (u : Matrix (Fin a) (Fin a) (Ad E)) i j = 0) ∧ ∀ i, (u : Matrix (Fin a) (Fin a) (Ad E)) i i = 1}

def psiN (u : GA E a) : ℂ := (GroundTheory.Global.adelicChar E (GlobalTheory.Whittaker.superDiag u) : ℂ)

variable (E a) in

def supS (S : Finset (HeightOneSpectrum (𝓞 E))) : Set (GA E a) :=
  {g | ∀ w ∉ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1}

variable (E) in

def mirS (S : Finset (HeightOneSpectrum (𝓞 E))) (m : ℕ) : Set (GA E (m + 1)) :=
  supS E (m + 1) S ∩ {g | ∀ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j = if j = Fin.last m then 1 else 0}

def diagPow {K : Type} [CommRing K] {n : ℕ} (ϖ : Kˣ) (l : Fin n → ℕ) : GL (Fin n) K :=
  Units.map (Matrix.diagonalRingHom (Fin n) K).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ l i)

def tl (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ)) : GA E a :=
  (l.support.toList.map fun w => finGL E a (locGL E a w (diagPow (ϖ w) (l w)))).prod

def IsRapidInf {X : Type} [MeasurableSpace X] (ν : MeasureTheory.Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) : Prop :=
  Measurable k ∧ Measurable (fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) ∧
    ∀ N : ℕ, MeasureTheory.Integrable (fun x => ‖k x‖ * height (γ x) ^ N) ν

def mspanR [IsTotallyComplex E] (π : CuspSub E a) : Submodule ℂ (GA E a → ℂ) :=
  sInf {S | (∀ φ ∈ π.V, φ.1 ∈ S) ∧ (∀ F ∈ S, ∀ h : GA E a, (fun g => F (g * h)) ∈ S) ∧
    ∀ F ∈ S, ∀ (X : Type) (_ : MeasurableSpace X) (ν : MeasureTheory.Measure X) (_ : MeasureTheory.SFinite ν) (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → (fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) ∈ S}

def psiLoc (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) : ℂ := (GroundTheory.Global.adelicChar E (sFin E (sLoc E w x)) : ℂ)

end GlobalTheory.JSW
