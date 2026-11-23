import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.RSJ

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E) in

def pFin : Ad E →+* Af E := RingHom.snd (InfiniteAdeleRing E) (Af E)

def secRow {R : Type*} [CommRing R] (y : Fin a → R) : Matrix (Fin a) (Fin a) R :=
  Matrix.of fun i j => if (i : ℕ) + 1 = a then y j else (1 : Matrix (Fin a) (Fin a) R) i j

open Classical in

def secInv (y : Fin a → Cinf E) : GL (Fin a) (Cinf E) :=
  if h : IsUnit (secRow y).det then (Matrix.nonsingInvUnit (secRow y) h)⁻¹ else 1

def rowAct (ξ : Fin a → E) (g : GA E a) : Fin a → Ad E :=
  Matrix.vecMul (fun i => algebraMap E (Ad E) (ξ i)) (g : Matrix (Fin a) (Fin a) (Ad E))

variable (E) in

def natLat (N : ℕ) : Set (Af E) :=
  {x | ∃ z : Af E, (∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) ∧ x = (N : Af E) * z}

open Classical in

def indN (N : ℕ) (y : Fin a → Af E) : ℂ :=
  if ∀ i : Fin a, y i - (if (i : ℕ) + 1 = a then 1 else 0) ∈ natLat E N then 1 else 0

variable (E a) in

def detPow (x : ℝ) (g : GA E a) : ℝ := ‖((chiDet a (GlobalTheory.HeckeGal.Model.absPow E x) g : ℂˣ) : ℂ)‖

def Psi (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (N : ℕ) (g : GA E a) (y : Fin a → Ad E) : ℂ :=
  φ (g * infGL E a (secInv fun i => pInf E (y i))) * starRingEnd ℂ (φ' (g * infGL E a (secInv fun i => pInf E (y i)))) *
    Φ (fun i => pInf E (y i)) * indN N (fun i => pFin E (y i))

def thetaSum (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (N : ℕ) (g : GA E a) : ℂ :=
  ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, Psi φ φ' Φ N g (rowAct ξ.1 g)

def Zint (μ : Measure (GA E a)) (𝓕 : Set (GA E a)) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∫ g in 𝓕, thetaSum φ φ' Φ N g * (detPow E a x g : ℂ) ∂μ

end GlobalTheory.RSJ
