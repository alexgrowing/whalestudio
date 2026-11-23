import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameGlue

open GlobalTheory.Cartier

variable {X : Scheme.{0}} [IsIntegral X]

def ModPFrames (p : ℕ) {ι : Type} {N : ℕ} (U : ι → X.Opens) (M : ι → Matrix (Fin N) (Fin N) X.functionField)
    (c : ι → Fin N → X.functionFieldˣ) : Prop :=
  (∀ x : X, ¬ IsUnit (p : X.presheaf.stalk x) → ∃ a, x ∈ U a) ∧
  (∀ a, ∀ x ∈ U a, ¬ IsUnit (p : X.presheaf.stalk x) → (∀ i k, RegAt x (M a i k)) ∧ UnitAt x (M a).det) ∧
  ∀ a b, ∀ x ∈ U a, x ∈ U b → ¬ IsUnit (p : X.presheaf.stalk x) → ∀ i,
    UnitAt x ((c a i / c b i : X.functionFieldˣ) : X.functionField) ∧
    (∀ k, k < i → ZeroAt x (((M a)⁻¹ * M b) i k)) ∧
    ZeroAt x (((M a)⁻¹ * M b) i i - ((c a i / c b i : X.functionFieldˣ) : X.functionField))

def PowOfFrames (p : ℕ) {ι : Type} (U : ι → X.Opens) (c : ι → X.functionFieldˣ) (m : ℕ) (L : LB X) : Prop :=
  ∃ s : L.ι → X.functionFieldˣ, IsRatSec L s ∧ ∀ a k, ∀ x ∈ U a, x ∈ L.U k → ¬ IsUnit (p : X.presheaf.stalk x) →
    UnitAt x ((s k / c a ^ m : X.functionFieldˣ) : X.functionField)

end GlobalTheory.FrameGlue

end
