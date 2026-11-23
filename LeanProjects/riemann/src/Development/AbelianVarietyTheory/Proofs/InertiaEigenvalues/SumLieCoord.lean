import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def kerOp {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (F : GA E a → ℂ) :
    GA E a → ℂ := fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν

structure IsBCC (F : GA E a → ℂ) : Prop where
  cont : Continuous F
  bdd : ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C
  cusp : IsCuspidal F
  left : ∀ γ g, F (ratGL E a γ * g) = F g

variable (E a) in

def lieBasis : Module.Basis (Fin (Module.finrank ℝ (Lie E a))) ℝ (Lie E a) := Module.finBasis ℝ (Lie E a)

variable (E a) in

def lieCoord (i : Fin (Module.finrank ℝ (Lie E a))) : Lie E a →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap ((lieBasis E a).coord i))

def adCoef (γ : GL (Fin a) (Cinf E)) (p : Fin (Module.finrank ℝ (Lie E a)) × Fin (Module.finrank ℝ (Lie E a))) : ℂ :=
  lieCoord E a p.1 (toL ((γ⁻¹).val * Matrix.of (lieBasis E a p.2) * γ.val))

theorem sum_lieCoord (X : Lie E a) : ∑ i, ((lieBasis E a).coord i X) • lieBasis E a i = X :=
  (lieBasis E a).sum_repr X

end GlobalTheory.JSW
