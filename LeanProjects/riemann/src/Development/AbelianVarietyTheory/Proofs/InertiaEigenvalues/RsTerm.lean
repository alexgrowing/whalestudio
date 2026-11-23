import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def rsTerm {a b : ℕ} (σ : CG E a) (σ' : CG E b) (x : ℝ) (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : ℂ :=
  ((sat σ w).map fun α => (α : ℂ) ^ (r + 1)).sum * ((sat σ' w).map fun β => (starRingEnd ℂ (β : ℂ)) ^ (r + 1)).sum *
    (Ideal.absNorm w.asIdeal : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1)

def logRS (T : Finset (HeightOneSpectrum (𝓞 E))) {a b : ℕ} (σ : CG E a) (σ' : CG E b) (x : ℝ) : ℂ :=
  ∑' p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ, rsTerm σ σ' x p.1.1 p.2

end GlobalTheory.JSW
