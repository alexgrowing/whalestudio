import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG

namespace GlobalTheory.RSNonvan

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def lfac {a b : ℕ} (σ : CG E a) (σ' : CG E b) (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) : ℂ :=
  locL (Ideal.absNorm w.asIdeal) (sat σ w) ((sat σ' w).map (Units.map (starRingEnd ℂ).toMonoidHom)) s

def IsGood (T : Finset (HeightOneSpectrum (𝓞 E))) : Prop :=
  (∀ w ∈ T, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ T) ∧
    ∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w

def dcoef {a b : ℕ} (σ : CG E a) (σ' : CG E b) (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : ℝ :=
  ‖(((sat σ w).map (fun α : ℂˣ => (α : ℂ)) + (sat σ' w).map (fun α : ℂˣ => (α : ℂ))).map (· ^ (r + 1))).sum‖ ^ 2 /
    ((r : ℝ) + 1)

def dexp (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : ℝ := ((r : ℝ) + 1) * Real.log (Ideal.absNorm w.asIdeal)

theorem dcoef_nonneg {a b : ℕ} (σ : CG E a) (σ' : CG E b) (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) :
    0 ≤ dcoef σ σ' w r := div_nonneg (sq_nonneg _) (by positivity)

theorem dexp_nonneg (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) : 0 ≤ dexp w r :=
  mul_nonneg (by positivity) (Real.log_nonneg (by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm w
    exact_mod_cast this.le))

end GlobalTheory.RSNonvan
