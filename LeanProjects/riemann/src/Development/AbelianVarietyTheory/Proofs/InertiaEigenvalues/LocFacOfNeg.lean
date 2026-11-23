import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCell

def sphZ (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (ν : Fin n → ℤ) : ℂ :=
  if Antitone ν then GlobalTheory.JSW.sphW q α (fun i => (ν i).toNat) else 0

def locFac (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) (ν : Fin n → ℤ) : ℝ≥0∞ :=
  if Antitone ν ∧ ∀ i, 0 ≤ ν i then
    ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (fun i => (ν i).toNat) α‖ ^ 2 *
      (q : ℝ) ^ (-(((∑ i, (ν i).toNat : ℕ) : ℝ) * x)))
  else 0

def cellProd {E : Type} [Field E] [NumberField E] {n : ℕ} (T : Finset (HeightOneSpectrum (𝓞 E)))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin n → ℂ) (x : ℝ)
    (ν : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) : ℝ≥0∞ :=
  ∏ w ∈ ν.support, if h : w ∈ T then 1 else locFac (Ideal.absNorm w.asIdeal) (α ⟨w, h⟩) x (ν w)

def bInt {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (ℓ : Fin a) (F : GA E a → ℂ)
    (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (x : ℝ) (g : GA E a) : ℝ≥0∞ :=
  ‖GlobalTheory.RSTheta.rsPsi ℓ (GlobalTheory.JSW.whit F) (GlobalTheory.JSW.whit F) Φ J η g (g.val ℓ)‖ₑ *
    ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x)

theorem locFac_zero (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) : locFac q α x 0 = 1 := by
  have h : (fun i : Fin n => ((0 : Fin n → ℤ) i).toNat) = fun _ => 0 := funext fun _ => rfl
  rw [locFac, if_pos (show Antitone (0 : Fin n → ℤ) ∧ ∀ i, (0 : ℤ) ≤ (0 : Fin n → ℤ) i from ⟨fun _ _ _ => le_rfl, fun _ => le_rfl⟩), h]
  simp [GlobalTheory.JSW.schurAt, GlobalTheory.JSW.schur_zero]

theorem locFac_of_neg (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) {ν : Fin n → ℤ} {i : Fin n} (h : ν i < 0) :
    locFac q α x ν = 0 := by
  rw [locFac, if_neg fun h' => absurd (h'.2 i) (not_le.2 h)]

example {E : Type} [Field E] [NumberField E] {n : ℕ} (T : Finset (HeightOneSpectrum (𝓞 E)))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin n → ℂ) (x : ℝ) : cellProd T α x 0 = 1 := by
  simp [cellProd]

end GlobalTheory.RSCell
