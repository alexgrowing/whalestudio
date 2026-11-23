import Mathlib

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

open MeasureTheory
open scoped Matrix ComplexConjugate

def hermC (n : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) ℂ) := selfAdjoint _

theorem mem_hermC {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} : b ∈ hermC n ↔ b.IsHermitian := by
  unfold hermC
  rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
  exact Iff.rfl

theorem isClosed_hermC (n : ℕ) : IsClosed (hermC n : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hset : (hermC n : Set (Matrix (Fin n) (Fin n) ℂ)) = {b | star b = b} := rfl
  rw [hset]
  exact isClosed_eq continuous_star continuous_id

instance measHermC (n : ℕ) : MeasurableSpace (hermC n) := borel _

instance borelHermC (n : ℕ) : BorelSpace (hermC n) := ⟨rfl⟩

instance locCompactHermC (n : ℕ) : LocallyCompactSpace (hermC n) :=
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  (isClosed_hermC n).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance secondCountableHermC (n : ℕ) : SecondCountableTopology (hermC n) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _

def detW {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) : ℝ := (Matrix.det (1 + b * b)).re

def gramC {n M : ℕ} (J : Matrix (Fin M) (Fin M) ℂ) (X : Fin n → Fin M → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun a c => ∑ i, ∑ j, conj (X a i) * J i j * X c j

def phaseM {W : Type} [Fintype W] {n M : ℕ} (J : W → Matrix (Fin M) (Fin M) ℂ)
    (B : W → Matrix (Fin n) (Fin n) ℂ) (X : W → Fin n → Fin M → ℂ) : ℝ :=
  ∑ w, (Matrix.trace (B w * gramC (J w) (X w))).re

def coreC {W : Type} [Fintype W] {n M : ℕ} (J : W → Matrix (Fin M) (Fin M) ℂ)
    (μ : Measure (W → Fin n → Fin M → ℂ)) (g : (W → Fin n → Fin M → ℂ) → ℂ) (b : W → hermC n) : ℂ :=
  ∫ X, g X * Complex.exp (2 * Real.pi * Complex.I *
    ((phaseM J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) X : ℝ) : ℂ)) ∂μ

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
