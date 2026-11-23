import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ConeWeightsNotSecondType

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgBcC.Real

variable {n : ℕ}

def domC (x : Fin n → ℝ) : Fin n → ℝ := x ∘ Tuple.sort (fun a => -x a)

def spinSq (ν : Fin n → ℝ) : ℝ := nsq (domC (ν - rhoV n) + rhoV n)

def LSq (lam : Fin n → ℤ) : ℝ := nsq fun a => 2 * ((lam a : ℝ) + rhoV n a)

open Classical in

def topTypes (lam : Fin n → ℤ) : Finset (Fin n → ℝ) :=
  (((univ : Finset (Finset (Fin n × Fin n))).filter fun B => ∀ p ∈ B, p.1 < p.2).image fun B =>
    domC ((fun a => 2 * (lam a : ℝ) + 2 * rhoV n a) + rhoV n - wtB B) - rhoV n).filter fun ν => StrictAnti (ν + rhoV n)

def LemmaHT : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → harmSet lam ⊆ topTypes lam ∧
    ∀ ν ∈ topTypes lam, spinSq ν ≤ LSq lam ∧ (spinSq ν = LSq lam → ν ∈ harmSet lam)

def DiracV : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V),
    IsCoreMod (infOf lam) E1 E2 σ A → ∀ ν : Fin n → ℝ, hwSp E1 E2 ν ≠ ⊥ → LSq lam ≤ spinSq ν

def SecondTypeWeightsShorter : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ ν, IsSecondTypeWeight lam lev ν →
    ν ∈ topTypes lam ∧ nsq (ν + rhoV n) < nsq (muQ lam lev + rhoV n)

def CountE : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
      (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V), IsCoreMod (infOf lam) E1 E2 σ A →
      FiniteDimensional ℂ (invA σ E) → ∃ m : (Fin n → ℝ) → ℕ, (∀ μ ∈ harmSet lam, m μ = 1) ∧
        (∀ ν ∈ topTypes lam, m ν ≠ 0 → FiniteDimensional ℂ (hwSp E1 E2 ν)) ∧
        (invA σ E ≠ ⊥ → ∃ ν ∈ topTypes lam, m ν ≠ 0 ∧ hwSp E1 E2 ν ≠ ⊥) ∧
        trOn (invA σ E) (flipA E A T) = 2 ^ n * ∑ ν ∈ topTypes lam, (m ν : ℂ) * trOn (hwSp E1 E2 ν) A

end PositivityTheory.RgBcC.RealD
