import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CongL
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.G1

def AuxiliaryInertOddPrime : Prop := ∀ d : ℕ, 0 < d → ∀ b : ℕ, ∃ (p : ℕ) (_ : Fact p.Prime), b < p ∧ IsSquare (-(d : ℚ_[p]))

def ArithK : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ), 0 < d → ∀ x : E, x ^ 2 = -(d : E) →
  ∀ (τ₀ : E →+* ℂ) (Q : Finset ℕ), (∀ q ∈ Q, ∃ _ : Fact q.Prime, IsSquare (-(d : ℚ_[q]))) →
  ∃ A : Arith E, A.τ₀ = τ₀ ∧ (∃ f : ℚ, f ≠ 0 ∧ 2 * (A.ω : E) - (A.tr : E) = (f : E) * x) ∧
    (∀ (q : ℕ) [Fact q.Prime], IsSquare (-(d : ℚ_[q])) → A.SplitK q) ∧ ∀ q ∈ Q, A.Good q

def ScOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Even (Module.finrank ℚ (maximalRealSubfield E)) →
  ∀ (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p), Odd n → Sc S.D S.G

def DatumEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (a : ℕ), Odd a → ∀ d : ℕ,
  FieldOK E l d → ∀ x : E, x ^ 2 = -(d : E) → ∀ (τ₀ : E →+* ℂ) (Q : Finset ℕ), (∀ q ∈ Q, ∃ _ : Fact q.Prime, SqAt d q) → ∀ b : ℕ,
  ∃ (A : Arith E) (p : ℕ) (_ : Fact p.Prime) (S : Setup A a p), b < p ∧ p ∉ Q ∧ SqAt d p ∧ A.τ₀ = τ₀ ∧ Sc S.D S.G ∧
    (∃ f : ℚ, f ≠ 0 ∧ 2 * (A.ω : E) - (A.tr : E) = (f : E) * x) ∧
    (∀ (q : ℕ) [Fact q.Prime], SqAt d q → A.SplitK q) ∧ (∀ q ∈ Q, A.Good q) ∧
    ∃ e : ℕ, 0 < e ∧ ∀ (q : ℕ) [Fact q.Prime], SqAt d q → ¬ q ∣ e → A.Good q

def RootAt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (q : ℕ), q.Prime → A.SplitK q →
  ∀ w : HeightOneSpectrum (𝓞 E), (q : 𝓞 E) ∈ w.asIdeal →
  ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - A.tr * r + A.nm ∧ A.ω - (r : 𝓞 E) ∈ w.asIdeal

def AtPrimeEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (x : E) (f : ℚ), 2 * (A.ω : E) - (A.tr : E) = (f : E) * x → ∀ q : ℕ, q.Prime → q ≠ p → A.Good q →
  ∀ w : HeightOneSpectrum (𝓞 E), (q : 𝓞 E) ∈ w.asIdeal →
  ∃ r : ℤ, ∀ w' : HeightOneSpectrum (𝓞 E), OneK x w w' →
    A.ω - (r : 𝓞 E) ∈ w'.asIdeal ∧ AtPrime S.D q r w'.asIdeal ∧ IsPl (D := S.D) (RingEquiv.refl E) w' w'.asIdeal

def StdForm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p),
  ∃ β : S.G.Cˣ, mat S β = Matrix.diagonal (fun i => ((A.dg n i : 𝓞 E) : E)) ∧ sh S.G β = β ∧
    ∀ v : InfinitePlace S.G.F, ∀ x : Fin S.G.n → ℂ, x ≠ 0 →
      (sigPosH (S.G.gram_herm v) = 1 → 0 < (star x ⬝ᵥ ((S.G.gram v * S.G.psi v ((β⁻¹ : S.G.Cˣ) : S.G.C)) *ᵥ x)).re) ∧
      (sigPosH (S.G.gram_herm v) ≠ 1 → (star x ⬝ᵥ ((S.G.gram v * S.G.psi v ((β⁻¹ : S.G.Cˣ) : S.G.C)) *ᵥ x)).re < 0)

end UpperTheory.Gal.G1
