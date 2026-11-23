import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

def RamSplit (E : Type) {Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (H : Subgroup (G (maximalRealSubfield E) Ω)) : Prop :=
  ∀ (t : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (A : ValuationSubring Ω), IsPlaceOver A t →
    Ine (F := maximalRealSubfield E) A ≤ H ∨ ∀ g ∈ Dec (F := maximalRealSubfield E) A, Fixes E g

def MoveRoot : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (U : Subgroup (G ℚ Ω)), IsOpen (U : Set (G ℚ Ω)) →
    ∀ ℓ : ℕ, ℓ.Prime → ∃ (b : ℕ) (σ : G ℚ Ω), σ ∈ U ∧ ∀ ζ : Ω, IsPrimitiveRoot ζ (ℓ ^ b) → σ ζ ≠ ζ

def NormVal : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (U : Subgroup (G ℚ Ω)), IsOpen (U : Set (G ℚ Ω)) →
    ∀ q : ℕ, 1 < q → ∃ D : ℕ, 0 < D ∧ ∀ (z : Ω) (n c : ℕ), (∀ τ ∈ U, τ z = z) → z ^ n * (q : Ω) ^ c = 1 → n ∣ c * D

def KumMove : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (U : Subgroup (G ℚ Ω)), IsOpen (U : Set (G ℚ Ω)) →
    ∀ ℓ q : ℕ, ℓ.Prime → 1 < q → ∃ j : ℕ, ∀ k, j ≤ k → ∀ ζ y : Ω, IsPrimitiveRoot ζ (ℓ ^ k) → y ^ ℓ ^ j = (q : Ω) →
      ∃ σ ∈ U, σ ζ = ζ ∧ σ y ≠ y

def OrdPrime : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ℓ k q B : ℕ), ℓ.Prime → 1 < q →
    ∃ p : ℕ, p.Prime ∧ B < p ∧ ℓ ^ k ∣ orderOf (q : ZMod p) ∧ ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 →
      ∀ h : Ω ≃+* Ω, (∀ z, h z ∈ A ↔ z ∈ A) → ∀ y : E, h (algebraMap E Ω y) = algebraMap E Ω y

def CharOrd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ℓ k : ℕ) (a : (ZMod p)ˣ), ℓ.Prime → ℓ ^ (k + 1) ∣ orderOf a →
    ∃ lam : (ZMod p)ˣ →* ℂˣ, lam (-1) = 1 ∧ orderOf (lam a) = ℓ ^ k

def UnrCharAt (f : ℕ) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))),
    ∃ r : G (maximalRealSubfield E) Ω →* ℂˣ, Good r.ker ∧ RamSplit E r.ker ∧
      ∀ A : ValuationSubring Ω, IsPlaceOver A v → Ine (F := maximalRealSubfield E) A ≤ r.ker ∧
        ∀ φ : G (maximalRealSubfield E) Ω, IsFrob A (normV v) φ → orderOf (r φ) = f

def UnrCharPP : Prop := ∀ ℓ k : ℕ, ℓ.Prime → UnrCharAt (ℓ ^ k)

def FreshSplit : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (U : Subgroup (G (maximalRealSubfield E) Ω)),
    IsOpen (U : Set (G (maximalRealSubfield E) Ω)) →
    ∀ T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), T.Finite → ∀ n : ℕ, 0 < n →
    ∃ ψ : G (maximalRealSubfield E) Ω →* ℂˣ, Good ψ.ker ∧ RamSplit E ψ.ker ∧ ψ ^ n = 1 ∧
      (∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t → ∀ g ∈ Dec (F := maximalRealSubfield E) A, ψ g = 1) ∧
      ∃ u ∉ T, ∀ A : ValuationSubring Ω, IsPlaceOver A u → Dec (F := maximalRealSubfield E) A ≤ U ∧
        ∃ τ ∈ Ine (F := maximalRealSubfield E) A, orderOf (ψ τ) = n

theorem RamSplit.inf {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {H H' : Subgroup (G (maximalRealSubfield E) Ω)} (h : RamSplit E H) (h' : RamSplit E H') : RamSplit E (H ⊓ H') := by
  intro t A hA
  rcases h t A hA with h1 | h1
  · rcases h' t A hA with h2 | h2
    · exact Or.inl (le_inf h1 h2)
    · exact Or.inr h2
  · exact Or.inr h1

theorem RamSplit.mono {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {H H' : Subgroup (G (maximalRealSubfield E) Ω)} (hle : H ≤ H') (h : RamSplit E H) : RamSplit E H' := by
  intro t A hA
  rcases h t A hA with h1 | h1
  · exact Or.inl (h1.trans hle)
  · exact Or.inr h1

theorem unrCharAt_of (h : UnrCharPP) (f : ℕ) (hf : 0 < f) : UnrCharAt f := by
  induction f using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp _ => exact h p n hp
  | zero => exact absurd hf (lt_irrefl 0)
  | one => simpa using h 2 0 Nat.prime_two
  | coprime a b ha hb hab iha ihb =>
    intro E Ω _ _ _ _ _ _ v
    obtain ⟨r, h1, h2, h3⟩ := iha (by omega) E Ω v
    obtain ⟨s, k1, k2, k3⟩ := ihb (by omega) E Ω v
    have hle : r.ker ⊓ s.ker ≤ (r * s).ker := fun g hg => by
      rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.mem_ker.1 hg.1, MonoidHom.mem_ker.1 hg.2, one_mul]
    refine ⟨r * s, (h1.inf k1).mono hle, (h2.inf k2).mono hle, fun A hA =>
      ⟨(le_inf (h3 A hA).1 (k3 A hA).1).trans hle, fun φ hφ => ?_⟩⟩
    have e1 := (h3 A hA).2 φ hφ
    have e2 := (k3 A hA).2 φ hφ
    rw [MonoidHom.mul_apply, (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime (by rwa [e1, e2]), e1, e2]

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
