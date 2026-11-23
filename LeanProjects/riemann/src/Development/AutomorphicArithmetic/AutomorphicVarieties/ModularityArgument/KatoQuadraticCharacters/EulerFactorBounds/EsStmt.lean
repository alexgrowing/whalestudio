import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KZ.ES UpperTheory.Kd.K4
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Z.Kato.Nb

def SEsLev : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ), 1 ≤ N →
    ∀ b ∈ X.BSet N l w, ∀ n : ℕ, (∀ u u' : Fin 2 → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ u i - u' i) →
      AdicCompletion.eval (idl l) (X.Kl l) n (b u - b u') = 0) ∧ (∀ (t : ℤ_[l]) u, b (t • u) = t ^ w • b u) ∧
      ∀ u, ∃ (k : ℕ) (F : X.Kˣ), n ≤ k ∧ F ∈ X.Un (l ^ n) ∧ ES.Lev X (6 * l * N * l ^ k) (F : X.K) ∧ Rep X l n F ((4 : ℤ_[l]) • b u)

def SEsFrob : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (v : Pl) (B : ValuationSubring Ω) (σ : G ℚ Ω),
    (normV v).Prime → normV v ≠ l → IsPlaceOver B v → IsFrob B (normV v) σ →
      FrobV B (normV v) σ ∧ (cyclotomicCharacter Ω l σ.toRingEquiv : ℤ_[l]) = (normV v : ℕ)

def SEsT : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w q M : ℕ), 1 ≤ N →
    q.Prime → Nat.Coprime q (l * N) → Nat.Coprime q M → l * N ∣ M → ∀ γ : SL(2, ℤ), DiagMod M q γ → ∀ b ∈ X.BSet N l w,
      X.heckeT N l q b = (∑ j ∈ Finset.range q, X.act l !![1, (j * M : ℤ); 0, (q : ℤ)] b) +
        X.act l ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) b ∧
      ∀ s, X.diam N l q (X.galB l s b) = X.galB l s (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b)

def SEs : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), l ≠ 2 → ∀ (N w : ℕ),
    1 ≤ N → ∃ S0 : Finset ℕ, ∀ (v : Pl) (B : ValuationSubring Ω) (σ : G ℚ Ω), normV v ∉ S0 → (normV v).Prime →
      IsPlaceOver B v → IsFrob B (normV v) σ → ∀ b ∈ X.B N l w,
        X.heckeT N l (normV v) b = X.galB l σ b + ((normV v : ℤ_[l]) ^ (w + 1)) • X.diam N l (normV v) (X.galB l σ⁻¹ b)

end UpperTheory.V.Z.Kato.Nb

end
