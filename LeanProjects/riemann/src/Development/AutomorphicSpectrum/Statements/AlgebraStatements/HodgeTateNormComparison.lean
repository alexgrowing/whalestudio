import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

def HodgeTateNormComparison : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C],
    v.Integers O → ∀ (E : Type) [Field E] [NumberField E] (c : E ≃+* E), (∀ x, c (c x) = x) →
    ∀ (κ : O) (N : ℕ) (V Ω : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
      [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω] (P : HTPoint C O c κ N V Ω)
      (Ψ : Type) [Fintype Ψ] (τ : Ψ → (E →+* C)) (j k : Ψ → ℕ)
      (bW : ∀ s, Basis (Fin (j s)) C (P.Wsp (τ s))) (bΩ : ∀ s, Basis (Fin (k s)) C (P.Ωsp (τ s)))
      (lW : ∀ s, Fin (j s) → ℝ) (lΩ : ∀ s, Fin (k s) → ℝ),
      |P.phiDiff v τ bW bΩ lW lΩ| ≤
        ∑ s, (-Real.log (v (algebraMap O C κ)) * ((∑ i, |lW s i|) + ∑ i, |lΩ s i|) +
          -Real.log (diffAbs v (τ s)) * |∑ i, lW s i|)

def ChartSequence : Prop :=
  ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K]
    [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E), (∀ x, c (c x) = x) →
    ∀ (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
      (D : HTChart A K c p R N Ω) (κ : A) (m : ℕ), κ * (p : A) ^ m ∣ (p : A) ^ R → D.HasTestPoints κ →
      Module.Projective A D.om' →
      (D.om' ≤ D.om ∧ ∀ x ∈ D.om, κ • x ∈ D.om') ∧
      ∀ (σ : E →+* K) (d d' : A), GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' →
        Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) →
        ∃ i, D.IsDualMap σ d m i ∧ D.ExactMod σ m i

end GlobalTheory.CompanionTheory.Ar.HT
