import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CM

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.DegreeIdentityCharacter

section Period

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def hostChar (H : Host E) : DirichletCharacter ℂ H.d :=
  haveI : Fact H.d.Prime := ⟨H.d_prime⟩
  (quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ)

def logOmega (H : Host E) : ℝ :=
  haveI : NeZero H.d := ⟨H.d_prime.ne_zero⟩
  (logOm E (hostChar H)).re

theorem hostChar_apply (H : Host E) (n : ℤ) : hostChar H (n : ZMod H.d) = (jacobiSym n H.d : ℂ) := by
  haveI : Fact H.d.Prime := ⟨H.d_prime⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  rfl

theorem hostChar_ne_one (H : Host E) : hostChar H ≠ 1 := by
  haveI : Fact H.d.Prime := ⟨H.d_prime⟩
  have h2 : ringChar (ZMod H.d) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    have := H.d_mod
    omega
  exact (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom ℂ) Int.cast_injective).2 (quadraticChar_ne_one h2)

theorem lFunction_one_ne_zero (H : Host E) :
    haveI : NeZero H.d := ⟨H.d_prime.ne_zero⟩
    (hostChar H).LFunction 1 ≠ 0 :=
  haveI : NeZero H.d := ⟨H.d_prime.ne_zero⟩
  DirichletCharacter.LFunction_apply_one_ne_zero (hostChar_ne_one H)

end Period

def EigenLineDegree : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K]
    (T : PAT H (Sp (𝓞 K))) (ρ : 𝓞 K) (τ : 𝓞 E →+* 𝓞 K), ρ ^ 2 = -(H.d : 𝓞 K) →
    (HasType H T.t.act ρ 1 0 ∧ τ H.rt = ρ) ∨ (HasType H T.t.act ρ 0 1 ∧ τ H.rt = -ρ) →
    ∀ (F : GenFib T.pol) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h →
      deg h (F.eigLat T.t.act τ) = logOmega H / 2

def DiffLength : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K]
    (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q) (j : Fin p ⊕ Fin q)
    (FA : GenFib (X.A j.isLeft).pol) (FB : GenFib X.B.pol)
    (hA : HermFam K (Fin FA.P₀.g → K)) (hB : HermFam K (Fin FB.P₀.g → K))
    (M : (Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)),
    FA.IsHerm hA → FB.IsHerm hB → FA.IsDiffOf FB (X.φ j) M →
    ∀ (τ : 𝓞 E →+* 𝓞 K), ∀ c ∈ FA.eigLat (X.A j.isLeft).t.act τ, ∀ s : K →+* ℂ,
      hB.nrm s (M c) ^ 2 = ‖s (τ (X.hh j) : K)‖ * hA.nrm s c ^ 2

def EigenImagesSpan : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K]
    (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q)
    (FA : ∀ b : Bool, GenFib (X.A b).pol) (FB : GenFib X.B.pol)
    (M : ∀ j : Fin p ⊕ Fin q, (Fin (FA j.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)),
    (∀ j, (FA j.isLeft).IsDiffOf FB (X.φ j) (M j)) →
    ∀ τ : 𝓞 E →+* 𝓞 K,
      (∀ j : Fin p ⊕ Fin q, ∀ c ∈ (FA j.isLeft).eigLat (X.A j.isLeft).t.act τ, M j c ∈ FB.eigLat X.B.t.act τ) ∧
      (FB.eigLat X.B.t.act τ : Set (Fin FB.P₀.g → K)) ⊆
        Submodule.span K {y | ∃ j : Fin p ⊕ Fin q, ∃ c ∈ (FA j.isLeft).eigLat (X.A j.isLeft).t.act τ, y = M j c}

def KeyDegreeIdentity : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (hg : 1 ≤ F.P₀.g)
    (rig : LB.Gen (F.P₀.L.pull (eSec F.P₀.A))) (hr : rig.IsGen) (th : F.P₀.L.Sec)
    (hth : ∀ s : Sp K, ∃ x : F.P₀.A.left, F.P₀.A.hom x = s ∧ x ∈ Out.nonzeroLocus th)
    (h : HermFam K (Fin F.P₀.g → K)) (δ : ℝ), F.IsHerm h → IsThetaDeg (F.key hg rig hr th hth) δ →
      δ = (1 / 2) * (-deg h F.lieLat) + (P.g : ℝ) / 4 * Real.log (2 * Real.pi)

def DegreeBounds : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K]
    (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q) (La : ℝ), 0 < La →
    (∀ (j : Fin p ⊕ Fin q) (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ La ^ 2) →
    ∀ FB : GenFib X.B.pol,
      (∀ h : HermFam K (Fin FB.P₀.g → K), FB.IsHerm h →
        (Module.finrank ℚ E : ℝ) / 2 * (p + q) * (logOmega H / 2 - Real.log La) ≤ deg h FB.lieLat) ∧
      ∀ (hg : 1 ≤ FB.P₀.g) (rig : LB.Gen (FB.P₀.L.pull (eSec FB.P₀.A))) (hr : rig.IsGen) (th : FB.P₀.L.Sec)
        (hth : ∀ s : Sp K, ∃ x : FB.P₀.A.left, FB.P₀.A.hom x = s ∧ x ∈ Out.nonzeroLocus th) (δ : ℝ),
        IsThetaDeg (FB.key hg rig hr th hth) δ →
          δ ≤ -((Module.finrank ℚ E : ℝ) / 2 * (p + q) / 2) * (logOmega H / 2 - Real.log La) +
            (Module.finrank ℚ E : ℝ) / 2 * (p + q) / 4 * Real.log (2 * Real.pi)

def CMNumbers : Prop :=
  EigenLineDegree ∧ DiffLength ∧ EigenImagesSpan ∧ KeyDegreeIdentity ∧ DegreeBounds

end GlobalTheory.IndefiniteRowSideFullHecke.DegreeIdentityCharacter
end
