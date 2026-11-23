import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsDivPushResBranches
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Topology Filter ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

def resAbove {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {e n : ℕ}
    (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (y : Fin n → ℂ)
    (w : ((k : K) → ι k) → ℂ) : Set R.X :=
  {x | projCoord R Ψ x = y ∧ divPt R Ψ x = w}

def DivPushResFibreGerms.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (A : HermLine ι) (s : MRing ι)
    (r : ℕ) (m : Fin r → ℕ) (W : Fin r → Set R.X)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsArithVar P (n + 2) → IsSectionOn P A s →
    IsSNC R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) m W →
    (∀ W' ∈ divSupp P s, IsHorizontal W' → IsGoodProj W' Ψ) →
    ∀ᵐ y, ∀ W' ∈ divSupp P s, IsHorizontal W' → ∀ w ∈ fibre W' Ψ y,
      ∀ Wa ∈ (W'.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
      ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ f ∈ Wa, eval z f = 0) → segre z = w →
        (resAbove R Ψ y w).Finite ∧
        ∃ V : R.X → Set R.X,
          (∀ x ∈ resAbove R Ψ y w, IsOpen (V x) ∧ x ∈ V x ∧ V x ⊆ R.U x) ∧
          (∀ x ∈ resAbove R Ψ y w, ∀ k k', x ∈ W k → x ∈ W k' → k = k') ∧
          (∀ x ∈ resAbove R Ψ y w, ∀ y₁ ∈ V x, ∀ y₂ ∈ V x,
            SameOrbit (R.lift x y₁) (R.lift x y₂) → y₁ = y₂) ∧
          (∀ x ∈ resAbove R Ψ y w, ∀ x' ∈ resAbove R Ψ y w, x ≠ x' → ∀ v : (Σ k, ι k) → ℂ,
            (∃ y₁ ∈ V x, SameOrbit v (R.lift x y₁)) → (∃ y₂ ∈ V x', SameOrbit v (R.lift x' y₂)) →
              eval v (map (Int.castRingHom ℂ) s) = 0) ∧
          (∀ V' : R.X → Set R.X, (∀ x ∈ resAbove R Ψ y w, V' x ∈ 𝓝 x) →
            ∃ N ∈ 𝓝 z, ∀ v ∈ mcPts P ∩ N, ∃ x ∈ resAbove R Ψ y w, ∃ y₁ ∈ V' x ∩ V x,
              SameOrbit v (R.lift x y₁)) ∧
          (∀ V' : R.X → Set R.X, (∀ x ∈ resAbove R Ψ y w, V' x ∈ 𝓝 x) →
            ∃ N ∈ 𝓝 z, ∀ v ∈ N, (∀ f ∈ Wa, eval v f = 0) → ∀ x ∈ resAbove R Ψ y w,
              ∃ y₁ ∈ V' x ∩ V x, eval (R.lift x y₁) (map (Int.castRingHom ℂ) s) = 0 ∧
                SameOrbit v (R.lift x y₁))

end GroundTheory.Heights₂.Heights.Targets
