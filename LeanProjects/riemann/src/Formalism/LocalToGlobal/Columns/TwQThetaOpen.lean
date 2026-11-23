import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}

def lqPrinc (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) (g : Sp E n ≃ₗ[E] Sp E n) : Prop :=
  ∀ i j : Fin n, P.valuation E ((LinearMap.toMatrix' (g : Sp E n →ₗ[E] Sp E n) - 1) i j) ≤
    WithZero.coe (Multiplicative.ofAdd (-(N : ℤ)))

def ThetaOpen {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q) : Prop :=
  ∀ P : Q, ∃ N : ℕ, 0 < N ∧ ∀ g : ↥(GLint E n P.1), lqPrinc P.1 N (g : Sp E n ≃ₗ[E] Sp E n) →
    ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1

theorem thetaOpen_top (Q : Finset (HeightOneSpectrum (𝓞 E))) : ThetaOpen (LevQFam.top E K n Q) := by
  intro P
  exact ⟨1, Nat.one_pos, fun g _ => ⟨Subgroup.mem_top _, rfl⟩⟩

end Formalism.L2.Col
