import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

section Defs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def IsDehomNormForms (y : (Σ k, ι k) → Ω) {D : ℕ} (L : Fin (D + 1) → MRing ι) (j : Fin (D + 1)) (m : ℕ) (s : Ω)
    (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ) : Prop :=
  aeval y (L j) ≠ 0 ∧ ∃ _ : FiniteDimensional (pullField y L) Ω,
    c 0 = 1 ∧ (∀ i ≤ Module.finrank (pullField y L) Ω, (c i).IsHomogeneous (i * m)) ∧
    (LinearMap.charpoly (Algebra.lmul (pullField y L) Ω (s / aeval y (L j) ^ m))).map
        (algebraMap (pullField y L) Ω) =
      ∑ i ∈ Finset.range (Module.finrank (pullField y L) Ω + 1),
        Polynomial.C (aeval (fun i' => aeval y (L i') / aeval y (L j)) (c i)) *
          Polynomial.X ^ (Module.finrank (pullField y L) Ω - i)

end Defs

def FibreNormDehomCharpoly.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    FiniteDimensional (pullField y L) Ω ∧
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ j : Fin (D + 1), aeval y (L j) ≠ 0 →
        ∃ c : ℕ → MvPolynomial (Fin (D + 1)) ℚ, IsDehomNormForms y L j (q * τ) s c ∧
          (s ≠ 0 → c (Module.finrank (pullField y L) Ω) ≠ 0)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
