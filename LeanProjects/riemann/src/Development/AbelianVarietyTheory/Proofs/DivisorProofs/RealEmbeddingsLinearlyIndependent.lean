import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem realEmb_linearIndependent_on_integers (F : Type) [Field F] [NumberField F] (a : (F →+* ℝ) → ℝ) :
    (∀ x : 𝓞 F, ∑ τ, a τ * τ (x : F) = 0) → a = 0 := by
  intro h
  have hall : ∀ x : F, ∑ τ, a τ * τ x = 0 := by
    intro x
    have halg : IsAlgebraic ℤ x := by
      first
        | exact Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x
        | (haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
           exact (Algebra.IsIntegral.isIntegral (R := ℚ) x).isAlgebraic.restrictScalars ℤ)
    obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
    have h1 : ∑ τ : F →+* ℝ, a τ * τ (y • x) = 0 := h ⟨y • x, hint⟩
    rw [zsmul_eq_mul] at h1
    have h2 : ∑ τ : F →+* ℝ, a τ * τ ((y : F) * x) = (y : ℝ) * ∑ τ, a τ * τ x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [map_mul, map_intCast]; ring
    rw [h2] at h1
    rcases mul_eq_zero.mp h1 with h4 | h4
    · exact absurd (by exact_mod_cast h4) hy
    · exact h4
  have hli : LinearIndependent ℝ (fun τ : F →+* ℝ => ((τ : F →* ℝ) : F → ℝ)) :=
    (linearIndependent_monoidHom F ℝ).comp (fun τ : F →+* ℝ => (τ : F →* ℝ))
      (fun τ σ hτσ => RingHom.ext fun x => DFunLike.congr_fun hτσ x)
  funext τ
  refine Fintype.linearIndependent_iff.mp hli a ?_ τ
  funext x
  simpa [Finset.sum_apply, smul_eq_mul] using hall x

example : ∀ (F : Type) [Field F] [NumberField F] (a : (F →+* ℝ) → ℝ),
    (∀ x : 𝓞 F, ∑ τ, a τ * τ (x : F) = 0) → a = 0 := fun F _ _ a h => GlobalTheory.realEmb_linearIndependent_on_integers F a h

end GlobalTheory
