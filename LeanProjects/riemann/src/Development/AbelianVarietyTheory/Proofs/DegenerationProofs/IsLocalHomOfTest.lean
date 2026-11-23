import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrameUnit
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH.ZHPre
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}

theorem isLocalHom_of_test {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)
    (jV : u.V →+* OO p)
    (hj : ∀ x, (jV x : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) x)) :
    IsLocalHom jV := by
  refine ⟨fun x hx => ?_⟩
  have h1 : ‖(jV x : PadicAlgCl p)‖ = 1 :=
    le_antisymm ((mem_OO_iff _).1 (jV x).2) (not_lt.1 fun h => (not_isUnit_OO_iff _).2 h hx)
  have h0 : algebraMap u.V (FractionRing u.V) x ≠ 0 := fun h => by
    rw [hj, h, map_zero, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨v, hv⟩ := (u.norm_le (algebraMap u.V (FractionRing u.V) x)⁻¹).1 (by
    rw [map_inv₀, ← hj, norm_inv, h1, inv_one])
  refine IsUnit.of_mul_eq_one v (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  rw [map_mul, hv, mul_inv_cancel₀ h0, map_one]

end GlobalTheory.ZH.ZHPre
end
