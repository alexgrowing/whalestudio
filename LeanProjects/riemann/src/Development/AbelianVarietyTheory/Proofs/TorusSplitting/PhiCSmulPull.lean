import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PhiSetPullSub
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

open scoped Pointwise

theorem phiC_smul_of_nonneg {E : Type} [Field E] [NumberField E] (cj : E → E) {X : Type} [AddCommGroup X]
    [Module (𝓞 E) X] (b : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X) {t : ℝ} (ht : 0 ≤ t) :
    Formalism.MainNotions.ModuliIntegralCharts.phiC cj (t • b) = t * Formalism.MainNotions.ModuliIntegralCharts.phiC cj b := by
  rw [phiC_eq_sInf, phiC_eq_sInf, ← smul_eq_mul, ← Real.sInf_smul_of_nonneg ht]
  congr 1
  ext x
  constructor
  · rintro ⟨l, h1, h2, rfl⟩
    exact ⟨l b, ⟨l, h1, h2, rfl⟩, (map_smul l t b).symm⟩
  · rintro ⟨_, ⟨l, h1, h2, rfl⟩, rfl⟩
    exact ⟨l, h1, h2, (map_smul l t b).symm⟩

theorem phiC_smul_pull : ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (X X' : Type) [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup X'] [Module (𝓞 E) X'] (e : X ≃ₗ[𝓞 E] X') (β' : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X') (t : ℝ), 0 ≤ t → ∃ β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X, (∀ a b, (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a b = t * (β' : X' →ₗ[ℤ] X' →ₗ[ℤ] ℝ) (e a) (e b)) ∧ Formalism.MainNotions.ModuliIntegralCharts.phiC cj β = t * Formalism.MainNotions.ModuliIntegralCharts.phiC cj β' := by
  intro E _ _ cj X X' _ _ _ _ e β' t ht
  refine ⟨t • pullS cj e β', fun a b => ?_, ?_⟩
  · rw [← pullS_apply cj e β' a b]
    rfl
  · rw [phiC_smul_of_nonneg cj _ ht, phiC_pull]

end GlobalTheory.EtaVal
