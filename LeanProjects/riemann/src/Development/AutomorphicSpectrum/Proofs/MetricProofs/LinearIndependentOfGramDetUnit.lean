import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PPartRealSmul
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem linearIndependent_of_isUnit_gram_det :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ]
      [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (d : Fin m → Fin g → ℂ),
      IsUnit (R.gram d).det → LinearIndependent ℂ d := by
  intro E _ _ _ g Λ _ _ R m d hdet
  rw [Fintype.linearIndependent_iff]
  intro x hx
  have hmul : (R.gram d) *ᵥ x = 0 := by
    funext a
    have hsum : (∑ b, x b • d b) ⬝ᵥ (R.Hm *ᵥ star (d a)) = 0 := by
      rw [hx, zero_dotProduct]
    rw [sum_dotProduct] at hsum
    simp only [smul_dotProduct, smul_eq_mul] at hsum
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hsum ⊢
    rw [← hsum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, Matrix.mulVec, dotProduct]
    rw [mul_comm]
  have hx0 : x = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet.ne_zero hmul
  intro i
  rw [hx0, Pi.zero_apply]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
