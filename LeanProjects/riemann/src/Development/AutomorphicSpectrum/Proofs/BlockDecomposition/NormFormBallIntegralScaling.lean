import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnstatedLocalWeilLemma

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilGaussScale

theorem mul_mem_valBall_add_ord_iff {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {t : K} (ht : t ≠ 0) (n : ℤ) (u : K) :
    t * u ∈ (valBall K (n + ord t) : Set K) ↔ u ∈ (valBall K n : Set K) := by
  rw [← smul_valBall ht n, ← smul_eq_mul]
  exact Set.smul_mem_smul_set_iff₀ ht _ _

theorem integral_valBall_dilation : ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (t : Eˣ) (n : ℤ),
  ∫ u in (valBall E n : Set E), (χ (Algebra.norm F (t : E) * Algebra.norm F u) : ℂ) ∂muE E χ =
    (((modulus (Algebra.norm F (t : E)) : ℝ)⁻¹ : ℝ) : ℂ) *
      ∫ u in (valBall E (n + ord (t : E)) : Set E), (χ (Algebra.norm F u) : ℂ) ∂muE E χ := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη t n
  haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : ValuativeExtension F E := GlobalTheory.CompanionTheory.WeilSB.valuativeExtension_of_continuous hcont
  haveI : Algebra.IsSeparable F E := inferInstance
  rw [modulus_norm (K := F) (t : E)]
  set f : E → ℂ := (valBall E (n + ord (t : E)) : Set E).indicator
    (fun u => (χ (Algebra.norm F u) : ℂ)) with hf
  have hsub := integral_comp_mul_left (muE E χ) t.ne_zero f
  have hpt : (fun u => f ((t : E) * u)) = (valBall E n : Set E).indicator
      (fun u => (χ (Algebra.norm F (t : E) * Algebra.norm F u) : ℂ)) := by
    funext u
    by_cases hu : u ∈ (valBall E n : Set E)
    · rw [Set.indicator_of_mem hu, hf, Set.indicator_of_mem
        ((mul_mem_valBall_add_ord_iff t.ne_zero n u).2 hu), map_mul]
    · rw [Set.indicator_of_notMem hu, hf, Set.indicator_of_notMem
        (fun h => hu ((mul_mem_valBall_add_ord_iff t.ne_zero n u).1 h))]
  rw [hpt, integral_indicator (measurableSet_valBall n), hf,
    integral_indicator (measurableSet_valBall _)] at hsub
  rw [hsub, Complex.real_smul]

end GlobalTheory.CompanionTheory.WeilGaussScale
