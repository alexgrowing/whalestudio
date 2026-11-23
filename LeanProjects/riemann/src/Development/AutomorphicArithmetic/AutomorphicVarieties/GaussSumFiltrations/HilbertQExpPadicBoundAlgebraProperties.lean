import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.QExpansionLinearCombination
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.QExpansionMulFiniteConvolution
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem small_filtration : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (r s : ℝ) (f g : Hn F → ℂ) (c : ℂ), Small ι r f → Small ι s g → Small ι (max r s) (f + g) ∧ Small ι (r * s) (f * g) ∧ Small ι (‖ι.symm c‖ * r) (c • f) ∧ (r ≤ s → Small ι s f) ∧ 0 ≤ r ∧ Small ι ‖ι.symm c‖ (fun _ : Hn F => c) := by
  intro F _ _ _ p _ ι r s f g c hf hg
  obtain ⟨a, ha, har⟩ := hf
  obtain ⟨b, hb, hbs⟩ := hg
  have hr : 0 ≤ r := (norm_nonneg _).trans (har 0)
  have hs : 0 ≤ s := (norm_nonneg _).trans (hbs 0)
  obtain ⟨h1, h2, -, h4⟩ := GlobalTheory.T.qExpansion_linear_combination F f g a b c ha hb
  refine ⟨⟨a + b, h1, fun ξ => ?_⟩, ?_, ⟨c • a, h2, fun ξ => ?_⟩, fun hrs => ⟨a, ha, fun ξ => (har ξ).trans hrs⟩, hr,
    ⟨_, h4, fun ξ => ?_⟩⟩
  · rw [Pi.add_apply, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (har ξ) (hbs ξ))
  · obtain ⟨d, hd, hds⟩ := GlobalTheory.T.qExpansion_mul_finite_convolution F f g a b ha hb
    refine ⟨d, hd, fun ξ => ?_⟩
    obtain ⟨t, ht⟩ := hds ξ
    rw [ht, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun η _ => ?_
    rw [map_mul, norm_mul]
    exact mul_le_mul (har η) (hbs _) (norm_nonneg _) hr
  · rw [Pi.smul_apply, smul_eq_mul, map_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (har ξ) (norm_nonneg _)
  · split_ifs
    · exact le_rfl
    · rw [map_zero, norm_zero]; exact norm_nonneg _

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertQExp_padicBound_algebra_properties : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (r s : ℝ) (f g : Hn F → ℂ) (c : ℂ), Small ι r f → Small ι s g → Small ι (max r s) (f + g) ∧ Small ι (r * s) (f * g) ∧ Small ι (‖ι.symm c‖ * r) (c • f) ∧ (r ≤ s → Small ι s f) ∧ 0 ≤ r ∧ Small ι ‖ι.symm c‖ (fun _ : Hn F => c) := by
  first | exact @GlobalTheory.HilbertThetaSeries.small_filtration | exact GlobalTheory.HilbertThetaSeries.small_filtration | (intros; apply GlobalTheory.HilbertThetaSeries.small_filtration <;> assumption)
