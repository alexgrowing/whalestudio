import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.PoinTerm

theorem norm_coef_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v : ∀ τ, M.H τ), KDecay M v → ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : GA D V, ‖coef θ M K v b x‖ ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := by
  intro D θ hθ V S M K v hv b hb
  choose C hC using fun τ => (hv τ).2 (b τ) (hb τ)
  have hpos : ∀ (τ : D.what₂.Tau) (x : GA D V), 0 < (1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1) := fun τ x =>
    pow_pos (add_pos_of_pos_of_nonneg one_pos (Real.sqrt_nonneg _)) _
  have hle : ∀ (τ : D.what₂.Tau) (x : GA D V), ‖⟪v τ, M.rep τ (cmp θ τ x) (b τ)⟫_ℂ‖ * (1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1) ≤ C τ :=
    fun τ x => hC τ _ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ)
  have h0 : ∀ τ, 0 ≤ C τ := fun τ => (mul_nonneg (norm_nonneg _) (hpos τ 1).le).trans (hle τ 1)
  have hP : 0 ≤ ∏ τ, C τ := Finset.prod_nonneg fun τ _ => h0 τ
  refine ⟨∏ τ, C τ, hP, fun x => ?_⟩
  unfold coef
  split_ifs
  · unfold coefR
    rw [norm_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun τ _ => norm_nonneg _) fun τ _ => ?_
    rw [← div_eq_mul_inv, le_div_iff₀ (hpos τ x)]
    exact hle τ x
  · rw [norm_zero]
    exact mul_nonneg hP (Finset.prod_nonneg fun τ _ => (inv_pos.2 (hpos τ x)).le)

end GlobalTheory.PoinTerm
