import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnPeriodicFundamentalDomain

open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff

namespace GlobalTheory

theorem integrableOn_strN_heatKernel_diag : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g m : ℕ} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)} {j : Fl g → Pt E g → ℂ} {h : Pt E g → ℝ} (β : Fin m → E) (b : E) (u : ℝ) (D : Set (Fl g)), IsLat M → IsAddFundamentalDomain M D volume → ∀ (K : ℝ → (Fin g → ℂ) → (Fin g → ℂ) → Ext (m + m + g) →L[ℂ] Ext (m + m + g)), IsHeatKernel τ M j h β b u D K → IntegrableOn (fun x => strN (K 1 (per (τ b) x) (per (τ b) x))) D := by
  intro E _ _ g m τ M j h β b u D hM hD K hK
  obtain ⟨hc, hp, -, -⟩ := hK
  have hper : Continuous (per (τ b)) := by
    unfold per
    refine Continuous.add ?_ (by fun_prop)
    exact Continuous.matrix_vecMul (by fun_prop) continuous_const
  have hadd : ∀ x l : Fl g, per (τ b) (x + l) = per (τ b) x + per (τ b) l := by
    intro x l
    funext i
    simp only [per, Matrix.vecMul, dotProduct, Pi.add_apply, Complex.ofReal_add, add_mul,
      Finset.sum_add_distrib]
    ring
  have hKc : Continuous fun x : Fl g => K 1 (per (τ b) x) (per (τ b) x) :=
    hc.continuousOn.comp_continuous
      (f := fun x : Fl g => ((1 : ℝ), per (τ b) x, per (τ b) x))
      (continuous_const.prodMk (hper.prodMk hper))
      (fun x => ⟨(one_pos : (0 : ℝ) < 1), mem_univ _⟩)
  refine GlobalTheory.integrableOn_periodic_of_isLat M hM D hD _ ?_ ?_
  · refine continuous_pi fun S => ?_
    unfold strN
    refine continuous_finsetSum _ fun I _ => continuous_const.mul ?_
    exact (continuous_apply _).comp (hKc.clm_apply continuous_const)
  · intro l hl x
    rw [hadd, (hp 1 one_pos l hl (per (τ b) x) (per (τ b) x + per (τ b) l)).1,
      (hp 1 one_pos l hl (per (τ b) x) (per (τ b) x)).2]

end GlobalTheory
