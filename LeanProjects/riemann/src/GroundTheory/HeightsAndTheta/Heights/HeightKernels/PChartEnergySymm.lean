import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergySymm
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartIbpSymm
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergySwap
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotLtLtOfMemMinimalPrimes
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartEnergySymmetry

theorem cxHessian_sub {D : ℕ} {f g : (Fin D → ℂ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (y : Fin D → ℂ) : cxHessian (fun y' => f y' - g y') y = cxHessian f y - cxHessian g y := by
  have h1 : fderiv ℝ (fun y' => f y' - g y') = fun z => fderiv ℝ f z - fderiv ℝ g z := by
    funext z
    exact fderiv_sub (hf.differentiable (by norm_num) z) (hg.differentiable (by norm_num) z)
  have hf' : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hg' : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ (fun y' => f y' - g y')) y =
      fderiv ℝ (fderiv ℝ f) y - fderiv ℝ (fderiv ℝ g) y := by
    rw [h1]
    exact fderiv_sub (hf' y) (hg' y)
  ext i j
  simp only [cxHessian, h2, _root_.sub_apply, Matrix.sub_apply]
  push_cast
  ring

theorem mixedDisc_update_sub {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (k : Fin D)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (Function.update A k (X - Y)) =
      mixedDisc (Function.update A k X) - mixedDisc (Function.update A k Y) := by
  obtain ⟨M, hM⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := D)
  have e : ∀ C, mixedDisc (Function.update A k C) = M.toLinearMap A k C := fun C => by
    rw [MultilinearMap.toLinearMap_apply, hM]
    rfl
  simp only [e, map_sub]

theorem maDensity_update_sub {D : ℕ} (Φ : Fin D → (Fin D → ℂ) → ℝ) (p : Fin D) {f g : (Fin D → ℂ) → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (y : Fin D → ℂ) :
    maDensity (Function.update Φ p f) y - maDensity (Function.update Φ p g) y =
      maDensity (Function.update Φ p fun y' => f y' - g y') y := by
  have key : ∀ h : (Fin D → ℂ) → ℝ, (fun k => cxHessian (Function.update Φ p h k) y) =
      Function.update (fun k => cxHessian (Φ k) y) p (cxHessian h y) := fun h => by
    funext k
    exact Function.apply_update (fun _ h' => cxHessian h' y) Φ p h k
  simp only [maDensity, key, cxHessian_sub hf hg y, mixedDisc_update_sub, Complex.sub_re]
  ring

theorem update_comp_swap {α : Type*} {n : ℕ} (Φ : Fin (n + 1) → α) (p : Fin (n + 1)) (f : α) :
    Function.update Φ p f ∘ Equiv.swap 0 p = Fin.cons f (fun i => Φ (Equiv.swap 0 p i.succ)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp only [Function.comp_apply, Fin.cons_succ]
    rw [Function.update_of_ne]
    intro h
    have h' := congrArg (Equiv.swap 0 p) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at h'
    exact Fin.succ_ne_zero i h'

end ChartEnergySymmetry

open ChartEnergySymmetry in

theorem ChartEnergySymm.proof (hI : ChartIbpSymm.Statement) : ChartEnergySymm.Statement := by
  intro e A B C D T p hA hB hC hD hT
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by have := p.pos; omega⟩
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p with hσ
  set T' : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ := fun i => T (σ i.succ) with hT'def
  have hT' : ∀ i, (T' i).PosDef := fun i => hT _
  have hpot : ∀ X, (fun j => hermChartPot (Function.update T p X j)) =
      Function.update (fun j => hermChartPot (T j)) p (hermChartPot X) := fun X => by
    funext j
    exact Function.apply_update (fun _ M => hermChartPot M) T p X j
  have hdiff : ∀ X Y : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ, X.PosDef → Y.PosDef → ∀ y,
      maDensity (fun j => hermChartPot (Function.update T p X j)) y -
          maDensity (fun j => hermChartPot (Function.update T p Y j)) y =
        maDensity (Fin.cons (fun y' => hermChartPot X y' - hermChartPot Y y')
          fun i => hermChartPot (T' i)) y := by
    intro X Y hX hY y
    rw [hpot, hpot, maDensity_update_sub _ _ (ChartEnergySwapHessian.contDiff_hermChartPot X hX)
      (ChartEnergySwapHessian.contDiff_hermChartPot Y hY), ← Inter.maDensity_comp_perm _ σ, update_comp_swap]
  simp_rw [hdiff C D hC hD, hdiff A B hA hB]
  exact hI n A B C D T' hA hB hC hD hT'

end

end GroundTheory.Heights₂.Heights
