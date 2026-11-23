import Mathlib
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

namespace GlobalTheory

theorem contDiffOn_one_wdb_of_contDiffOn_two_isOpen {n : ℕ} {U : Set (V n)} {g : V n → ℂ}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (l : Fin n) :
    ContDiffOn ℝ 1 (wdb n l g) U := by
  have hD : ContDiffOn ℝ 1 (fun y => fderiv ℝ g y) U :=
    hg.fderiv_of_isOpen hU (by norm_num)
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ g y (bas n l)) U :=
    hD.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ 1 (fun y => fderiv ℝ g y (Complex.I • bas n l)) U :=
    hD.clm_apply contDiffOn_const
  have h3 : ContDiffOn ℝ 1
      (fun y => (fderiv ℝ g y (bas n l) + Complex.I * fderiv ℝ g y (Complex.I • bas n l)) / 2) U :=
    (h1.add (contDiffOn_const.mul h2)).div_const 2
  have e : wdb n l g = fun y =>
      (fderiv ℝ g y (bas n l) + Complex.I * fderiv ℝ g y (Complex.I • bas n l)) / 2 :=
    funext fun y => rfl
  rw [e]
  exact h3

theorem continuousOn_wd_of_contDiffOn_one_isOpen {n : ℕ} {U : Set (V n)} {g : V n → ℂ}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U) (j : Fin n) :
    ContinuousOn (wd n j g) U := by
  have hD : ContinuousOn (fun y => fderiv ℝ g y) U :=
    hg.continuousOn_fderiv_of_isOpen hU le_rfl
  have h1 : ContinuousOn (fun y => fderiv ℝ g y (bas n j)) U :=
    hD.clm_apply continuousOn_const
  have h2 : ContinuousOn (fun y => fderiv ℝ g y (Complex.I • bas n j)) U :=
    hD.clm_apply continuousOn_const
  have h3 : ContinuousOn
      (fun y => (fderiv ℝ g y (bas n j) - Complex.I * fderiv ℝ g y (Complex.I • bas n j)) / 2) U :=
    (h1.sub (continuousOn_const.mul h2)).div_const 2
  have e : wd n j g = fun y =>
      (fderiv ℝ g y (bas n j) - Complex.I * fderiv ℝ g y (Complex.I • bas n j)) / 2 :=
    funext fun y => rfl
  rw [e]
  exact h3

theorem continuousOn_cHess_of_contDiffOn_two :
    ∀ (n : ℕ) (U : Set (V n)) (φ : V n → ℝ), IsOpen U → ContDiffOn ℝ 2 φ U → ∀ j l,
      ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z j l) U := by
  intro n U φ hU hφ j l
  have hc : ContDiffOn ℝ 2 (fun v => (φ v : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hφ
  have hb := contDiffOn_one_wdb_of_contDiffOn_two_isOpen hU hc l
  simpa only [cHess, Matrix.of_apply] using continuousOn_wd_of_contDiffOn_one_isOpen hU hb j

end GlobalTheory
