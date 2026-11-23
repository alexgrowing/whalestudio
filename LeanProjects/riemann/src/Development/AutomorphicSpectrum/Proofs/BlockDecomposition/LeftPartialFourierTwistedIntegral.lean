import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Slice

theorem fubini3 {F : Type} [MeasurableSpace F] (μ : Measure F) [SFinite μ] (J : F × F × F → ℂ)
    (hJ : Integrable J (μ.prod (μ.prod μ))) :
    ∫ b, ∫ d, ∫ a, J (a, b, d) ∂μ ∂μ ∂μ = ∫ a, ∫ b, ∫ d, J (a, b, d) ∂μ ∂μ ∂μ := by
  have h1 : ∫ a, ∫ b, ∫ d, J (a, b, d) ∂μ ∂μ ∂μ = ∫ a, ∫ t, J (a, t) ∂(μ.prod μ) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hJ.prod_right_ae] with a ha
    exact (integral_prod (fun t => J (a, t)) ha).symm
  have h2 : ∫ a, ∫ t, J (a, t) ∂(μ.prod μ) ∂μ = ∫ t, ∫ a, J (a, t) ∂μ ∂(μ.prod μ) :=
    integral_integral_swap (f := fun a t => J (a, t)) hJ
  have h3 : ∫ t, ∫ a, J (a, t) ∂μ ∂(μ.prod μ) = ∫ b, ∫ d, ∫ a, J (a, b, d) ∂μ ∂μ ∂μ :=
    integral_prod (fun t => ∫ a, J (a, t) ∂μ) hJ.integral_prod_right
  rw [h1, h2, h3]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem hcs_comp {X : Type} [TopologicalSpace X] [T2Space X] {p : Matrix (Fin 2) (Fin 2) F → ℂ}
    (hp : HasCompactSupport p) (ι : X → Matrix (Fin 2) (Fin 2) F) (r : Matrix (Fin 2) (Fin 2) F → X)
    (hι : Continuous ι) (hr : Continuous r) (h : Function.LeftInverse r ι) :
    HasCompactSupport (fun x => p (ι x)) :=
  hp.comp_isClosedEmbedding (h.isClosedEmbedding hr hι)

def J (ψ : AddChar F Circle) (p : Matrix (Fin 2) (Fin 2) F → ℂ) (t : F × F × F) : ℂ :=
  p !![t.1, t.2.1; t.2.2, 1] * (ψ (-(t.2.1 + t.2.2)) : ℂ)

theorem integrable_J {ψ : AddChar F Circle} (hψ : Continuous ψ) {p : Matrix (Fin 2) (Fin 2) F → ℂ} (hp : SB2 p) :
    Integrable (J ψ p) ((selfDualMeasure ψ).prod ((selfDualMeasure ψ).prod (selfDualMeasure ψ))) := by
  have hι : Continuous (fun t : F × F × F => (!![t.1, t.2.1; t.2.2, 1] : Matrix (Fin 2) (Fin 2) F)) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hr : Continuous (fun M : Matrix (Fin 2) (Fin 2) F => ((M 0 0, M 0 1, M 1 0) : F × F × F)) := by
    fun_prop
  have hc : HasCompactSupport (fun t : F × F × F => p !![t.1, t.2.1; t.2.2, 1]) :=
    hcs_comp hp.2 _ _ hι hr (fun t => by simp)
  have hcont : Continuous (J ψ p) := by
    unfold J
    refine (hp.1.continuous.comp hι).mul ?_
    exact continuous_subtype_val.comp (hψ.comp (by fun_prop))
  exact hcont.integrable_of_hasCompactSupport (hc.mul_right)

theorem mul_Lpart {ψ : AddChar F Circle} (hψ : Continuous ψ) {p : Matrix (Fin 2) (Fin 2) F → ℂ} (hp : SB2 p) (u : F) :
    (ψ u : ℂ) * Lpart ψ (fun M => p ((uni2 (-u)).val * M)) =
      ∫ d, ∫ a, J ψ p (a, -u, d) ∂selfDualMeasure ψ ∂selfDualMeasure ψ := by
  set μ := selfDualMeasure ψ with hμ
  have hι : Continuous (fun y : F × F => (!![y.1 - u * y.2, -u; y.2, 1] : Matrix (Fin 2) (Fin 2) F)) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hr : Continuous (fun M : Matrix (Fin 2) (Fin 2) F => ((M 0 0 + u * M 1 0, M 1 0) : F × F)) := by
    fun_prop
  have hc : HasCompactSupport (fun y : F × F => p !![y.1 - u * y.2, -u; y.2, 1]) :=
    hcs_comp hp.2 _ _ hι hr (fun t => by simp)
  set h : F × F → ℂ := fun y => p !![y.1 - u * y.2, -u; y.2, 1] * (ψ (-y.2) : ℂ) with hh
  have hint : Integrable h (μ.prod μ) := by
    have hcont : Continuous h := by
      refine (hp.1.continuous.comp hι).mul ?_
      exact continuous_subtype_val.comp (hψ.comp (by fun_prop))
    exact hcont.integrable_of_hasCompactSupport hc.mul_right
  have hL : Lpart ψ (fun M => p ((uni2 (-u)).val * M)) = ∫ y, h y ∂(μ.prod μ) := by
    unfold Lpart LFS.vol2
    rw [← ((measurePreserving_finTwoArrow μ).symm MeasurableEquiv.finTwoArrow).integral_comp']
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have e0 : (MeasurableEquiv.finTwoArrow.symm y : Fin 2 → F) 0 = y.1 := rfl
    have e1 : (MeasurableEquiv.finTwoArrow.symm y : Fin 2 → F) 1 = y.2 := rfl
    have hm : (uni2 (-u)).val * col2 (MeasurableEquiv.finTwoArrow.symm y) = !![y.1 - u * y.2, -u; y.2, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [uni2, col2, e0, e1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    simp only [hh, hm, e1]
  rw [hL, integral_prod_symm h hint, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun d => ?_)
  have hs : ∫ x, h (x, d) ∂μ = ∫ a, p !![a, -u; d, 1] * (ψ (-d) : ℂ) ∂μ :=
    integral_sub_right_eq_self (fun a => p !![a, -u; d, 1] * (ψ (-d) : ℂ)) (u * d)
  simp only []
  rw [hs, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  have hψm : (ψ (-(-u + d)) : ℂ) = (ψ u : ℂ) * (ψ (-d) : ℂ) := by
    rw [show -(-u + d) = u + -d by ring, AddChar.map_add_eq_mul]; simp
  simp only [J, hψm]
  ring

theorem sliceForm : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ →
    ∀ p : Matrix (Fin 2) (Fin 2) F → ℂ, SB2 p →
      ∫ u, (ψ u : ℂ) * Lpart ψ (fun M => p ((uni2 (-u)).val * M)) ∂selfDualMeasure ψ = rr ψ p 1 := by
  intro F _ _ _ _ _ _ ψ hψ p hp
  have h1 : ∫ u, (ψ u : ℂ) * Lpart ψ (fun M => p ((uni2 (-u)).val * M)) ∂selfDualMeasure ψ =
      ∫ u, (fun b => ∫ d, ∫ a, J ψ p (a, b, d) ∂selfDualMeasure ψ ∂selfDualMeasure ψ) (-u) ∂selfDualMeasure ψ :=
    integral_congr_ae (Filter.Eventually.of_forall fun u => mul_Lpart hψ.1 hp u)
  have h2 := integral_neg_eq_self (fun b => ∫ d, ∫ a, J ψ p (a, b, d) ∂selfDualMeasure ψ ∂selfDualMeasure ψ)
    (selfDualMeasure ψ)
  rw [h1, h2, fubini3 _ _ (integrable_J hψ.1 hp)]
  rfl

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Slice
