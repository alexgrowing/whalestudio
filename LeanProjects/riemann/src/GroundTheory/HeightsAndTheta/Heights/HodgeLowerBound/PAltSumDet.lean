import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFibreSteps
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

namespace AltSumDet

def form (N r : ℕ) (V : (Fin r → Fin N) → ℂ) : MultilinearMap ℂ (fun _ : Fin r => Fin N → ℂ) ℂ :=
  ∑ q : Fin r → Fin N, V q • (MultilinearMap.mkPiAlgebra ℂ (Fin r) ℂ).compLinearMap
    (fun a => LinearMap.proj (q a))

theorem form_apply (N r : ℕ) (V : (Fin r → Fin N) → ℂ) (w : Fin r → Fin N → ℂ) :
    form N r V w = ∑ q, (∏ a, w a (q a)) * V q := by
  simp [form, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, mul_comm]

theorem sum_eq_zero_of_eq (N r : ℕ) (V : (Fin r → Fin N) → ℂ)
    (hV : ∀ q (σ : Equiv.Perm (Fin r)), V (q ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * V q)
    (w : Fin r → Fin N → ℂ) (i j : Fin r) (hw : w i = w j) (hij : i ≠ j) :
    ∑ q, (∏ a, w a (q a)) * V q = 0 := by
  have hw' : ∀ a, w (Equiv.swap i j a) = w a := by
    intro a
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, hw]
    · rw [h2, hw]
    · rfl
  have hterm : ∀ q : Fin r → Fin N,
      (∏ a, w a ((q ∘ Equiv.swap i j) a)) * V (q ∘ Equiv.swap i j) = -((∏ a, w a (q a)) * V q) := by
    intro q
    have hp : ∏ a, w a ((q ∘ Equiv.swap i j) a) = ∏ a, w a (q a) := by
      calc ∏ a, w a ((q ∘ Equiv.swap i j) a)
          = ∏ a, w (Equiv.swap i j a) (q (Equiv.swap i j a)) := by
            refine Finset.prod_congr rfl fun a _ => ?_
            rw [hw' a]; rfl
        _ = ∏ a, w a (q a) := Equiv.prod_comp (Equiv.swap i j) (fun a => w a (q a))
    rw [hp, hV, Equiv.Perm.sign_swap hij]
    simp
  let e : (Fin r → Fin N) ≃ (Fin r → Fin N) := (Equiv.swap i j).arrowCongr (Equiv.refl (Fin N))
  have he : ∀ q, e q = q ∘ Equiv.swap i j := by
    intro q
    ext a
    simp [e, Equiv.arrowCongr_apply, Equiv.symm_swap]
  have hS : ∑ q, (∏ a, w a (q a)) * V q = -∑ q, (∏ a, w a (q a)) * V q := by
    rw [← Finset.sum_neg_distrib]
    conv_lhs => rw [← Equiv.sum_comp e (fun q => (∏ a, w a (q a)) * V q)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [he q]
    exact hterm q
  linear_combination (1 / 2 : ℂ) * hS

def altForm (N r : ℕ) (V : (Fin r → Fin N) → ℂ)
    (hV : ∀ q (σ : Equiv.Perm (Fin r)), V (q ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * V q) :
    (Fin N → ℂ) [⋀^Fin r]→ₗ[ℂ] ℂ :=
  { form N r V with
    map_eq_zero_of_eq' := fun w i j hw hij => by
      change form N r V w = 0
      rw [form_apply]
      exact sum_eq_zero_of_eq N r V hV w i j hw hij }

theorem altForm_apply (N r : ℕ) (V : (Fin r → Fin N) → ℂ)
    (hV : ∀ q (σ : Equiv.Perm (Fin r)), V (q ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * V q)
    (w : Fin r → Fin N → ℂ) : altForm N r V hV w = ∑ q, (∏ a, w a (q a)) * V q :=
  form_apply N r V w

theorem proof : AltSumDet.Statement := by
  intro N r V A M _ hV
  let g : (Fin r → ℂ) [⋀^Fin r]→ₗ[ℂ] ℂ := (altForm N r V hV).compLinearMap A.mulVecLin
  have key := congrArg (fun F : (Fin r → ℂ) [⋀^Fin r]→ₗ[ℂ] ℂ => F (fun b a => M a b))
    (AlternatingMap.eq_smul_basis_det (Pi.basisFun ℂ (Fin r)) g)
  have hdet : (Pi.basisFun ℂ (Fin r)).det (fun b a => M a b) = M.det := by
    rw [Module.Basis.det_apply]
    congr 1
  have h1 : g (fun b a => M a b) = ∑ q, (∏ a, (A * M) (q a) a) * V q := by
    simp only [g, AlternatingMap.compLinearMap_apply, altForm_apply, Matrix.mulVecLin_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
  have h2 : g (Pi.basisFun ℂ (Fin r)) = ∑ q, (∏ a, A (q a) a) * V q := by
    simp only [g, AlternatingMap.compLinearMap_apply, altForm_apply, Matrix.mulVecLin_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    simp [Pi.basisFun_apply]
  simp only [AlternatingMap.smul_apply, smul_eq_mul, hdet] at key
  rw [← h1, ← h2, key, mul_comm]

end AltSumDet

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
