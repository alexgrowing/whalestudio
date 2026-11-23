import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchAt
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace GlobalTheory.ThetaDecay

theorem arch_bound_functional (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n d : ℕ) (g : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] AF F) (w : InfinitePlace F)
    (x : Matrix (Fin n) (Fin d) (AE F E)) (B : ℝ) (hB : 0 ≤ B)
    (hx : ∀ k l r, ‖archAt F w ((coB F E).repr (x k l) r)‖ ≤ B) :
    ‖archAt F w (g x)‖ ≤ B * ∑ k, ∑ l, ∑ r, ‖archAt F w (g (Matrix.single k l (coB F E r)))‖ := by
  have hx' : x = ∑ k, ∑ l, ∑ r, (coB F E).repr (x k l) r • Matrix.single k l (coB F E r) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single x]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    conv_lhs => rw [← (coB F E).sum_repr (x k l)]
    simp only [Matrix.smul_single]
    exact map_sum (Matrix.singleAddMonoidHom k l) _ _
  rw [hx']
  simp only [map_sum, map_smul, smul_eq_mul, map_mul]
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hx k l r) (norm_nonneg _)

theorem arch_bound_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (κ : Type) [Fintype κ]
    (f : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] (κ → AF F) × (κ → AF F)), ∃ K : ℝ, 0 ≤ K ∧
    ∀ (x : Matrix (Fin n) (Fin d) (AE F E)) (B : ℝ), 0 ≤ B →
    (∀ w k l r, ‖archAt F w ((coB F E).repr (x k l) r)‖ ≤ B) →
    ∀ w i, ‖archAt F w ((f x).1 i)‖ ≤ K * B ∧ ‖archAt F w ((f x).2 i)‖ ≤ K * B := by
  intro F E _ _ _ _ _ n d κ _ f
  classical
  let S : InfinitePlace F → κ → ℝ := fun w i =>
    (∑ k, ∑ l, ∑ r, ‖archAt F w ((f (Matrix.single k l (coB F E r))).1 i)‖) +
    ∑ k, ∑ l, ∑ r, ‖archAt F w ((f (Matrix.single k l (coB F E r))).2 i)‖
  have hS : ∀ w i, 0 ≤ S w i := fun w i => by positivity
  refine ⟨∑ w, ∑ i, S w i, Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun i _ => hS w i, ?_⟩
  intro x B hB hx w i
  have hle : S w i ≤ ∑ w, ∑ i, S w i :=
    (Finset.single_le_sum (f := fun i => S w i) (fun i _ => hS w i) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun w => ∑ i, S w i)
        (fun w _ => Finset.sum_nonneg fun i _ => hS w i) (Finset.mem_univ w))
  have h1 := arch_bound_functional F E n d ((LinearMap.proj i).comp ((LinearMap.fst _ _ _).comp f)) w x B hB (hx w)
  have h2 := arch_bound_functional F E n d ((LinearMap.proj i).comp ((LinearMap.snd _ _ _).comp f)) w x B hB (hx w)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval,
    LinearMap.fst_apply, LinearMap.snd_apply] at h1 h2
  have hA : 0 ≤ ∑ k, ∑ l, ∑ r, ‖archAt F w ((f (Matrix.single k l (coB F E r))).1 i)‖ := by positivity
  have hC : 0 ≤ ∑ k, ∑ l, ∑ r, ‖archAt F w ((f (Matrix.single k l (coB F E r))).2 i)‖ := by positivity
  constructor
  · refine h1.trans ((mul_le_mul_of_nonneg_left ?_ hB).trans_eq (mul_comm _ _))
    exact (le_add_of_nonneg_right hC).trans hle
  · refine h2.trans ((mul_le_mul_of_nonneg_left ?_ hB).trans_eq (mul_comm _ _))
    exact (le_add_of_nonneg_left hA).trans hle

end GlobalTheory.ThetaDecay
