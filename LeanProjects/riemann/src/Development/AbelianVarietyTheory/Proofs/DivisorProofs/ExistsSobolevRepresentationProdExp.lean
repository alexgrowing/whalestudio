import Mathlib
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivExpGLineEqRightDerivPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueAtZeroEqSumIntegralKernelIteratedDerivStatement

open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory
namespace SobolevRep

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

theorem prodExp_succ {d : ℕ} (X : Fin (d + 1) → 𝔤) (t : Fin (d + 1) → ℝ) :
    h.prodExp X t = h.expG (t 0 • X 0) * h.prodExp (Fin.tail X) (Fin.tail t) := by
  simp [IsExpLieAlgebra.prodExp, List.ofFn_succ, Fin.tail]

theorem continuous_prodExp' {d : ℕ} (X : Fin d → 𝔤) : Continuous (h.prodExp X) := by
  have : h.prodExp X = fun t => (h.revProdExp X (-t))⁻¹ := by
    funext t; rw [h.revProdExp_inv, neg_neg]
  rw [this]
  exact ((h.continuous_revProdExp X).comp continuous_neg).inv

theorem isSmoothFun_foldr {f : G → ℂ} (hf : h.IsSmoothFun f) :
    ∀ l : List 𝔤, h.IsSmoothFun (l.foldr h.rightDeriv f)
  | [] => hf
  | X :: l => h.isSmoothFun_rightDeriv (isSmoothFun_foldr hf l) X

theorem continuous_of_isSmoothFun {f : G → ℂ} (hf : h.IsSmoothFun f) : Continuous f := by
  letI := h.chartedSpace
  exact ContMDiff.continuous hf

theorem integral_cons {d : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} (hε : 0 ≤ ε) {a : ℝ → ℂ}
    (ha : Continuous a) (has : tsupport a ⊆ Set.Icc (-ε) ε) {K : (Fin d → ℝ) → ℂ}
    (hK : Continuous K) (hKs : tsupport K ⊆ Metric.closedBall 0 ε) {F : G → ℂ}
    (hF : Continuous F) (x : G) :
    ∫ t, a (t 0) * K (Fin.tail t) * F (x * h.prodExp X t) =
      ∫ s, ∫ t', a s * (K t' * F (x * h.expG (s • X 0) * h.prodExp (Fin.tail X) t')) := by
  have hint : Integrable
      (fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t) * F (x * h.prodExp X t)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((ha.comp (continuous_apply 0)).mul
        (hK.comp (continuous_pi fun j => continuous_apply j.succ))).mul
        (hF.comp (continuous_const.mul (continuous_prodExp' h X)))
    · exact HasCompactSupport.mul_right (f := fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t))
        ((isCompact_closedBall 0 ε).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_cons_kernel hε has hKs))
  rw [integral_fin_succ_cons hint]
  congr 1; funext s; congr 1; funext t'
  simp only [Fin.cons_zero, Fin.tail_cons, prodExp_succ h, mul_assoc]

theorem integrable_integral_cons {d : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} {a : ℝ → ℂ}
    (ha : Continuous a) (has : tsupport a ⊆ Set.Icc (-ε) ε) {K : (Fin d → ℝ) → ℂ}
    (hK : Continuous K) (hKs : tsupport K ⊆ Metric.closedBall 0 ε) {F : G → ℂ}
    (hF : Continuous F) (x : G) :
    Integrable (fun s : ℝ =>
      ∫ t', a s * (K t' * F (x * h.expG (s • X 0) * h.prodExp (Fin.tail X) t'))) := by
  have hc : Continuous (fun p : ℝ × (Fin d → ℝ) =>
      a p.1 * (K p.2 * F (x * h.expG (p.1 • X 0) * h.prodExp (Fin.tail X) p.2))) :=
    (ha.comp continuous_fst).mul ((hK.comp continuous_snd).mul (hF.comp
      ((continuous_const.mul (h.continuous_expG.comp (continuous_fst.smul continuous_const))).mul
        ((continuous_prodExp' h (Fin.tail X)).comp continuous_snd))))
  have hs : HasCompactSupport (fun p : ℝ × (Fin d → ℝ) =>
      a p.1 * (K p.2 * F (x * h.expG (p.1 • X 0) * h.prodExp (Fin.tail X) p.2))) := by
    refine HasCompactSupport.intro
      ((isCompact_Icc (a := -ε) (b := ε)).prod (isCompact_closedBall (0 : Fin d → ℝ) ε)) ?_
    intro p hp
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (has h')), zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (hKs h')), zero_mul, mul_zero]
  exact (hc.integrable_of_hasCompactSupport hs).integral_prod_left

theorem sum_integral_cons {d m : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} (hε : 0 ≤ ε)
    {a : ℝ → ℂ} (ha : Continuous a) (has : tsupport a ⊆ Set.Icc (-ε) ε)
    {K : Fin m → (Fin d → ℝ) → ℂ} (hK : ∀ i, Continuous (K i))
    (hKs : ∀ i, tsupport (K i) ⊆ Metric.closedBall 0 ε) {F : Fin m → G → ℂ}
    (hF : ∀ i, Continuous (F i)) {f₁ : G → ℂ}
    (hd : ∀ y, f₁ y = ∑ i, ∫ t', K i t' * F i (y * h.prodExp (Fin.tail X) t')) (x : G) :
    ∑ i, ∫ t, a (t 0) * K i (Fin.tail t) * F i (x * h.prodExp X t) =
      ∫ s, a s * f₁ (x * h.expG (s • X 0)) := by
  rw [Finset.sum_congr rfl fun i _ => integral_cons h X hε ha has (hK i) (hKs i) (hF i) x,
    ← integral_finsetSum _ fun i _ =>
      integrable_integral_cons h X ha has (hK i) (hKs i) (hF i) x]
  congr 1; funext s
  rw [hd, Finset.mul_sum]
  congr 1; funext i
  rw [← integral_const_mul]

theorem exists_rep {ε : ℝ} (hε : 0 < ε) : ∀ (n : ℕ) (X : Fin n → 𝔤),
    ∃ (N : ℕ) (l : Fin N → List 𝔤) (κ : Fin N → (Fin n → ℝ) → ℂ),
      (∀ i, Continuous (κ i) ∧ tsupport (κ i) ⊆ Metric.closedBall 0 ε) ∧
      ∀ f : G → ℂ, h.IsSmoothFun f → ∀ g,
        f g = ∑ i, ∫ t, κ i t * (l i).foldr h.rightDeriv f (g * h.prodExp X t)
  | 0, X => by
    refine ⟨1, fun _ => [], fun _ _ => 1, fun _ => ⟨continuous_const, ?_⟩, fun f _ g => ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]; exact Metric.mem_closedBall_self hε.le
    · have hv : (volume : Measure (Fin 0 → ℝ)).real Set.univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      simp [IsExpLieAlgebra.prodExp, hv]
  | d + 1, X => by
    obtain ⟨N, l, K, hK, hrep⟩ := exists_rep hε d (Fin.tail X)
    obtain ⟨a, ha, hu⟩ := GlobalTheory.T.exists_kernels_eval_zero_eq_sum_integral_iteratedDeriv ε hε
    refine ⟨3 * N,
      fun j => l (finProdFinEquiv.symm j).2 ++ List.replicate (finProdFinEquiv.symm j).1 (X 0),
      fun j t => a (finProdFinEquiv.symm j).1 (t 0) * K (finProdFinEquiv.symm j).2 (Fin.tail t),
      fun j => ⟨?_, tsupport_cons_kernel hε.le (ha _).2 (hK _).2⟩, fun f hf g => ?_⟩
    · exact ((ha _).1.comp (continuous_apply 0)).mul
        ((hK _).1.comp (continuous_pi fun j => continuous_apply j.succ))
    · rw [← finProdFinEquiv.sum_comp]
      simp only [Equiv.symm_apply_apply, List.foldr_append]
      rw [Fintype.sum_prod_type]
      have h0 := hu _ (GlobalTheory.T.iteratedDeriv_expG_line_eq_foldr_rightDeriv 𝔸 G 𝔤 h f hf (X 0) g 0).1
      simp only [zero_smul, h.expG_zero, mul_one] at h0
      rw [h0]
      refine Finset.sum_congr rfl fun p _ => ?_
      have hp := isSmoothFun_foldr h hf (List.replicate p (X 0))
      rw [sum_integral_cons h X hε.le (ha p).1 (ha p).2 (fun i => (hK i).1) (fun i => (hK i).2)
        (fun i => continuous_of_isSmoothFun h (isSmoothFun_foldr h hp (l i))) (hrep _ hp) g]
      congr 1; funext s
      rw [(GlobalTheory.T.iteratedDeriv_expG_line_eq_foldr_rightDeriv 𝔸 G 𝔤 h f hf (X 0) g p).2 s]

end SobolevRep

theorem exists_sobolev_representation_prodExp :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
      (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (ε : ℝ), 0 < ε →
      ∀ (n : ℕ) (X : Fin n → 𝔤),
      ∃ (N : ℕ) (l : Fin N → List 𝔤) (κ : Fin N → (Fin n → ℝ) → ℂ),
        (∀ i, Continuous (κ i) ∧ tsupport (κ i) ⊆ Metric.closedBall 0 ε) ∧
        ∀ f : G → ℂ, h.IsSmoothFun f → ∀ g,
          f g = ∑ i, ∫ t, κ i t * (l i).foldr h.rightDeriv f (g * h.prodExp X t) :=
  fun _ _ _ _ _ _ _ h _ hε n X => SobolevRep.exists_rep h hε n X

end GlobalTheory
