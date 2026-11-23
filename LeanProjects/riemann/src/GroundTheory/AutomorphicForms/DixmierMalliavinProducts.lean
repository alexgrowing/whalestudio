import Mathlib
import GroundTheory.AutomorphicForms.DixmierMalliavinBasic
import GroundTheory.AutomorphicForms.GKModules.SmoothVectors

namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory

set_option linter.unusedSectionVars false

theorem integral_fin_succ_cons {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    {F : (Fin (d + 1) → ℝ) → E} (hF : Integrable F) :
    ∫ t, F t = ∫ s, ∫ t', F (Fin.cons s t') := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have h1 := hmp.symm.integral_comp' F
  have hint : Integrable (fun p : ℝ × (Fin d → ℝ) =>
      F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm p))
      ((volume : Measure ℝ).prod (Measure.pi fun _ : Fin d => (volume : Measure ℝ))) :=
    (hmp.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF
  rw [← h1]
  refine (integral_prod _ hint).trans ?_
  congr 1; funext s; congr 1; funext t'
  congr 1
  simp [MeasurableEquiv.piFinSuccAbove]
  rfl

theorem contDiff_cons_kernel {d : ℕ} {a : ℝ → ℂ} {K : (Fin d → ℝ) → ℂ} (ha : ContDiff ℝ ∞ a)
    (hK : ContDiff ℝ ∞ K) : ContDiff ℝ ∞ (fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t)) :=
  (ha.comp (contDiff_apply ℝ ℝ 0)).mul
    (hK.comp (contDiff_pi.2 fun j => contDiff_apply ℝ ℝ j.succ))

theorem tsupport_cons_kernel {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {a : ℝ → ℂ} {K : (Fin d → ℝ) → ℂ}
    (has : tsupport a ⊆ Icc (-ε) ε)
    (hKs : tsupport K ⊆ Metric.closedBall 0 ε) :
    tsupport (fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t)) ⊆ Metric.closedBall 0 ε := by
  intro t ht
  have h1 := tsupport_mul_subset_left ht
  have h2 := tsupport_mul_subset_right ht
  have h1' : t 0 ∈ tsupport a :=
    tsupport_comp_subset_preimage a (f := fun t : Fin (d + 1) → ℝ => t 0) (continuous_apply 0) h1
  have h2' : Fin.tail t ∈ tsupport K :=
    tsupport_comp_subset_preimage K (f := fun t : Fin (d + 1) → ℝ => Fin.tail t)
      (continuous_pi fun j => continuous_apply j.succ) h2
  have ha' := has h1'
  have hK' := hKs h2'
  rw [mem_closedBall_zero_iff] at hK' ⊢
  refine (pi_norm_le_iff_of_nonneg hε).2 fun j => ?_
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [Real.norm_eq_abs, abs_le]; exact ha'
  · exact (norm_le_pi_norm (Fin.tail t) j).trans hK'

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

noncomputable def revProdExp {d : ℕ} (X : Fin d → 𝔤) (t : Fin d → ℝ) : G :=
  (List.ofFn fun i => h.expG (t i • X i)).reverse.prod

theorem revProdExp_zero (X : Fin 0 → 𝔤) (t : Fin 0 → ℝ) : h.revProdExp X t = 1 := by
  simp [revProdExp]

theorem revProdExp_succ {d : ℕ} (X : Fin (d + 1) → 𝔤) (t : Fin (d + 1) → ℝ) :
    h.revProdExp X t = h.revProdExp (Fin.tail X) (Fin.tail t) * h.expG (t 0 • X 0) := by
  simp [revProdExp, List.ofFn_succ, Fin.tail]

theorem continuous_revProdExp : ∀ {d : ℕ} (X : Fin d → 𝔤), Continuous (h.revProdExp X)
  | 0, X => by
    have : h.revProdExp X = fun _ => 1 := funext (h.revProdExp_zero X)
    rw [this]; exact continuous_const
  | d + 1, X => by
    have : h.revProdExp X =
        fun t => h.revProdExp (Fin.tail X) (Fin.tail t) * h.expG (t 0 • X 0) :=
      funext (h.revProdExp_succ X)
    rw [this]
    exact ((continuous_revProdExp (Fin.tail X)).comp
      (continuous_pi fun j => continuous_apply j.succ)).mul
      (h.continuous_expG.comp ((continuous_apply 0).smul continuous_const))

theorem revProdExp_inv {d : ℕ} (X : Fin d → 𝔤) (t : Fin d → ℝ) :
    (h.revProdExp X t)⁻¹ = h.prodExp X (-t) := by
  rw [revProdExp, List.prod_inv_reverse, List.map_reverse, List.reverse_reverse, prodExp,
    List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  simp [neg_smul, h.expG_neg]

theorem integral_cons_kernel {d : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} (hε : 0 ≤ ε) {a : ℝ → ℂ}
    (ha : Continuous a) (has : tsupport a ⊆ Icc (-ε) ε) {K : (Fin d → ℝ) → ℂ}
    (hK : Continuous K) (hKs : tsupport K ⊆ Metric.closedBall 0 ε) {F : G → ℂ}
    (hF : Continuous F) (x : G) :
    ∫ t, a (t 0) * K (Fin.tail t) * F (h.revProdExp X t * x) =
      ∫ s, ∫ t', a s * (K t' * F (h.revProdExp (Fin.tail X) t' * (h.expG (s • X 0) * x))) := by
  have hint : Integrable
      (fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t) * F (h.revProdExp X t * x)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((ha.comp (continuous_apply 0)).mul
        (hK.comp (continuous_pi fun j => continuous_apply j.succ))).mul
        (hF.comp ((h.continuous_revProdExp X).mul continuous_const))
    · exact HasCompactSupport.mul_right (f := fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t))
        ((isCompact_closedBall 0 ε).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_cons_kernel hε has hKs))
  rw [integral_fin_succ_cons hint]
  congr 1; funext s; congr 1; funext t'
  simp only [Fin.cons_zero, Fin.tail_cons, h.revProdExp_succ, mul_assoc]

theorem integrable_integral_cons_kernel {d : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} {a : ℝ → ℂ}
    (ha : Continuous a) (has : tsupport a ⊆ Icc (-ε) ε) {K : (Fin d → ℝ) → ℂ}
    (hK : Continuous K) (hKs : tsupport K ⊆ Metric.closedBall 0 ε) {F : G → ℂ}
    (hF : Continuous F) (x : G) :
    Integrable (fun s : ℝ =>
      ∫ t', a s * (K t' * F (h.revProdExp (Fin.tail X) t' * (h.expG (s • X 0) * x)))) := by
  have hc : Continuous (fun p : ℝ × (Fin d → ℝ) =>
      a p.1 * (K p.2 * F (h.revProdExp (Fin.tail X) p.2 * (h.expG (p.1 • X 0) * x)))) :=
    (ha.comp continuous_fst).mul ((hK.comp continuous_snd).mul (hF.comp
      (((h.continuous_revProdExp (Fin.tail X)).comp continuous_snd).mul
        ((h.continuous_expG.comp (continuous_fst.smul continuous_const)).mul continuous_const))))
  have hs : HasCompactSupport (fun p : ℝ × (Fin d → ℝ) =>
      a p.1 * (K p.2 * F (h.revProdExp (Fin.tail X) p.2 * (h.expG (p.1 • X 0) * x)))) := by
    refine HasCompactSupport.intro
      ((isCompact_Icc (a := -ε) (b := ε)).prod (isCompact_closedBall (0 : Fin d → ℝ) ε)) ?_
    intro p hp
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (has h')), zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (hKs h')), zero_mul, mul_zero]
  exact (hc.integrable_of_hasCompactSupport hs).integral_prod_left

theorem sum_integral_cons_kernel {d m : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} (hε : 0 ≤ ε)
    {a : ℝ → ℂ} (ha : Continuous a) (has : tsupport a ⊆ Icc (-ε) ε)
    {K : Fin m → (Fin d → ℝ) → ℂ} (hK : ∀ i, Continuous (K i))
    (hKs : ∀ i, tsupport (K i) ⊆ Metric.closedBall 0 ε) {F : Fin m → G → ℂ}
    (hF : ∀ i, Continuous (F i)) {f₁ : G → ℂ}
    (hd : ∀ y, f₁ y = ∑ i, ∫ t', K i t' * F i (h.revProdExp (Fin.tail X) t' * y)) (x : G) :
    ∑ i, ∫ t, a (t 0) * K i (Fin.tail t) * F i (h.revProdExp X t * x) =
      ∫ s, a s * f₁ (h.expG (s • X 0) * x) := by
  rw [Finset.sum_congr rfl fun i _ => h.integral_cons_kernel X hε ha has (hK i) (hKs i) (hF i) x,
    ← integral_finsetSum _ fun i _ =>
      h.integrable_integral_cons_kernel X ha has (hK i) (hKs i) (hF i) x]
  congr 1; funext s
  rw [hd, Finset.mul_sum]
  congr 1; funext i
  rw [← integral_const_mul]

end IsExpLieAlgebra

end GroundTheory.Automorphic
