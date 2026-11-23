import Formalism.EllipticTorsion.VeluIntegralModel

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

namespace VeluIntegrality

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

def ball : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    rwa [norm_neg]

theorem mem_ball {x : K} : x ∈ (ball : Subring K) ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem veluGx_mem (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluGx W x y ∈ (ball : Subring K) := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  unfold veluGx
  refine sub_mem (add_mem (add_mem (mul_mem (ofNat_mem _ 3) (pow_mem hx 2))
    (mul_mem (mul_mem (ofNat_mem _ 2) h2) hx)) h4) (mul_mem h1 hy)

theorem veluGy_mem (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluGy W x y ∈ (ball : Subring K) := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  unfold veluGy
  exact sub_mem (sub_mem (mul_mem (neg_mem (ofNat_mem _ 2)) hy) (mul_mem h1 hx)) h3

theorem veluV_mem (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluV W x y ∈ (ball : Subring K) := by
  have gx := veluGx_mem W hW hx hy
  have gy := veluGy_mem W hW hx hy
  unfold veluV
  split_ifs
  · exact gx
  · exact sub_mem (mul_mem (ofNat_mem _ 2) gx) (mul_mem hW.1 gy)

theorem veluU_mem (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluU W x y ∈ (ball : Subring K) := by
  unfold veluU
  exact pow_mem (veluGy_mem W hW hx hy) 2

end VeluIntegrality

open VeluIntegrality in
theorem velu_integral_model : VeluIntegralModel := by
  intro K _ _ W k S hW hS
  have hx : ∀ i, (S i).1 ∈ (ball : Subring K) := fun i => (hS i).1
  have hy : ∀ i, (S i).2 ∈ (ball : Subring K) := fun i => (hS i).2
  have hv : (∑ i, veluV W (S i).1 (S i).2) ∈ (ball : Subring K) :=
    sum_mem fun i _ => veluV_mem W hW (hx i) (hy i)
  have hw : (∑ i, (veluU W (S i).1 (S i).2 + (S i).1 * veluV W (S i).1 (S i).2))
      ∈ (ball : Subring K) :=
    sum_mem fun i _ => add_mem (veluU_mem W hW (hx i) (hy i))
      (mul_mem (hx i) (veluV_mem W hW (hx i) (hy i)))
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · show W.a₄ - 5 * (∑ i, veluV W (S i).1 (S i).2) ∈ (ball : Subring K)
    exact sub_mem h4 (mul_mem (ofNat_mem _ 5) hv)
  · show W.a₆ - (W.a₁ ^ 2 + 4 * W.a₂) * (∑ i, veluV W (S i).1 (S i).2)
      - 7 * (∑ i, (veluU W (S i).1 (S i).2 + (S i).1 * veluV W (S i).1 (S i).2)) ∈ (ball : Subring K)
    exact sub_mem (sub_mem h6 (mul_mem (add_mem (pow_mem h1 2) (mul_mem (ofNat_mem _ 4) h2)) hv))
      (mul_mem (ofNat_mem _ 7) hw)

end Formalism.ELL
