import Mathlib

namespace Bl.FirstLemmaE

theorem goal1 :
  ∀ {L : Type} [inst : NontriviallyNormedField.{0} L] [IsUltrametricDist.{0} L] {ι : Type} (s : Finset.{0} ι)
  (f g : ι → L) {r : Real},
  LE.le.{0} 0 r →
    (∀ (i : ι), LE.le.{0} (Norm.norm.{0} (f i)) 1) →
      (∀ (i : ι), LE.le.{0} (Norm.norm.{0} (g i)) 1) →
        (∀ (i : ι), LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (f i) (g i))) r) →
          LE.le.{0}
            (Norm.norm.{0}
              (HSub.hSub.{0, 0, 0} (Finset.prod.{0, 0} s fun (i : ι) ↦ f i) (Finset.prod.{0, 0} s fun (i : ι) ↦ g i)))
            r := by
  intro L _ _ ι s f g r hr hf hg hfg
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hG : ‖∏ i ∈ t, g i‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hg i)
    have key : f a * ∏ i ∈ t, f i - g a * ∏ i ∈ t, g i
        = f a * (∏ i ∈ t, f i - ∏ i ∈ t, g i) + (f a - g a) * ∏ i ∈ t, g i := by ring
    rw [key]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖f a‖ * ‖∏ i ∈ t, f i - ∏ i ∈ t, g i‖ ≤ 1 * r :=
            mul_le_mul (hf a) ih (norm_nonneg _) zero_le_one
        _ = r := one_mul r
    · rw [norm_mul]
      calc ‖f a - g a‖ * ‖∏ i ∈ t, g i‖ ≤ r * 1 :=
            mul_le_mul (hfg a) hG (norm_nonneg _) hr
        _ = r := mul_one r

end Bl.FirstLemmaE
