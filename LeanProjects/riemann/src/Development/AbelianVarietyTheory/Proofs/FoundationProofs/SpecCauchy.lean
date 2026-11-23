import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KA

theorem spec_cauchy : ∀ (l : ℕ) [Fact l.Prime] {Γ : Type} [Group Γ] (Y : ∀ r : ℕ, Γ → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l), (∀ r s x i, ‖Y r s x i‖ ≤ 1) → (∀ r x, ‖η r x‖ ≤ 1) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → (∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖η (r + 1) x - η r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∀ r s i, ‖spec (η (r + 1)) (Y (r + 1)) s i - spec (η r) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  intro l _ Γ _ Y η hY hη hYp hηc r s i
  set red := (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) with hred
  have hpush : spec (η r) (Y r) s i = ∑ x', η r (red x') * Y (r + 1) s x' i := by
    simp only [spec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hYp r s]
    simp only [push, Finset.sum_apply, Finset.mul_sum]
    rw [← Finset.sum_fiberwise (Finset.univ) red (fun x' => η r (red x') * Y (r + 1) s x' i)]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' hx' => ?_
    rw [(Finset.mem_filter.mp hx').2]
  have hspec : spec (η (r + 1)) (Y (r + 1)) s i = ∑ x', η (r + 1) x' * Y (r + 1) s x' i := by
    simp only [spec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hpush, hspec, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun x' _ => ?_
  rw [← sub_mul, norm_mul]
  calc ‖η (r + 1) x' - η r (red x')‖ * ‖Y (r + 1) s x' i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ * 1 :=
        mul_le_mul (hηc r x') (hY _ _ _ _) (norm_nonneg _) (norm_nonneg _)
    _ = _ := mul_one _

end GlobalTheory.KA
