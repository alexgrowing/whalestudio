import Mathlib

namespace Bl.ThirdBlockLemmaC

noncomputable def goal1 :
  {K : Type} →   [inst : Field K] →     [NumberField K] →       RingHom K K → Submodule (NumberField.RingOfIntegers K) K → Submodule (NumberField.RingOfIntegers K) K := @fun K _ _ σ M =>
  { carrier := σ ⁻¹' (M : Set K)
    add_mem' := fun {x y} hx hy => by
      simp only [Set.mem_preimage, map_add, SetLike.mem_coe] at *
      exact M.add_mem hx hy
    zero_mem' := by
      simp only [Set.mem_preimage, map_zero, SetLike.mem_coe]
      exact M.zero_mem
    smul_mem' := fun r x hx => by
      simp only [Set.mem_preimage, SetLike.mem_coe] at *
      have hr : IsIntegral ℤ (σ (r : K)) := (NumberField.RingOfIntegers.isIntegral_coe r).map σ.toIntAlgHom
      have h : σ (r • x) = (⟨σ (r : K), hr⟩ : NumberField.RingOfIntegers K) • σ x := by
        rw [Algebra.smul_def, map_mul, Algebra.smul_def]
        rfl
      rw [h]
      exact M.smul_mem _ hx }

end Bl.ThirdBlockLemmaC
