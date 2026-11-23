import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

open scoped TensorProduct
open Algebra.TensorProduct (includeRight)

namespace GlobalTheory.CompanionTheory.NormLoc

section

variable {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O']

theorem trace_fixed (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (hτ : τ ^ ℓ = 1) (u : O') :
    τ (∑ j ∈ Finset.range ℓ, (τ ^ j) u) = ∑ j ∈ Finset.range ℓ, (τ ^ j) u := by
  rw [map_sum]
  have e := (Finset.sum_range_succ' (fun j => (τ ^ j) u) ℓ).symm.trans
    (Finset.sum_range_succ (fun j => (τ ^ j) u) ℓ)
  rw [hτ, pow_zero] at e
  rw [← add_right_cancel e]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_succ', AlgEquiv.mul_apply]

theorem exists_trace_one [IsLocalRing O] [Module.Finite O O'] (ℓ : ℕ) (τ : O' ≃ₐ[O] O')
    (hℓ : 0 < ℓ) (hτ : τ ^ ℓ = 1)
    (hfix : ∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O'))
    (hdual : ∃ x y : Fin ℓ → O', ∀ j < ℓ, ∑ i, x i * (τ ^ j) (y i) = if j = 0 then 1 else 0) :
    ∃ a : O', ∑ j ∈ Finset.range ℓ, (τ ^ j) a = 1 := by
  obtain ⟨x, y, hxy⟩ := hdual
  have hc : ∀ i, ∃ c : O, algebraMap O O' c = ∑ j ∈ Finset.range ℓ, (τ ^ j) (y i) := fun i =>
    hfix _ (GlobalTheory.CompanionTheory.NormLoc.trace_fixed ℓ τ hτ (y i))
  choose c hc using hc
  have hsum : ∑ i, x i * algebraMap O O' (c i) = 1 := by
    simp_rw [hc, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun j hj => hxy j (Finset.mem_range.mp hj)]
    simp [hℓ]
  by_cases hunit : ∃ i, IsUnit (c i)
  · obtain ⟨i, u, hu⟩ := hunit
    refine ⟨algebraMap O O' (↑u⁻¹ : O) * y i, ?_⟩
    have h : ∀ j, (τ ^ j) (algebraMap O O' (↑u⁻¹ : O) * y i) =
        algebraMap O O' (↑u⁻¹ : O) * (τ ^ j) (y i) := by
      intro j
      rw [map_mul, AlgEquiv.commutes]
    simp_rw [h]
    rw [← Finset.mul_sum, ← hc i, ← map_mul, ← hu, Units.inv_mul, map_one]
  · push_neg at hunit
    have htop : (⊤ : Submodule O O') ≤ IsLocalRing.maximalIdeal O • ⊤ := by
      intro z _
      have hz : z = ∑ i, c i • (z * x i) := by
        simp_rw [Algebra.smul_def]
        calc z = z * 1 := (mul_one z).symm
          _ = _ := by
            rw [← hsum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
      rw [hz]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hunit i
    have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal O) ⊤
      Module.Finite.fg_top htop (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    have h1 : (1 : O') = 0 := by
      have : (1 : O') ∈ (⊤ : Submodule O O') := Submodule.mem_top
      rw [hbot] at this
      exact this
    haveI : Subsingleton O' := subsingleton_of_zero_eq_one h1.symm
    exact ⟨0, Subsingleton.elim _ _⟩

variable {R : Type} [CommRing R] [Algebra O R]

theorem map_pow_succ_apply (τ : O' ≃ₐ[O] O') (j : ℕ) (t : O' ⊗[O] R) :
    Algebra.TensorProduct.map ((τ ^ (j + 1) : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) t =
      Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R)
        (Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u r => simp [Algebra.TensorProduct.map_tmul, pow_succ']
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_pow_fixed (τ : O' ≃ₐ[O] O') (s : O' ⊗[O] R)
    (hs : Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) s = s) (j : ℕ) :
    Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) s = s := by
  induction j with
  | zero =>
    clear hs
    induction s using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x r => simp
    | add x y hx hy => rw [map_add, hx, hy]
  | succ j ih => rw [GlobalTheory.CompanionTheory.NormLoc.map_pow_succ_apply, ih, hs]

theorem trace_tensor_mem (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (hτ : τ ^ ℓ = 1)
    (hfix : ∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O')) (t : O' ⊗[O] R) :
    ∑ j ∈ Finset.range ℓ,
        Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) t ∈
      Set.range (includeRight : R →ₐ[O] O' ⊗[O] R) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x r =>
    obtain ⟨c, hc⟩ := hfix _ (GlobalTheory.CompanionTheory.NormLoc.trace_fixed ℓ τ hτ x)
    refine ⟨c • r, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.toAlgHom_eq_coe,
      AlgEquiv.coe_algHom]
    rw [← TensorProduct.sum_tmul, ← hc, Algebra.TensorProduct.includeRight_apply,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp only [map_add, Finset.sum_add_distrib, ha, hb]⟩

theorem fixed_mem_range (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (hτ : τ ^ ℓ = 1)
    (hfix : ∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O')) (a : O')
    (ha : ∑ j ∈ Finset.range ℓ, (τ ^ j) a = 1) (s : O' ⊗[O] R)
    (hs : Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) s = s) :
    s ∈ Set.range (includeRight : R →ₐ[O] O' ⊗[O] R) := by
  have key : ∑ j ∈ Finset.range ℓ, Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom)
      (AlgHom.id O R) ((a ⊗ₜ[O] (1 : R)) * s) = s := by
    simp only [map_mul, GlobalTheory.CompanionTheory.NormLoc.map_pow_fixed τ s hs]
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.toAlgHom_eq_coe,
      AlgEquiv.coe_algHom, map_one]
    rw [← Finset.sum_mul, ← TensorProduct.sum_tmul, ha, ← Algebra.TensorProduct.one_def, one_mul]
  rw [← key]
  exact GlobalTheory.CompanionTheory.NormLoc.trace_tensor_mem ℓ τ hτ hfix _

theorem prod_one_add_tmul_sub_mem (J : Ideal R) (m : ℕ) (hm : 1 ≤ m) (r : R) (hr : r ∈ J ^ m)
    (S : Finset ℕ) (b : ℕ → O') :
    (∏ j ∈ S, (1 + b j ⊗ₜ[O] r)) - (1 + (∑ j ∈ S, b j) ⊗ₜ[O] r) ∈
      Ideal.map (includeRight : R →ₐ[O] O' ⊗[O] R) (J ^ (m + 1)) := by
  classical
  have hrr : r * r ∈ J ^ (m + 1) := by
    have h := Ideal.mul_mem_mul hr hr
    rw [← pow_add] at h
    exact Ideal.pow_le_pow_right (by omega) h
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk]
    have h : (1 + b k ⊗ₜ[O] r) * ∏ j ∈ S, (1 + b j ⊗ₜ[O] r) - (1 + (b k + ∑ j ∈ S, b j) ⊗ₜ[O] r)
        = (1 + b k ⊗ₜ[O] r) * (∏ j ∈ S, (1 + b j ⊗ₜ[O] r) - (1 + (∑ j ∈ S, b j) ⊗ₜ[O] r))
          + (b k * ∑ j ∈ S, b j) ⊗ₜ[O] (r * r) := by
      rw [TensorProduct.add_tmul, ← Algebra.TensorProduct.tmul_mul_tmul]
      ring
    rw [h]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) ?_
    have h' : (b k * ∑ j ∈ S, b j) ⊗ₜ[O] (r * r) =
        ((b k * ∑ j ∈ S, b j) ⊗ₜ[O] (1 : R)) * (includeRight : R →ₐ[O] O' ⊗[O] R) (r * r) := by
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        one_mul]
    rw [h']
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hrr)

end

theorem fixedRing_traceOne_firstOrder : PositivityTheory.Rg.Tf.Loc.N2 := by
  unfold PositivityTheory.Rg.Tf.Loc.N2
  intro O O' R _ _ _ _ _ _ _ _ _ _ _ _ ℓ τ hℓ hτ hfix hdual
  obtain ⟨a, ha⟩ := GlobalTheory.CompanionTheory.NormLoc.exists_trace_one ℓ τ hℓ hτ hfix hdual
  refine ⟨fun s hs => GlobalTheory.CompanionTheory.NormLoc.fixed_mem_range ℓ τ hτ hfix a ha s hs, a, ha, ?_⟩
  intro m hm r hr
  have key := GlobalTheory.CompanionTheory.NormLoc.prod_one_add_tmul_sub_mem (O := O) (O' := O') (Ideal.jacobson (⊥ : Ideal R)) m hm r hr
    (Finset.range ℓ) (fun j => (τ ^ j) a)
  have e1 : ∏ j ∈ Finset.range ℓ, Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom)
      (AlgHom.id O R) (1 + a ⊗ₜ[O] r) = ∏ j ∈ Finset.range ℓ, (1 + (τ ^ j) a ⊗ₜ[O] r) :=
    Finset.prod_congr rfl fun j _ => by simp
  have e2 : (includeRight : R →ₐ[O] O' ⊗[O] R) (1 + r) =
      1 + (∑ j ∈ Finset.range ℓ, (τ ^ j) a) ⊗ₜ[O] r := by
    rw [ha, Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_add,
      ← Algebra.TensorProduct.one_def]
  rw [← e1, ← e2] at key
  exact key

end GlobalTheory.CompanionTheory.NormLoc
