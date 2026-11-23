import Mathlib

open Module

namespace GlobalTheory.FiniteCover

theorem finrank_le_of_range_le {K P Q E : Type*} [Field K] [AddCommGroup P] [Module K P]
    [AddCommGroup Q] [Module K Q] [AddCommGroup E] [Module K E] [Module.Finite K Q]
    (L : P →ₗ[K] E) (hL : Function.Injective L) (B : Q →ₗ[K] E) (h : ∀ p, ∃ q, B q = L p) :
    finrank K P ≤ finrank K Q := by
  rw [← LinearMap.finrank_range_of_inj hL]
  refine (Submodule.finrank_mono (t := LinearMap.range B) ?_).trans B.finrank_range_le
  rintro _ ⟨p, rfl⟩
  exact h p

theorem exists_denominator {A C F F' ι : Type*} [CommRing A] [IsDomain A] [CommRing C] [IsDomain C]
    [Field F] [Field F'] [Algebra A C] [Module.Finite A C] [Algebra A F] [IsFractionRing A F]
    [Algebra C F'] [IsFractionRing C F'] [Algebra F F'] [Algebra A F'] [IsScalarTower A F F']
    [IsScalarTower A C F'] [Fintype ι] (e : Basis ι F F') :
    ∃ c : A, c ≠ 0 ∧
      (∀ j (y : C), ∃ a : A, algebraMap A F a = algebraMap A F c * e.repr (algebraMap C F' y) j) ∧
      ∀ j, ∃ y : C, algebraMap C F' y = algebraMap A F c • e j := by
  classical
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := C)
  obtain ⟨c₁, hc₁⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A)
    (fun p : ι × Fin n => e.repr (algebraMap C F' (g p.2)) p.1)
  have h2 : ∀ j, ∃ c : A, c ≠ 0 ∧ ∃ y : C, algebraMap C F' y = algebraMap A F c • e j := by
    intro j
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := C) (e j)
    have hinj : Function.Injective (algebraMap A C) := by
      have : Function.Injective (algebraMap A F') := by
        rw [IsScalarTower.algebraMap_eq A F F']
        exact (algebraMap F F').injective.comp (IsFractionRing.injective A F)
      rw [IsScalarTower.algebraMap_eq A C F'] at this
      exact Function.Injective.of_comp this
    have hal : IsAlgebraic A q := (Algebra.IsIntegral.isIntegral (R := A) q).isAlgebraic
    obtain ⟨c, hc, z, hz⟩ := hal.exists_nonzero_dvd hq
    refine ⟨c, hc, z * p, ?_⟩
    have hq' : algebraMap C F' q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    rw [← hpq, Algebra.smul_def, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A C F', hz, map_mul, map_mul]
    field_simp
  choose c₂ hc₂ y₂ hy₂ using h2
  refine ⟨c₁ * ∏ j, c₂ j, mul_ne_zero (nonZeroDivisors.coe_ne_zero c₁)
    (Finset.prod_ne_zero_iff.2 fun j _ => hc₂ j), fun j y => ?_, fun j => ?_⟩
  · have hy : y ∈ Submodule.span A (Set.range g) := hg ▸ Submodule.mem_top
    suffices h : ∃ a : A, algebraMap A F a = algebraMap A F c₁ * e.repr (algebraMap C F' y) j by
      obtain ⟨a, ha⟩ := h
      exact ⟨a * ∏ j, c₂ j, by rw [map_mul, map_mul, ha]; ring⟩
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      obtain ⟨a, ha⟩ := hc₁ (j, k)
      exact ⟨a, by rw [ha, Algebra.smul_def]⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, map_add, map_add, Finsupp.add_apply, ha, hb, mul_add]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨r * a, ?_⟩
      have : algebraMap C F' (r • x) = algebraMap A F r • algebraMap C F' x := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
      rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, ha]
      ring
  · refine ⟨(c₁ * ∏ k ∈ Finset.univ.erase j, c₂ k : A) • y₂ j, ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), ← mul_assoc, map_mul (algebraMap A F) _ (c₂ j),
      mul_smul (algebraMap A F _), ← hy₂, Algebra.smul_def, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem exists_common_multiple {F I : Type*} [Field F] [Fintype I] (A : I → Subring F) (ρ c : I → F)
    (hρ : ∀ i, ρ i ≠ 0) (hc : ∀ i, c i ≠ 0) (hr : ∀ i k, ρ i / ρ k ∈ A k)
    (hext : ∀ i k, ∃ m : ℕ, c i * (ρ i / ρ k) ^ m ∈ A k) :
    ∃ (a : ℕ) (u : F), u ≠ 0 ∧ ∀ i, ∃ b ∈ A i, u = ρ i ^ a * c i * b := by
  classical
  choose m hm using hext
  let M : I → ℕ := fun i => ∑ k, m i k
  have hM : ∀ i k, c i * (ρ i / ρ k) ^ M i ∈ A k := fun i k => by
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le
      (Finset.single_le_sum (f := m i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
    change c i * (ρ i / ρ k) ^ (∑ k, m i k) ∈ A k
    rw [hl, pow_add, ← mul_assoc]
    exact mul_mem (hm i k) (pow_mem (hr i k) _)
  refine ⟨∑ i, M i, ∏ i, c i * ρ i ^ M i,
    Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hc i) (pow_ne_zero _ (hρ i)), fun k => ?_⟩
  refine ⟨∏ i ∈ Finset.univ.erase k, c i * (ρ i / ρ k) ^ M i, prod_mem fun i _ => hM i k, ?_⟩
  have e : ∀ i, c i * ρ i ^ M i = ρ k ^ M i * (c i * (ρ i / ρ k) ^ M i) := fun i => by
    have := hρ k
    rw [div_pow]
    field_simp
  rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ k), div_self (hρ k), one_pow, mul_one, mul_assoc]

theorem finrank_sandwich {K F F' I : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Fintype I] {d : ℕ} (e : Basis (Fin d) F F')
    (A : I → Subring F) (C : I → Subring F') (ρ c : I → F)
    (hρ : ∀ i, ρ i ≠ 0) (hc : ∀ i, c i ≠ 0) (hr : ∀ i k, ρ i / ρ k ∈ A k)
    (hext : ∀ i k, ∃ m : ℕ, c i * (ρ i / ρ k) ^ m ∈ A k)
    (hAC : ∀ i, ∀ a ∈ A i, algebraMap F F' a ∈ C i)
    (hc₁ : ∀ i j, ∀ y ∈ C i, c i * e.repr y j ∈ A i) (hc₂ : ∀ i j, c i • e j ∈ C i)
    (V W : ℕ → Type*) [∀ t, AddCommGroup (V t)] [∀ t, Module K (V t)] [∀ t, AddCommGroup (W t)]
    [∀ t, Module K (W t)] (hV : ∀ t, Module.Finite K (V t)) (hW : ∀ t, Module.Finite K (W t))
    (α : ∀ t, V t →ₗ[K] F) (β : ∀ t, W t →ₗ[K] F') (hα : ∀ t, Function.Injective (α t))
    (hβ : ∀ t, Function.Injective (β t))
    (rα : ∀ t x, (∃ v, α t v = x) ↔ ∀ i, ∃ a ∈ A i, x = a * ρ i ^ t)
    (rβ : ∀ t y, (∃ w, β t w = y) ↔ ∀ i, ∃ a ∈ C i, y = a * algebraMap F F' (ρ i ^ t)) :
    ∃ a : ℕ, ∀ t : ℕ, d * finrank K (V t) ≤ finrank K (W (t + a)) ∧
      finrank K (W t) ≤ d * finrank K (V (t + a)) := by
  obtain ⟨a, u, hu, hub⟩ := exists_common_multiple A ρ c hρ hc hr hext
  have hpi : ∀ t, finrank K (Fin d → V t) = d * finrank K (V t) := fun t => by
    rw [Module.finrank_pi_fintype]
    simp
  refine ⟨a, fun t => ⟨?_, ?_⟩⟩
  · rw [← hpi]
    let L : (Fin d → V t) →ₗ[K] F' :=
      ((e.equivFun.symm.toLinearMap.restrictScalars K).comp
        (((LinearMap.mulLeft K u).comp (α t)).compLeft (Fin d)))
    have hL : ∀ v, L v = ∑ j, (u * α t (v j)) • e j := fun v => e.equivFun_symm_apply _
    refine finrank_le_of_range_le L ?_ (β (t + a)) fun v => (rβ _ _).2 fun i => ?_
    · intro v w h
      have h' := e.equivFun.symm.injective h
      funext j
      exact hα t (mul_left_cancel₀ hu (congrFun h' j))
    · obtain ⟨b, hb, rfl⟩ := hub i
      choose x hx hx' using fun j => (rα t _).1 ⟨v j, rfl⟩ i
      refine ⟨∑ j, algebraMap F F' (b * x j) * (c i • e j),
        sum_mem fun j _ => mul_mem (hAC i _ (mul_mem hb (hx j))) (hc₂ i j), ?_⟩
      rw [hL, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hx' j]
      simp only [Algebra.smul_def, map_mul, map_pow, pow_add]
      ring
  · rw [← hpi]
    let L : W t →ₗ[K] (Fin d → F) := ((LinearMap.mulLeft K u).compLeft (Fin d)).comp
      ((e.equivFun.toLinearMap.restrictScalars K).comp (β t))
    have hL : ∀ w j, L w j = u * e.repr (β t w) j := fun w j => rfl
    refine finrank_le_of_range_le L ?_ ((α (t + a)).compLeft (Fin d)) fun w => ?_
    · intro v w h
      refine hβ t (e.equivFun.injective (funext fun j => ?_))
      exact mul_left_cancel₀ hu (congrFun h j)
    · have key : ∀ j, ∃ v, α (t + a) v = L w j := fun j => (rα _ _).2 fun i => by
        obtain ⟨b, hb, hub⟩ := hub i
        obtain ⟨y, hy, hy'⟩ := (rβ t _).1 ⟨w, rfl⟩ i
        refine ⟨b * (c i * e.repr y j), mul_mem hb (hc₁ i j y hy), ?_⟩
        rw [hL, hy', mul_comm y, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, hub,
          pow_add]
        ring
      choose v hv using key
      exact ⟨v, funext hv⟩

end GlobalTheory.FiniteCover
