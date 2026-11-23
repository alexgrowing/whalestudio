import Mathlib

noncomputable section

namespace Formalism.MainNotions.N

section Len

variable {O : Type} [CommRing O]

theorem length_le_of_span {M : Type} [AddCommGroup M] [Module O M] {n : ℕ} (m : Fin n → M) (a : O)
    (hspan : Submodule.span O (Set.range m) = ⊤) (hk : ∀ i, a • m i = 0) :
    Module.length O M ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  classical
  have hker : ∀ i, Ideal.span {a} ≤ LinearMap.ker (LinearMap.toSpanSingleton O M (m i)) := by
    intro i
    rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact hk i
  let ψ : Fin n → (O ⧸ Ideal.span {a}) →ₗ[O] M := fun i =>
    (Ideal.span {a}).liftQ (LinearMap.toSpanSingleton O M (m i)) (hker i)
  let φ : (Fin n → O ⧸ Ideal.span {a}) →ₗ[O] M := ∑ i, (ψ i).comp
    (LinearMap.proj i : (Fin n → O ⧸ Ideal.span {a}) →ₗ[O] O ⧸ Ideal.span {a})
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i (Submodule.Quotient.mk (1 : O)), ?_⟩
    show (∑ j, (ψ j).comp (LinearMap.proj j : (Fin n → O ⧸ Ideal.span {a}) →ₗ[O] O ⧸ Ideal.span {a}))
      (Pi.single i (Submodule.Quotient.mk (1 : O))) = m i
    first
      | rw [LinearMap.sum_apply]
      | rw [LinearMap.coe_fn_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · first
        | (show (ψ i) ((Pi.single i (Submodule.Quotient.mk (1 : O)) : Fin n → O ⧸ Ideal.span {a}) i) = m i
           rw [Pi.single_eq_same]
           show (LinearMap.toSpanSingleton O M (m i)) 1 = m i
           simp)
        | (simp [ψ]; exact one_smul O (m i))
        | (simp [ψ]; rfl)
    · intro j _ hj
      simp [hj]
    · simp
  calc Module.length O M ≤ Module.length O (Fin n → O ⧸ Ideal.span {a}) :=
        Module.length_le_of_surjective φ hsurj
    _ = (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
        first
          | (rw [Module.length_pi_of_fintype]; simp)
          | (rw [Module.length_pi]; simp)

private theorem length_le_length_ker_add_length {N P : Type} [AddCommGroup N] [Module O N]
    [AddCommGroup P] [Module O P] (f : N →ₗ[O] P) :
    Module.length O N ≤ Module.length O ↥(LinearMap.ker f) + Module.length O P := by
  have hs : Function.Surjective f.rangeRestrict := by
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  have hex : Function.Exact (LinearMap.ker f).subtype f.rangeRestrict := by
    first
      | exact LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype])
      | exact fun y => ⟨fun hy => ⟨⟨y, LinearMap.mem_ker.2 (congrArg Subtype.val hy)⟩, rfl⟩,
          by rintro ⟨z, rfl⟩; exact Subtype.ext (LinearMap.mem_ker.1 z.2)⟩
  rw [Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict
    Subtype.val_injective hs hex]
  exact add_le_add le_rfl
    (Module.length_le_of_injective (LinearMap.range f).subtype Subtype.val_injective)

theorem length_torsionBy_pow_le {M : Type} [AddCommGroup M] [Module O M] (a : O) (c : ℕ) :
    Module.length O ↥(Submodule.torsionBy O M (a ^ c)) ≤ (c : ℕ∞) * Module.length O ↥(Submodule.torsionBy O M a) := by
  induction c with
  | zero =>
    have hs : Subsingleton ↥(Submodule.torsionBy O M (a ^ 0)) := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      have h1 : ∀ z : M, a ^ 0 • z = 0 → z = 0 := fun z hz => by
        rwa [pow_zero, one_smul] at hz
      have hx := x.2
      have hy := y.2
      rw [Submodule.mem_torsionBy_iff] at hx hy
      rw [h1 _ hx, h1 _ hy]
    have h0 : Module.length O ↥(Submodule.torsionBy O M (a ^ 0)) = 0 := by
      first
        | exact Module.length_eq_zero_iff.2 hs
        | exact Module.length_eq_zero
    rw [h0]
    first
      | exact zero_le _
      | exact zero_le
      | simp
  | succ c ih =>
    have hpow : a * a ^ c = a ^ (c + 1) := by ring
    let f : ↥(Submodule.torsionBy O M (a ^ (c + 1))) →ₗ[O] ↥(Submodule.torsionBy O M a) :=
      LinearMap.codRestrict (Submodule.torsionBy O M a)
        (a ^ c • (Submodule.torsionBy O M (a ^ (c + 1))).subtype) (fun x => by
          have hx := x.2
          rw [Submodule.mem_torsionBy_iff] at hx
          rw [Submodule.mem_torsionBy_iff]
          show a • a ^ c • (x : M) = 0
          rw [smul_smul, hpow]
          exact hx)
    let g : ↥(LinearMap.ker f) →ₗ[O] ↥(Submodule.torsionBy O M (a ^ c)) :=
      LinearMap.codRestrict (Submodule.torsionBy O M (a ^ c))
        ((Submodule.torsionBy O M (a ^ (c + 1))).subtype ∘ₗ (LinearMap.ker f).subtype) (fun y => by
          have hy := congrArg Subtype.val (LinearMap.mem_ker.1 y.2)
          rw [Submodule.mem_torsionBy_iff]
          exact hy)
    have hg : Function.Injective g := by
      intro y z h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    calc Module.length O ↥(Submodule.torsionBy O M (a ^ (c + 1)))
        ≤ Module.length O ↥(LinearMap.ker f) + Module.length O ↥(Submodule.torsionBy O M a) :=
          length_le_length_ker_add_length f
      _ ≤ Module.length O ↥(Submodule.torsionBy O M (a ^ c)) +
            Module.length O ↥(Submodule.torsionBy O M a) :=
          add_le_add (Module.length_le_of_injective g hg) le_rfl
      _ ≤ (c : ℕ∞) * Module.length O ↥(Submodule.torsionBy O M a) +
            Module.length O ↥(Submodule.torsionBy O M a) :=
          add_le_add ih le_rfl
      _ = ((c + 1 : ℕ) : ℕ∞) * Module.length O ↥(Submodule.torsionBy O M a) := by
          push_cast
          ring

end Len

section Quot

variable {O LL V : Type} [CommRing O] [Field LL] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V]
  [IsScalarTower O LL V]

theorem length_torsion_quot (T : Submodule O V) {n : ℕ} (b : Fin n → V)
    (hT : T = Submodule.span O (Set.range b)) (a : O) (ha : algebraMap O LL a ≠ 0) :
    Module.length O ↥(Submodule.torsionBy O (V ⧸ T) a) ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  classical
  have hinv : ∀ v : V, a • ((algebraMap O LL a)⁻¹ • v) = v := fun v => by
    rw [← algebraMap_smul LL a, smul_smul, mul_inv_cancel₀ ha, one_smul]
  have hmem : ∀ i, (Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ • b i) : V ⧸ T) ∈
      Submodule.torsionBy O (V ⧸ T) a := by
    intro i
    rw [Submodule.mem_torsionBy_iff, ← Submodule.Quotient.mk_smul, hinv,
      Submodule.Quotient.mk_eq_zero, hT]
    exact Submodule.subset_span ⟨i, rfl⟩
  let m : Fin n → ↥(Submodule.torsionBy O (V ⧸ T) a) := fun i => ⟨_, hmem i⟩
  refine length_le_of_span m a ?_ ?_
  · rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective T y
    have hy' := hy
    rw [Submodule.mem_torsionBy_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hT,
      Submodule.mem_span_range_iff_exists_fun] at hy'
    obtain ⟨c, hc⟩ := hy'
    have hx : x = ∑ i, c i • ((algebraMap O LL a)⁻¹ • b i) := by
      calc x = (algebraMap O LL a)⁻¹ • (a • x) := by
            rw [← algebraMap_smul LL a x, smul_smul, inv_mul_cancel₀ ha, one_smul]
        _ = ∑ i, c i • ((algebraMap O LL a)⁻¹ • b i) := by
            rw [← hc, Finset.smul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            first
              | exact smul_comm _ _ _
              | rw [← algebraMap_smul LL (c i) ((algebraMap O LL a)⁻¹ • b i), smul_smul, mul_comm,
                  ← smul_smul, algebraMap_smul]
    have he : (⟨Submodule.Quotient.mk x, hy⟩ : ↥(Submodule.torsionBy O (V ⧸ T) a)) =
        ∑ i, c i • m i := by
      apply Subtype.ext
      first
        | (rw [Submodule.coe_sum]; simp only [Submodule.coe_smul, m])
        | simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, m]
      rw [hx]
      first
        | (change T.mkQ _ = ∑ i, c i • T.mkQ ((algebraMap O LL a)⁻¹ • b i)
           rw [map_sum]
           simp only [map_smul])
        | simp [Submodule.Quotient.mk_sum]
    rw [he]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro i
    apply Subtype.ext
    have h := hmem i
    rw [Submodule.mem_torsionBy_iff] at h
    exact h

theorem length_le_of_killed (T : Submodule O V) {n : ℕ} (b : Fin n → V)
    (hT : T = Submodule.span O (Set.range b)) (a : O) (ha : algebraMap O LL a ≠ 0) (c : ℕ)
    (W : Submodule O (V ⧸ T)) (hW : ∀ x ∈ W, a ^ c • x = 0) :
    Module.length O ↥W ≤ (n : ℕ∞) * (c : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  have hle : W ≤ Submodule.torsionBy O (V ⧸ T) (a ^ c) := fun x hx => by
    rw [Submodule.mem_torsionBy_iff]
    exact hW x hx
  have h3 := length_torsion_quot T b hT a ha
  calc Module.length O ↥W ≤ Module.length O ↥(Submodule.torsionBy O (V ⧸ T) (a ^ c)) :=
        Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    _ ≤ (c : ℕ∞) * Module.length O ↥(Submodule.torsionBy O (V ⧸ T) a) := length_torsionBy_pow_le a c
    _ ≤ (c : ℕ∞) * ((n : ℕ∞) * Module.length O (O ⧸ Ideal.span {a})) := by
        first
          | exact mul_le_mul' le_rfl h3
          | gcongr
    _ = (n : ℕ∞) * (c : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by ring

end Quot

end Formalism.MainNotions.N
