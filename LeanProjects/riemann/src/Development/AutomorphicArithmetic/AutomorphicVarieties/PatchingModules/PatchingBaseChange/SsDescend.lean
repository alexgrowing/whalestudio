import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem eq_bot_of_forall_isNilpotent_of_isSemisimple {R : Type*} [Ring R] [IsSemisimpleRing R] (L : Submodule R R)
    (h : ∀ z ∈ L, IsNilpotent z) : L = ⊥ := by
  obtain ⟨C, hC⟩ := exists_isCompl L
  have h1 : (1 : R) ∈ L ⊔ C := by rw [hC.sup_eq_top]; trivial
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp h1
  have key : ∀ l ∈ L, l * f = 0 := by
    intro l hl
    have hl1 : l * e ∈ L := L.smul_mem l he
    have hl2 : l * f ∈ C := C.smul_mem l hf
    have hsub : l * f = l - l * e := by
      rw [eq_sub_iff_add_eq, add_comm, ← mul_add, hef, mul_one]
    have hL : l * f ∈ L := by rw [hsub]; exact L.sub_mem hl hl1
    exact (Submodule.disjoint_def.mp hC.disjoint) _ hL hl2
  have hee : IsIdempotentElem e := by
    show e * e = e
    calc e * e = e * (e + f) := by rw [mul_add, key e he, add_zero]
      _ = e := by rw [hef, mul_one]
  have he0 : e = 0 := hee.eq_zero_of_isNilpotent (h e he)
  rw [eq_bot_iff]
  intro l hl
  have hl' : l = l * e + l * f := by rw [← mul_add, hef, mul_one]
  rw [Submodule.mem_bot, hl', key l hl, he0, mul_zero, add_zero]

theorem UpperTheory.V.Pa.BC.ss_descend :
    ∀ (κ κ' E : Type) [Field κ] [Field κ'] [Algebra κ κ'] [Ring E] [Algebra κ E] [Module.Finite κ E], IsSemisimpleRing (κ' ⊗[κ] E) → IsSemisimpleRing E := by
  intro κ κ' E _ _ _ _ _ _ hT
  haveI : IsArtinianRing E := IsArtinianRing.of_finite κ E
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  obtain ⟨n, hn⟩ := IsSemiprimaryRing.isNilpotent (R := E)
  set J := Ring.jacobson E with hJ
  let S : ℕ → Submodule κ (κ' ⊗[κ] E) := fun k =>
    Submodule.span κ {z | ∃ c : κ', ∃ a ∈ J ^ k, z = c ⊗ₜ[κ] a}
  have hgen : ∀ k (c : κ') (a : E), a ∈ J ^ k → c ⊗ₜ[κ] a ∈ S k :=
    fun k c a ha => Submodule.subset_span ⟨c, a, ha, rfl⟩
  have hmul : ∀ a (z w : κ' ⊗[κ] E), z ∈ S a → w ∈ S 1 → z * w ∈ S (a + 1) := by
    intro a z w hz hw
    induction hz using Submodule.span_induction with
    | mem z hz =>
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨c, u, hu, rfl⟩ := hz
        obtain ⟨c', v, hv, rfl⟩ := hw
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        refine hgen _ _ _ ?_
        rw [Submodule.pow_succ]
        rw [Submodule.pow_one] at hv
        exact Ideal.mul_mem_mul hu hv
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add w₁ w₂ _ _ h₁ h₂ => rw [mul_add]; exact Submodule.add_mem _ h₁ h₂
      | smul r w _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ r h
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add z₁ z₂ _ _ h₁ h₂ => rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
    | smul r z _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r h
  have hbot : S n = ⊥ := by
    rw [eq_bot_iff, Submodule.span_le]
    rintro z ⟨c, a, ha, rfl⟩
    rw [hn, Ideal.zero_eq_bot, Submodule.mem_bot] at ha
    show _ ∈ (⊥ : Submodule κ (κ' ⊗[κ] E))
    rw [Submodule.mem_bot, ha, TensorProduct.tmul_zero]
  have h1 : ∀ t : κ' ⊗[κ] E, t * ((1 : κ') ⊗ₜ[κ] x) ∈ S 1 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | tmul c a =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      refine hgen 1 c _ ?_
      rw [Submodule.pow_one]
      exact J.mul_mem_left a hx
    | add t₁ t₂ h₁ h₂ => rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
  have hpow : ∀ z ∈ S 1, ∀ k, z ^ k ∈ S k := by
    intro z hz k
    induction k with
    | zero =>
      rw [pow_zero, Algebra.TensorProduct.one_def]
      exact hgen 0 1 1 (Submodule.one_le.mp fun _ h => h)
    | succ k ih => rw [pow_succ]; exact hmul k _ _ ih hz
  have hL : Submodule.span (κ' ⊗[κ] E) {(1 : κ') ⊗ₜ[κ] x} = ⊥ := by
    apply eq_bot_of_forall_isNilpotent_of_isSemisimple
    intro z hz
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
    refine ⟨n, ?_⟩
    have hz' := hpow _ (h1 t) n
    rw [hbot, Submodule.mem_bot] at hz'
    rw [smul_eq_mul]
    exact hz'
  have hy : (1 : κ') ⊗ₜ[κ] x = 0 := by
    have hm : (1 : κ') ⊗ₜ[κ] x ∈ Submodule.span (κ' ⊗[κ] E) {(1 : κ') ⊗ₜ[κ] x} :=
      Submodule.mem_span_singleton_self _
    rw [hL, Submodule.mem_bot] at hm
    exact hm
  apply Algebra.TensorProduct.includeRight_injective (R := κ) (A := κ') (B := E)
    (algebraMap κ κ').injective
  rw [Algebra.TensorProduct.includeRight_apply, map_zero, hy]
