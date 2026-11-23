import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.length_quotient_fg_bounds {A : Type} [CommRing A] (H : Type) [AddCommGroup H] [Module A H]
    (r : ℕ) (π : H →ₗ[A] (Fin r → A)) (hπ : Function.Surjective π) (I : Ideal A) :
    Module.length A (Fin r → A ⧸ I) ≤ Module.length A (H ⧸ I • (⊤ : Submodule A H)) ∧
    Module.length A (H ⧸ I • (⊤ : Submodule A H)) ≤
      Module.length A (Fin r → A ⧸ I) + Module.length A (LinearMap.ker π) := by
  classical
  let N := I • (⊤ : Submodule A H)
  let φ : H →ₗ[A] (Fin r → A ⧸ I) := LinearMap.pi fun i => I.mkQ ∘ₗ (LinearMap.proj i ∘ₗ π)
  have hφ : ∀ h i, φ h i = Submodule.Quotient.mk (π h i) := fun h i => rfl
  have hNφ : N ≤ LinearMap.ker φ := by
    rw [Submodule.smul_le]
    intro a ha h _
    rw [LinearMap.mem_ker]
    funext i
    rw [hφ, map_smul, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact I.mul_mem_right _ ha
  let φ' := N.liftQ φ hNφ
  have hφ' : ∀ h, φ' (N.mkQ h) = φ h := fun h => rfl
  have hsurj : Function.Surjective φ' := by
    intro y
    choose z hz using fun i => Submodule.Quotient.mk_surjective I (y i)
    obtain ⟨h, rfl⟩ := hπ z
    refine ⟨N.mkQ h, ?_⟩
    funext i
    rw [hφ', hφ, hz]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hs' : ∀ v, π (s v) = v := fun v => LinearMap.congr_fun hs v
  let ρ : LinearMap.ker π →ₗ[A] LinearMap.ker φ' :=
    (N.mkQ ∘ₗ (LinearMap.ker π).subtype).codRestrict (LinearMap.ker φ') (by
      intro k
      rw [LinearMap.mem_ker, LinearMap.comp_apply, hφ']
      funext i
      rw [hφ, Submodule.subtype_apply, LinearMap.mem_ker.1 k.2]
      simp)
  have hρ : Function.Surjective ρ := by
    rintro ⟨x, hx⟩
    obtain ⟨h, rfl⟩ := N.mkQ_surjective x
    rw [LinearMap.mem_ker, hφ'] at hx
    have hI : ∀ i, π h i ∈ I := fun i => by
      have := congrFun hx i
      rw [hφ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
      exact this
    have hsN : s (π h) ∈ N := by
      rw [pi_eq_sum_univ (π h), map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_smul]
      exact Submodule.smul_mem_smul (hI i) trivial
    have hk : h - s (π h) ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_sub, hs', sub_self]
    refine ⟨⟨_, hk⟩, ?_⟩
    apply Subtype.ext
    change N.mkQ (h - s (π h)) = N.mkQ h
    have h0 : N.mkQ (s (π h)) = 0 := (Submodule.Quotient.mk_eq_zero N).2 hsN
    rw [map_sub, h0, sub_zero]
  have hex := Module.length_eq_add_of_exact (LinearMap.ker φ').subtype φ'
    (Submodule.subtype_injective _) hsurj (LinearMap.exact_subtype_ker_map φ')
  refine ⟨Module.length_le_of_surjective φ' hsurj, ?_⟩
  rw [hex, add_comm]
  exact add_le_add le_rfl (Module.length_le_of_surjective ρ hρ)

private theorem UpperTheory.V.AlgebraTools.len_fg_quot_tors {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] (hT : Module.IsTorsion A T) :
    Module.length A T ≠ ⊤ := by
  classical
  obtain ⟨x, hxann, hx⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hT
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
  have hspan : Ideal.span {x} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hspan hϖ
  have hJ : Ideal.span {x} = maximalIdeal A ^ n := by
    rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' A T
  let I : Ideal A := maximalIdeal A ^ n
  have hIf : I • (⊤ : Submodule A (Fin k → A)) ≤ LinearMap.ker f := by
    rw [Submodule.smul_le]
    intro a ha v _
    rw [LinearMap.mem_ker, map_smul]
    have ha' : a ∈ Ideal.span {x} := by rw [hJ]; exact ha
    rw [Ideal.mem_span_singleton'] at ha'
    obtain ⟨c, rfl⟩ := ha'
    rw [mul_smul, (Submodule.mem_annihilator.1 hxann) _ trivial, smul_zero]
  have hsurj : Function.Surjective ((I • (⊤ : Submodule A (Fin k → A))).liftQ f hIf) := by
    intro t
    obtain ⟨v, rfl⟩ := hf t
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  have h1 := (UpperTheory.V.AlgebraTools.length_quotient_fg_bounds (Fin k → A) k LinearMap.id
    Function.surjective_id I).2
  have hker : Module.length A (LinearMap.ker (LinearMap.id : (Fin k → A) →ₗ[A] (Fin k → A))) = 0 := by
    rw [Module.length_eq_zero_iff]
    constructor
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    rw [LinearMap.mem_ker, LinearMap.id_apply] at ha hb
    subst ha hb
    rfl
  have h2 : Module.length A (Fin k → A ⧸ I) = (k * n : ℕ) := by
    rw [Module.length_pi, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    simp
  have h3 := Module.length_le_of_surjective _ hsurj
  rw [hker, add_zero, h2] at h1
  exact ne_top_of_le_ne_top (ENat.coe_ne_top _) (h3.trans h1)

theorem UpperTheory.V.AlgebraTools.len_fg_quot :
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (H : Type) [AddCommGroup H] [Module A H] [Module.Finite A H], ∃ c : ℕ, Module.length A (Submodule.torsion A H) = c ∧ ∀ j : ℕ, ((Module.finrank A H * j : ℕ) : ℕ∞) ≤ Module.length A (H ⧸ maximalIdeal A ^ j • (⊤ : Submodule A H)) ∧ Module.length A (H ⧸ maximalIdeal A ^ j • (⊤ : Submodule A H)) ≤ ((Module.finrank A H * j + c : ℕ) : ℕ∞) := by
  intro A _ _ _ H _ _ _
  classical
  let Tor := Submodule.torsion A H
  haveI : Module.Free A (H ⧸ Tor) := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis A (H ⧸ Tor)
  have hm : Module.finrank A (H ⧸ Tor) = Module.finrank A H :=
    finrank_quotient_eq_of_le_torsion le_rfl
  let π : H →ₗ[A] (Fin (Module.finrank A (H ⧸ Tor)) → A) := b.equivFun.toLinearMap ∘ₗ Tor.mkQ
  have hπ : Function.Surjective π := b.equivFun.surjective.comp (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker π = Tor := by
    simp only [π, LinearEquiv.ker_comp, Submodule.ker_mkQ]
  have hTf : Module.length A Tor ≠ ⊤ :=
    UpperTheory.V.AlgebraTools.len_fg_quot_tors Tor (Submodule.torsion_isTorsion)
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hTf
  refine ⟨c, hc.symm, fun j => ?_⟩
  have h := UpperTheory.V.AlgebraTools.length_quotient_fg_bounds H _ π hπ (maximalIdeal A ^ j)
  have hlen : Module.length A (Fin (Module.finrank A (H ⧸ Tor)) → A ⧸ maximalIdeal A ^ j) =
      ((Module.finrank A H * j : ℕ) : ℕ∞) := by
    rw [Module.length_pi, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, hm]
    simp
  rw [hlen, hker, ← hc] at h
  refine ⟨h.1, ?_⟩
  rw [Nat.cast_add]
  exact h.2
