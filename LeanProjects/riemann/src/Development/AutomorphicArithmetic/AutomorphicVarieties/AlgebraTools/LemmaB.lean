import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ComapPowLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LenFgQuot

open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.lemma_B_range {A H Q : Type} [CommRing A] [AddCommGroup H] [Module A H]
    [AddCommGroup Q] [Module A Q] (N : Submodule A H) (φ : H →ₗ[A] Q) (h : N ≤ LinearMap.ker φ) :
    Module.length A (LinearMap.range φ) ≤ Module.length A (H ⧸ N) := by
  refine Module.length_le_of_surjective (N.liftQ φ.rangeRestrict (by rwa [LinearMap.ker_rangeRestrict])) ?_
  intro y
  obtain ⟨x, rfl⟩ := φ.surjective_rangeRestrict y
  exact ⟨N.mkQ x, rfl⟩

private theorem UpperTheory.V.AlgebraTools.lemma_B_sup {A Q : Type} [CommRing A] [AddCommGroup Q] [Module A Q]
    (P U V : Submodule A Q) (h : P ≤ U ⊔ V) :
    Module.length A P ≤ Module.length A U + Module.length A V := by
  have hsurj : Function.Surjective ((Submodule.inclusion (le_sup_left : U ≤ U ⊔ V)).coprod
      (Submodule.inclusion (le_sup_right : V ≤ U ⊔ V))) := by
    rintro ⟨y, hy⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
    exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
  calc Module.length A P ≤ Module.length A (U ⊔ V : Submodule A Q) :=
        Module.length_le_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
    _ ≤ Module.length A (U × V) := Module.length_le_of_surjective _ hsurj
    _ = Module.length A U + Module.length A V := Module.length_prod _ _ _

private theorem UpperTheory.V.AlgebraTools.lemma_B_le {A M M' S : Type} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup M'] [Module A M']
    [Module.Finite A M'] (I : Ideal A) (f : S → M →ₗ[A] M') :
    ∃ c : ℕ, ∀ m : ℕ, (⨅ s, (I ^ (m + c) • (⊤ : Submodule A M')).comap (f s)) ≤
      (⨅ s, LinearMap.ker (f s)) ⊔ I ^ m • (⊤ : Submodule A M) := by
  classical
  obtain ⟨_, ⟨T, rfl⟩, hT⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian A (M →ₗ[A] M'))
    (Set.range fun T : Finset S => Submodule.span A (f '' (T : Set S))) ⟨_, ⟨∅, rfl⟩⟩
  have hspan : ∀ s, f s ∈ Submodule.span A (f '' (T : Set S)) := by
    intro s
    by_contra hs
    refine hT _ ⟨insert s T, rfl⟩ (lt_of_le_of_ne (Submodule.span_mono ?_) ?_)
    · apply Set.image_mono
      rw [Finset.coe_insert]
      exact Set.subset_insert _ _
    · intro heq
      apply hs
      simp only at heq
      rw [heq]
      exact Submodule.subset_span ⟨s, by simp, rfl⟩
  have hker : ⨅ t : T, LinearMap.ker (f t) ≤ ⨅ s, LinearMap.ker (f s) := by
    intro x hx
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
    intro s
    have hle : Submodule.span A (f '' (T : Set S)) ≤
        LinearMap.ker (LinearMap.applyₗ (R := A) (M₂ := M') x) := by
      rw [Submodule.span_le]
      rintro _ ⟨t, ht, rfl⟩
      simpa using hx ⟨t, ht⟩
    simpa using hle (hspan s)
  let F : M →ₗ[A] (T → M') := LinearMap.pi fun t => f t
  obtain ⟨c, hc⟩ := UpperTheory.V.AlgebraTools.comap_pow_le I F
  refine ⟨c, fun m x hx => ?_⟩
  have hFx : F x ∈ I ^ (m + c) • (⊤ : Submodule A (T → M')) := by
    rw [← Finset.univ_sum_single (F x)]
    refine Submodule.sum_mem _ fun t _ => ?_
    have h1 : f t x ∈ I ^ (m + c) • (⊤ : Submodule A M') := by
      simpa using (Submodule.mem_iInf _).mp hx t
    simpa [F] using Submodule.smul_top_le_comap_smul_top (I ^ (m + c))
      (LinearMap.single A (fun _ : T => M') t) h1
  have hm := hc m hFx
  have hle : LinearMap.ker F ≤ ⨅ s, LinearMap.ker (f s) := by
    simp only [F, LinearMap.ker_pi]
    exact hker
  exact (sup_le_sup_right hle _) hm

theorem UpperTheory.V.AlgebraTools.lemma_B :
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {M M' S : Type} [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup M'] [Module A M'] [Module.Finite A M'] (f : S → M →ₗ[A] M'), ∃ e : ℕ, ∀ j : ℕ, Module.length A ((⨅ s, (maximalIdeal A ^ j • (⊤ : Submodule A M')).comap (f s)).map (maximalIdeal A ^ j • (⊤ : Submodule A M)).mkQ) ≤ ((Module.finrank A (⨅ s, LinearMap.ker (f s) : Submodule A M) * j + e : ℕ) : ℕ∞) := by
  intro A _ _ _ M M' S _ _ _ _ _ _ f
  set K : Submodule A M := ⨅ s, LinearMap.ker (f s) with hKdef
  obtain ⟨c, hc⟩ := UpperTheory.V.AlgebraTools.lemma_B_le (maximalIdeal A) f
  obtain ⟨cK, -, hK⟩ := UpperTheory.V.AlgebraTools.len_fg_quot (A := A) K
  obtain ⟨cM, -, hM⟩ := UpperTheory.V.AlgebraTools.len_fg_quot (A := A) M
  refine ⟨cK + Module.finrank A M * c + cM, fun j => ?_⟩
  set P := ⨅ s, (maximalIdeal A ^ j • (⊤ : Submodule A M')).comap (f s) with hPdef
  set N := maximalIdeal A ^ j • (⊤ : Submodule A M) with hNdef
  have hQ : Module.length A (P.map N.mkQ) ≤ Module.length A (M ⧸ N) :=
    Module.length_le_of_injective (Submodule.subtype _) (Submodule.injective_subtype _)
  by_cases hj : j < c
  · refine le_trans hQ (le_trans (hM j).2 ?_)
    have h1 := Nat.mul_le_mul_left (Module.finrank A M) hj.le
    have h2 := Nat.zero_le (Module.finrank A K * j)
    exact_mod_cast (show Module.finrank A M * j + cM ≤
      Module.finrank A K * j + (cK + Module.finrank A M * c + cM) by omega)
  · push_neg at hj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + c := ⟨j - c, by omega⟩
    have hP : P ≤ K ⊔ maximalIdeal A ^ m • ⊤ := hc m
    have hU : Module.length A (K.map N.mkQ) ≤ ((Module.finrank A K * (m + c) + cK : ℕ) : ℕ∞) := by
      refine le_trans ?_ (hK (m + c)).2
      have := UpperTheory.V.AlgebraTools.lemma_B_range (maximalIdeal A ^ (m + c) • (⊤ : Submodule A K))
        (N.mkQ ∘ₗ K.subtype) ?_
      · rwa [LinearMap.range_comp, Submodule.range_subtype] at this
      · intro x hx
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_top_le_comap_smul_top _ K.subtype hx
    let g : (M ⧸ N) →ₗ[A] (M ⧸ (maximalIdeal A ^ m • (⊤ : Submodule A M))) :=
      N.liftQ (Submodule.mkQ _) (by
        rw [Submodule.ker_mkQ]
        exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right m c)))
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
      exact ⟨N.mkQ x, rfl⟩
    have hV : (maximalIdeal A ^ m • (⊤ : Submodule A M)).map N.mkQ = LinearMap.ker g := by
      rw [Submodule.ker_liftQ, Submodule.ker_mkQ]
    have hlen := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
      (Submodule.injective_subtype _) hg (LinearMap.exact_subtype_ker_map g)
    have hVb : Module.length A (LinearMap.ker g) ≤ ((Module.finrank A M * c + cM : ℕ) : ℕ∞) := by
      have h1 := (hM (m + c)).2
      have h2 := (hM m).1
      rw [hlen] at h1
      have h3 : Module.length A (LinearMap.ker g) + ((Module.finrank A M * m : ℕ) : ℕ∞) ≤
          ((Module.finrank A M * (m + c) + cM : ℕ) : ℕ∞) :=
        le_trans (add_le_add le_rfl h2) h1
      have hfin : Module.length A (LinearMap.ker g) ≠ ⊤ := by
        intro htop
        rw [htop, top_add, top_le_iff] at h3
        exact ENat.coe_ne_top _ h3
      obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hfin
      rw [← ha] at h3 ⊢
      norm_cast at h3 ⊢
      rw [Nat.mul_add] at h3
      omega
    calc Module.length A (P.map N.mkQ)
        ≤ Module.length A (K.map N.mkQ) +
          Module.length A ((maximalIdeal A ^ m • (⊤ : Submodule A M)).map N.mkQ) := by
          apply UpperTheory.V.AlgebraTools.lemma_B_sup
          rw [← Submodule.map_sup]
          exact Submodule.map_mono hP
      _ ≤ ((Module.finrank A K * (m + c) + cK : ℕ) : ℕ∞) + ((Module.finrank A M * c + cM : ℕ) : ℕ∞) := by
          rw [hV]
          exact add_le_add hU hVb
      _ = _ := by
          push_cast
          ring
