import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing Matrix UpperTheory.V.Alg

namespace UpperTheory.V.Fr.PF

theorem span_mul {G C A : Type} [Monoid G] [CommRing C] [Ring A] [Algebra C A] (r : G →* A) {a b : A}
    (ha : a ∈ Submodule.span C (Set.range r)) (hb : b ∈ Submodule.span C (Set.range r)) :
    a * b ∈ Submodule.span C (Set.range r) := by
  have h := Submodule.mul_mem_mul ha hb
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨g, rfl⟩, _, ⟨h, rfl⟩, rfl⟩
  exact ⟨g * h, map_mul r g h⟩

section Gen

variable {G C K : Type} [Monoid G] [CommRing C] [CommRing K] [Algebra C K] {n : ℕ}
  (r : G →* Matrix (Fin n) (Fin n) K)

theorem entry_mem {a : Matrix (Fin n) (Fin n) K} (ha : a ∈ Submodule.span C (Set.range r)) (i j : Fin n) :
    a i j ∈ Submodule.span C (Set.range fun g => r g i j) := by
  induction ha using Submodule.span_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact Submodule.subset_span ⟨g, rfl⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

variable {r}

theorem single_mem (hE : ∀ i, Matrix.single i i (1 : K) ∈ Submodule.span C (Set.range r)) {i j : Fin n} {x : K}
    (hx : x ∈ Submodule.span C (Set.range fun g => r g i j)) :
    Matrix.single i j x ∈ Submodule.span C (Set.range r) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    have h := span_mul r (span_mul r (hE i) (Submodule.subset_span ⟨g, rfl⟩)) (hE j)
    rwa [Matrix.single_mul_mul_single, one_mul, mul_one] at h
  | zero => rw [Matrix.single_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.single_add]; exact add_mem hx hy
  | smul c x _ hx => rw [← Matrix.smul_single]; exact Submodule.smul_mem _ c hx

theorem ent_mul (hE : ∀ i, Matrix.single i i (1 : K) ∈ Submodule.span C (Set.range r)) {i j k : Fin n} {x y : K}
    (hx : x ∈ Submodule.span C (Set.range fun g => r g i j))
    (hy : y ∈ Submodule.span C (Set.range fun g => r g j k)) :
    x * y ∈ Submodule.span C (Set.range fun g => r g i k) := by
  have h := entry_mem r (span_mul r (single_mem hE hx) (single_mem hE hy)) i k
  rwa [Matrix.single_mul_single_same, Matrix.single_apply_same] at h

theorem trace_cont [TopologicalSpace G] [ContinuousMul G] (I : Ideal C) (t : G → C) (hc : AdicCont I t)
    (ht : ∀ g, algebraMap C K (t g) = (r g).trace) {m : Matrix (Fin n) (Fin n) K}
    (hm : m ∈ Submodule.span C (Set.range r)) :
    ∃ c : G → C, AdicCont I c ∧ ∀ g, algebraMap C K (c g) = (m * r g).trace := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    exact ⟨fun g => t (h * g), fun N => (hc N).comp_continuous (continuous_const_mul h), fun g => by
      rw [ht, map_mul]⟩
  | zero => exact ⟨fun _ => 0, fun N => IsLocallyConstant.const _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, h1, h2⟩ := hx
    obtain ⟨d, h3, h4⟩ := hy
    refine ⟨fun g => c g + d g, fun N => ?_, fun g => by rw [map_add, h2, h4, add_mul, trace_add]⟩
    simp only [map_add]
    exact (h1 N).add (h3 N)
  | smul a x _ hx =>
    obtain ⟨c, h1, h2⟩ := hx
    refine ⟨fun g => a * c g, fun N => ?_, fun g => by
      rw [map_mul, h2, Matrix.smul_mul, trace_smul, Algebra.smul_def]⟩
    simp only [map_mul]
    exact (IsLocallyConstant.const _).mul (h1 N)

theorem residues {k : Type} [Field k] [Algebra C k] (hinj : Function.Injective (algebraMap C K))
    (hE : ∀ i, Matrix.single i i (1 : K) ∈ Submodule.span C (Set.range r)) (χ : Fin n → G →* k)
    (ht : ∀ g, ∃ c, algebraMap C K c = (r g).trace ∧ algebraMap C k c = ∑ j, χ j g) (g₀ g₁ : G) (δ : Fin n → C)
    (hD : r g₀ - r g₁ = diagonal fun i => algebraMap C K (δ i))
    (hd : ∀ j, χ j g₀ - χ j g₁ = algebraMap C k (δ j)) (hδ : Function.Injective fun j => algebraMap C k (δ j)) :
    (∀ g i, ∃ c, algebraMap C K c = r g i i ∧ algebraMap C k c = χ i g) ∧
    ∀ i j, i ≠ j → ∀ x ∈ Submodule.span C (Set.range fun g => r g i j),
      ∀ y ∈ Submodule.span C (Set.range fun g => r g j i), ∃ c, algebraMap C K c = x * y ∧ algebraMap C k c = 0 := by
  let R : G →* Matrix (Fin n) (Fin n) K × (Fin n → k) := r.prod (MonoidHom.pi χ)
  let S := Submodule.span C (Set.range R)
  have hR : ∀ g, (r g, fun j => χ j g) ∈ S := fun g => Submodule.subset_span ⟨g, rfl⟩
  have htr : ∀ p ∈ S, ∃ c, algebraMap C K c = p.1.trace ∧ algebraMap C k c = ∑ j, p.2 j := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem x hx => obtain ⟨g, rfl⟩ := hx; exact ht g
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, h1, h2⟩ := hx
      obtain ⟨d, h3, h4⟩ := hy
      exact ⟨c + d, by simp [h1, h3], by simp [h2, h4, Finset.sum_add_distrib]⟩
    | smul a x _ hx =>
      obtain ⟨c, h1, h2⟩ := hx
      exact ⟨a * c, by rw [map_mul, h1, Prod.smul_fst, trace_smul, Algebra.smul_def], by
        rw [map_mul, h2, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Prod.smul_snd, Pi.smul_apply, Algebra.smul_def]⟩
  have hex : ∀ m ∈ Submodule.span C (Set.range r), ∃ a, (m, a) ∈ S := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx => obtain ⟨g, rfl⟩ := hx; exact ⟨_, hR g⟩
    | zero => exact ⟨0, zero_mem S⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, add_mem ha hb⟩
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      exact ⟨c • a, S.smul_mem c ha⟩
  have hχ : Function.Injective χ := fun i j h => hδ (by simp only [← hd, h])
  have huniq : ∀ a, ((0 : Matrix (Fin n) (Fin n) K), a) ∈ S → a = 0 := by
    intro a ha
    have hli := (linearIndependent_monoidHom G k).comp χ hχ
    funext j
    refine Fintype.linearIndependent_iff.1 hli a ?_ j
    funext g
    obtain ⟨c, h1, h2⟩ := htr _ (span_mul R ha (hR g))
    have hc : c = 0 := hinj (by simpa using h1)
    simpa [hc] using h2.symm
  have hES : ∀ i, (Matrix.single i i (1 : K), (Pi.single i 1 : Fin n → k)) ∈ S := by
    intro i
    obtain ⟨a, ha⟩ := hex _ (hE i)
    have h1 := sub_mem (span_mul R (sub_mem (hR g₀) (hR g₁)) ha) (S.smul_mem (δ i) ha)
    have h2 : (r g₀ - r g₁) * Matrix.single i i (1 : K) - δ i • Matrix.single i i (1 : K) = 0 := by
      rw [hD]
      ext a b
      rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.smul_apply, Algebra.smul_def, Matrix.single_apply,
        Matrix.zero_apply]
      split_ifs with h
      · rw [h.1, sub_self]
      · simp
    simp only [Prod.mk_sub_mk, Prod.mk_mul_mk, Prod.smul_mk, h2] at h1
    have h3 := huniq _ h1
    have h4 : ∀ j, j ≠ i → a j = 0 := fun j hj => by
      have h5 := congrFun h3 j
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, hd, Algebra.smul_def, Pi.zero_apply, ← sub_mul] at h5
      exact (mul_eq_zero.1 h5).resolve_left fun h => hj (hδ (sub_eq_zero.1 h))
    obtain ⟨c, h5, h6⟩ := htr _ ha
    have hc : c = 1 := hinj (by simpa using h5)
    rw [hc, map_one, Finset.sum_eq_single i (fun j _ hj => h4 j hj) (by simp)] at h6
    have h7 : a = Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · rw [hj, Pi.single_eq_same]; exact h6.symm
      · rw [h4 j hj, Pi.single_eq_of_ne hj]
    rwa [h7] at ha
  refine ⟨fun g i => ?_, fun i j hij x hx y hy => ?_⟩
  · obtain ⟨c, h1, h2⟩ := htr _ (span_mul R (hES i) (hR g))
    refine ⟨c, ?_, ?_⟩
    · simpa [Matrix.trace_single_mul] using h1
    · simpa [Pi.single_apply] using h2
  · obtain ⟨a, ha⟩ := hex _ (single_mem hE hx)
    obtain ⟨b, hb⟩ := hex _ (single_mem hE hy)
    obtain ⟨c, h1, h2⟩ := htr _ (span_mul R (span_mul R (span_mul R (hES i) ha) (hES j)) hb)
    refine ⟨c, ?_, ?_⟩
    · simpa [Matrix.single_mul_single_same] using h1
    · simpa [Pi.single_apply, hij, hij.symm] using h2

end Gen

theorem artin_rees {G C K : Type} [TopologicalSpace G] [CommRing C] [IsNoetherianRing C] [Field K] [Algebra C K]
    (I : Ideal C) (N : Submodule C K) {y : K} (hy : y ≠ 0)
    (hN : ∀ x ∈ N, ∃ c, algebraMap C K c = y * x) (f : G → K) (hf : ∀ g, f g ∈ N) (c : G → C) (hc : AdicCont I c)
    (hcf : ∀ g, algebraMap C K (c g) = y * f g) :
    N.FG ∧ ∀ m : ℕ, IsLocallyConstant fun g => (I ^ m • N).mkQ (f g) := by
  let θ : C →ₗ[C] K := (LinearMap.mulLeft C y⁻¹).comp (Algebra.linearMap C K)
  have hθ : ∀ a x, algebraMap C K a = y * x → θ a = x := fun a x h => by
    show y⁻¹ * algebraMap C K a = x
    rw [h, inv_mul_cancel_left₀ hy]
  let J : Submodule C C := N.comap θ
  have hJ : J.map θ = N := Submodule.map_comap_eq_self fun x hx => by
    obtain ⟨a, ha⟩ := hN x hx
    exact ⟨a, hθ a x ha⟩
  refine ⟨hJ ▸ (IsNoetherian.noetherian J).map θ, fun m => ?_⟩
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I J
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (hc (m + k)) g] with h hh
  have h1 : c h - c g ∈ I ^ (m + k) := Ideal.Quotient.eq.1 hh
  have h2 : θ (c h - c g) = f h - f g := by rw [map_sub, hθ _ _ (hcf h), hθ _ _ (hcf g)]
  have h3 : c h - c g ∈ (I ^ (m + k) • ⊤ : Submodule C C) ⊓ J :=
    ⟨by simpa using h1, show θ _ ∈ N from h2 ▸ sub_mem (hf h) (hf g)⟩
  rw [hk _ (Nat.le_add_left k m), Nat.add_sub_cancel] at h3
  have h4 := Submodule.mem_map_of_mem (f := θ) (Submodule.smul_mono (le_refl (I ^ m)) inf_le_right h3)
  rw [Submodule.map_smul'', hJ, h2] at h4
  exact (Submodule.Quotient.eq _).2 h4

theorem cycles {C K : Type} [CommRing C] [CommRing K] [Algebra C K] (I : Ideal C) (N : ℤ → Set K)
    (h0 : ∀ x ∈ N 0, ∃ c, algebraMap C K c = x)
    (hm : ∀ a b, 0 < a → b < 0 → ∀ x ∈ N a, ∀ y ∈ N b,
      x * y ∈ N (a + b) ∧ (a + b = 0 → ∃ c ∈ I, algebraMap C K c = x * y))
    (L : Multiset (ℤ × K)) (hL : ∀ p ∈ L, p.2 ∈ N p.1) (hs : (L.map Prod.fst).sum = 0) :
    ∃ c, algebraMap C K c = (L.map Prod.snd).prod ∧ ((∃ p ∈ L, p.1 ≠ 0) → c ∈ I) := by
  classical
  induction hn : L.card using Nat.strong_induction_on generalizing L with
  | _ m ih =>
  by_cases hz : ∃ p ∈ L, p.1 ≠ 0
  · obtain ⟨u, hu, hu0⟩ := hz
    have hp : ∃ p ∈ L, 0 < p.1 := by
      by_contra h
      push Not at h
      have := Multiset.sum_lt_sum (s := L) (f := Prod.fst) (g := fun _ => (0 : ℤ)) h ⟨u, hu, (h u hu).lt_of_ne hu0⟩
      simp [hs] at this
    have hq : ∃ p ∈ L, p.1 < 0 := by
      by_contra h
      push Not at h
      have := Multiset.sum_lt_sum (s := L) (g := Prod.fst) (f := fun _ => (0 : ℤ)) h
        ⟨u, hu, (h u hu).lt_of_ne hu0.symm⟩
      simp [hs] at this
    obtain ⟨p, hpL, hp⟩ := hp
    obtain ⟨q, hqL, hq⟩ := hq
    obtain ⟨L₁, rfl⟩ := Multiset.exists_cons_of_mem hpL
    have hq1 : q ∈ L₁ := (Multiset.mem_cons.1 hqL).resolve_left fun h => by rw [h] at hq; omega
    obtain ⟨L₂, rfl⟩ := Multiset.exists_cons_of_mem hq1
    obtain ⟨h1, h2⟩ := hm _ _ hp hq _ (hL p hpL) _ (hL q hqL)
    have hL₂ : ∀ s ∈ L₂, s.2 ∈ N s.1 := fun s h => hL s (by simp [h])
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons, Multiset.card_cons] at hs hn ⊢
    by_cases h : p.1 + q.1 = 0
    · obtain ⟨c, hc, h3⟩ := h2 h
      obtain ⟨d, h4, -⟩ := ih _ (by omega) L₂ hL₂ (by omega) rfl
      exact ⟨c * d, by rw [map_mul, h3, h4, mul_assoc], fun _ => I.mul_mem_right _ hc⟩
    · obtain ⟨d, h4, h5⟩ := ih (L₂.card + 1) (by omega) ((p.1 + q.1, p.2 * q.2) ::ₘ L₂)
        (fun s hs => by
          rcases Multiset.mem_cons.1 hs with rfl | hs
          exacts [h1, hL₂ s hs]) (by simp only [Multiset.map_cons, Multiset.sum_cons]; omega) (by simp)
      exact ⟨d, by simp [h4, mul_assoc], fun _ => h5 ⟨_, Multiset.mem_cons_self _ _, h⟩⟩
  · have h : (L.map Prod.snd).prod ∈ (algebraMap C K).range := by
      refine Subring.multiset_prod_mem _ _ fun x hx => ?_
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
      have h1 : p.1 = 0 := by
        by_contra h1
        exact hz ⟨p, hp, h1⟩
      exact h0 _ (h1 ▸ hL p hp)
    obtain ⟨c, hc⟩ := h
    exact ⟨c, hc, fun h => absurd h hz⟩

end UpperTheory.V.Fr.PF
