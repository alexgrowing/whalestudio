import Development.EtaleCohomology.EtaleSheaves.SurjectiveCharts.EtaleSurjectiveChartOfFiniteChartSurj

noncomputable section

namespace LateralTheory.E.FiniteChartSurjPf

open LateralTheory.E.LSurjChartPf

theorem ker_le {A A' : Type} [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.FormallyUnramified A A']
    (I : Ideal A) (φ : A' →ₐ[A] A ⧸ I) :
    RingHom.ker φ ≤ RingHom.ker φ ^ 2 ⊔ I.map (algebraMap A A') := by
  set K := RingHom.ker φ with hKdef
  set N : Ideal A' := K ^ 2 ⊔ I.map (algebraMap A A') with hN
  let Q : Ideal (A' ⧸ N) := K.map (Ideal.Quotient.mk N)
  have hQ : Q ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left hx
  have hmemK : ∀ x : A', ∀ a : A, φ x = Ideal.Quotient.mk I a → x - algebraMap A A' a ∈ K := by
    intro x a h
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, h]
    simp [Ideal.Quotient.algebraMap_eq]
  let g : A ⧸ I →ₐ[A] A' ⧸ N := Ideal.Quotient.liftₐ I (Algebra.ofId A (A' ⧸ N)) (by
    intro a ha
    rw [Algebra.ofId_apply, IsScalarTower.algebraMap_apply A A' (A' ⧸ N), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha))
  have key : (Ideal.Quotient.mkₐ A Q).comp (Ideal.Quotient.mkₐ A N) =
      (Ideal.Quotient.mkₐ A Q).comp (g.comp φ) := by
    ext x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := I) (φ x)
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [← ha]
    have : g (Ideal.Quotient.mk I a) = Ideal.Quotient.mk N (algebraMap A A' a) := by
      rfl
    rw [this, Ideal.Quotient.eq, ← map_sub]
    exact Ideal.mem_map_of_mem _ (hmemK x a ha.symm)
  have := Algebra.FormallyUnramified.comp_injective Q hQ key
  intro k hk
  have h1 := congrArg (fun f => f k) this
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h1
  have hk' : φ k = 0 := hk
  rw [hk', map_zero] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp h1

theorem P_le {A A' : Type} [CommRing A] [CommRing A'] [Algebra A A'] (I : Ideal A) (φ : A' →ₐ[A] A ⧸ I)
    (S : Subalgebra A A') (r : S) (hr : IsUnit (φ r.1)) (hb : ∀ x : A', ∃ m : ℕ, r.1 ^ m * x ∈ S)
    (hK : RingHom.ker φ ≤ RingHom.ker φ ^ 2 ⊔ I.map (algebraMap A A')) :
    RingHom.ker (φ.comp S.val) ≤ RingHom.ker (φ.comp S.val) ^ 2 ⊔ I.map (algebraMap A S) := by
  set P := RingHom.ker (φ.comp S.val) with hPdef
  set L := P ^ 2 ⊔ I.map (algebraMap A S) with hLdef
  let W : Ideal A' :=
    { carrier := {y | ∃ m : ℕ, ∃ s ∈ L, (s : A') = r.1 ^ m * y}
      add_mem' := by
        rintro y1 y2 ⟨m1, s1, hs1, e1⟩ ⟨m2, s2, hs2, e2⟩
        refine ⟨m1 + m2, r ^ m2 * s1 + r ^ m1 * s2, L.add_mem (L.mul_mem_left _ hs1) (L.mul_mem_left _ hs2), ?_⟩
        push_cast; rw [e1, e2]; ring
      zero_mem' := ⟨0, 0, L.zero_mem, by simp⟩
      smul_mem' := by
        rintro c y ⟨m, s, hs, e⟩
        obtain ⟨m', hm'⟩ := hb c
        refine ⟨m + m', ⟨_, hm'⟩ * s, L.mul_mem_left _ hs, ?_⟩
        push_cast; rw [e, smul_eq_mul]; ring }
  have hmemP : ∀ (k : A') (m : ℕ) (h : r.1 ^ m * k ∈ S), k ∈ RingHom.ker φ → (⟨_, h⟩ : S) ∈ P := by
    intro k m h hk
    rw [RingHom.mem_ker] at hk ⊢
    show φ (r.1 ^ m * k) = 0
    rw [map_mul, hk, mul_zero]
  have hW : RingHom.ker φ ^ 2 ⊔ I.map (algebraMap A A') ≤ W := by
    refine sup_le ?_ ?_
    · rw [pow_two]
      refine Ideal.mul_le.mpr fun k hk k' hk' => ?_
      obtain ⟨m1, h1⟩ := hb k
      obtain ⟨m2, h2⟩ := hb k'
      refine ⟨m1 + m2, ⟨_, h1⟩ * ⟨_, h2⟩, Ideal.mem_sup_left ?_, ?_⟩
      · rw [pow_two]; exact Ideal.mul_mem_mul (hmemP k m1 h1 hk) (hmemP k' m2 h2 hk')
      · push_cast; ring
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact ⟨0, algebraMap A S a, Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha), by simp⟩
  intro x hx
  obtain ⟨m, s, hs, e⟩ := hW (hK hx)
  obtain ⟨b, hb'⟩ : ∃ b : A, Ideal.Quotient.mk I b * φ r.1 ^ m = 1 := by
    obtain ⟨v, hv⟩ := (hr.pow m).exists_left_inv
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
    exact ⟨b, hv⟩
  have hsx : s = r ^ m * x := Subtype.ext (by push_cast; exact e)
  have h1 : 1 - algebraMap A S b * r ^ m ∈ P := by
    rw [RingHom.mem_ker, map_sub, map_one, map_mul, map_pow, AlgHom.commutes, Ideal.Quotient.algebraMap_eq]
    change 1 - Ideal.Quotient.mk I b * φ r.1 ^ m = 0
    rw [hb', sub_self]
  have hx' : x = algebraMap A S b * s + (1 - algebraMap A S b * r ^ m) * x := by rw [hsx]; ring
  rw [hx']
  refine L.add_mem (L.mul_mem_left _ hs) (Ideal.mem_sup_left ?_)
  rw [pow_two]; exact Ideal.mul_mem_mul h1 hx

theorem ker_le_span_sub_sup_map {A A' : Type} [CommRing A] [CommRing A'] [Algebra A A'] (I : Ideal A) (φ : A' →ₐ[A] A ⧸ I)
    (S : Subalgebra A A') {n : ℕ} (t : Fin n → S) (ht : Submodule.span A (Set.range t) = ⊤) (a : Fin n → A)
    (ha : ∀ i, Ideal.Quotient.mk I (a i) = φ (t i).1) :
    RingHom.ker (φ.comp S.val) ≤ Ideal.span (Set.range fun i => t i - algebraMap A S (a i)) ⊔
      I.map (algebraMap A S) := by
  intro x hx
  have hxs : x ∈ Submodule.span A (Set.range t) := by rw [ht]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hxs
  have hsplit : x = ∑ i, algebraMap A S (c i) * (t i - algebraMap A S (a i)) +
      algebraMap A S (∑ i, c i * a i) := by
    rw [← hc, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul]; ring
  have hI : ∑ i, c i * a i ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
    have h0 : (φ.comp S.val) x = 0 := hx
    rw [← hc, map_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ha, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    rfl
  rw [hsplit]
  refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hI))
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem isUnit_of_mk {A : Type} [CommRing A] {I : Ideal A} (hI : I ≤ Ideal.jacobson ⊥) (a : A)
    (h : IsUnit (Ideal.Quotient.mk I a)) : IsUnit a := by
  obtain ⟨v, hv⟩ := h.exists_right_inv
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hm : a * b - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hv, map_one, sub_self]
  have := (Ideal.mem_jacobson_bot.mp (hI hm)) 1
  rw [mul_one, sub_add_cancel] at this
  exact isUnit_of_mul_isUnit_left this

theorem exists_idem {A A' : Type} [CommRing A] [CommRing A'] [Algebra A A'] (I : Ideal A)
    (hid : LateralTheory.E.LChartPf.IdemLiftInt A I) (φ : A' →ₐ[A] A ⧸ I) (S : Subalgebra A A') [Module.Finite A S]
    (hP : RingHom.ker (φ.comp S.val) ≤ RingHom.ker (φ.comp S.val) ^ 2 ⊔ I.map (algebraMap A S)) :
    ∃ e : S, IsIdempotentElem e ∧ φ e.1 = 1 ∧
      ∀ p ∈ RingHom.ker (φ.comp S.val), e * p ∈ I.map (algebraMap A S) := by
  obtain ⟨n, t, ht⟩ := Module.Finite.exists_fin (R := A) (M := S)
  choose a ha using fun i => Ideal.Quotient.mk_surjective (I := I) (φ (t i).1)
  have hPfg := ker_le_span_sub_sup_map I φ S t ht a ha
  have hISP : I.map (algebraMap A S) ≤ RingHom.ker (φ.comp S.val) := by
    rw [Ideal.map_le_iff_le_comap]; intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]; exact hx
  let IS := I.map (algebraMap A S)
  let J : Ideal (S ⧸ IS) := (RingHom.ker (φ.comp S.val)).map (Ideal.Quotient.mk IS)
  have hJeq : J = Ideal.span (Set.range fun i => Ideal.Quotient.mk IS (t i - algebraMap A S (a i))) := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      refine le_trans hPfg (sup_le ?_ ?_)
      · rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩
        exact Ideal.mem_comap.mpr (Ideal.subset_span ⟨i, rfl⟩)
      · intro x hx
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact Ideal.zero_mem _
    · rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩
      refine Ideal.mem_map_of_mem _ ?_
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, ha]; exact sub_self _
  have hJfg : J.FG := by rw [hJeq]; exact Submodule.fg_span (Set.finite_range _)
  have hJid : IsIdempotentElem J := by
    apply le_antisymm Ideal.mul_le_left
    calc J ≤ (RingHom.ker (φ.comp S.val) ^ 2 ⊔ IS).map (Ideal.Quotient.mk IS) := Ideal.map_mono hP
      _ = J * J := by rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_quotient_self, sup_bot_eq, pow_two]
  obtain ⟨ε, hε, hJε⟩ := (Ideal.isIdempotentElem_iff_of_fg J hJfg).mp hJid
  obtain ⟨e, he, hee⟩ := hid S (1 - ε) hε.one_sub
  have hee' : Ideal.Quotient.mk IS e = 1 - ε := hee
  refine ⟨e, he, ?_, ?_⟩
  · have hmem : Ideal.Quotient.mk IS (1 - e) ∈ J := by
      rw [map_sub, map_one, hee', sub_sub_cancel, hJε]; exact Ideal.mem_span_singleton_self ε
    obtain ⟨y, hy, hye⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hmem
    have h1 : 1 - e ∈ RingHom.ker (φ.comp S.val) := by
      have hd : (1 - e) - y ∈ IS := by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hye, sub_self]
      have := Ideal.add_mem _ (hISP hd) hy
      rwa [sub_add_cancel] at this
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h1
    exact h1.symm
  · intro p hp
    have h0 : Ideal.Quotient.mk IS p ∈ J := Ideal.mem_map_of_mem _ hp
    rw [hJε, Ideal.mem_span_singleton'] at h0
    obtain ⟨c, hc⟩ := h0
    show e * p ∈ IS
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hee', ← hc]
    have h2 : ε * ε = ε := hε
    linear_combination (-c) * h2

theorem nak {A A' : Type} [CommRing A] [CommRing A'] [Algebra A A'] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    (φ : A' →ₐ[A] A ⧸ I) (S : Subalgebra A A') [Module.Finite A S] (e : S) (he : IsIdempotentElem e)
    (heP : ∀ p ∈ RingHom.ker (φ.comp S.val), e * p ∈ I.map (algebraMap A S)) :
    ∀ s : S, ∃ a : A, s * e = algebraMap A S a * e := by
  let f : S →ₗ[A] S := LinearMap.mulRight A e
  have hMfg : (LinearMap.range f).FG := by
    rw [LinearMap.range_eq_map]; exact (Module.Finite.fg_top).map f
  have hle : LinearMap.range f ≤ Submodule.span A {e} ⊔ I • LinearMap.range f := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (I := I) (φ s.1)
    have hp : s - algebraMap A S b ∈ RingHom.ker (φ.comp S.val) := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, hb]; exact sub_self _
    have h1 : e * (s - algebraMap A S b) ∈ I • (⊤ : Submodule A S) := by
      rw [Ideal.smul_top_eq_map]; exact heP _ hp
    have h2 : f (e * (s - algebraMap A S b)) ∈ I • LinearMap.range f := by
      rw [LinearMap.range_eq_map, ← Submodule.map_smul'']; exact Submodule.mem_map_of_mem h1
    rw [Submodule.mem_sup]
    refine ⟨b • e, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e), _, h2, ?_⟩
    simp only [f, LinearMap.mulRight_apply, Algebra.smul_def]
    have h3 : e * e = e := he
    linear_combination (s - algebraMap A S b) * h3
  intro s
  have hs := Submodule.le_of_le_smul_of_le_jacobson_bot hMfg hI hle ⟨s, rfl⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hs
  exact ⟨a, by rw [← Algebra.smul_def, ha]; rfl⟩

theorem FiniteChartSurj_of : LateralTheory.E.LSurjChartPf.FiniteChartSurj := by
  intro A _ I hI hid A' _ _ _ φ S hfg r hr hb
  rw [bij_iff] at hb
  have : Module.Finite A S := Module.Finite.iff_fg.mpr hfg
  obtain ⟨e, he, he1, heP⟩ := exists_idem I hid φ S (P_le I φ S r hr hb (ker_le I φ))
  have hN := nak I hI φ S e he heP
  obtain ⟨a₀, ha₀⟩ := hN r
  have hφr : φ r.1 = Ideal.Quotient.mk I a₀ := by
    have h := congrArg (fun x : S => φ x.1) ha₀
    simp only [Subalgebra.coe_mul, map_mul, he1, mul_one, Subalgebra.coe_algebraMap, AlgHom.commutes,
      Ideal.Quotient.algebraMap_eq] at h
    exact h
  have hu₀ : IsUnit a₀ := isUnit_of_mk hI a₀ (hφr ▸ hr)
  refine ⟨e.1 * r.1, by rw [map_mul, he1, one_mul]; exact hr, ?_⟩
  have hg : IsUnit (algebraMap A' (Localization.Away (e.1 * r.1)) (e.1 * r.1)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hue : algebraMap A' (Localization.Away (e.1 * r.1)) e.1 = 1 := by
    have h : IsUnit (algebraMap A' (Localization.Away (e.1 * r.1)) e.1) := by
      rw [map_mul] at hg; exact isUnit_of_mul_isUnit_left hg
    have hi : IsIdempotentElem (algebraMap A' (Localization.Away (e.1 * r.1)) e.1) := by
      show _ * _ = _
      rw [← map_mul]; exact congrArg _ (congrArg Subtype.val he)
    exact (IsIdempotentElem.iff_eq_one_of_isUnit h).mp hi
  have hS : ∀ (s : S) (a : A), s * e = algebraMap A S a * e →
      algebraMap A' (Localization.Away (e.1 * r.1)) s.1 = algebraMap A (Localization.Away (e.1 * r.1)) a := by
    intro s a ha
    have h := congrArg (fun x : S => algebraMap A' (Localization.Away (e.1 * r.1)) x.1) ha
    simp only [Subalgebra.coe_mul, map_mul, hue, mul_one, Subalgebra.coe_algebraMap] at h
    rw [h, ← IsScalarTower.algebraMap_apply]
  have hur : algebraMap A' (Localization.Away (e.1 * r.1)) (e.1 * r.1) =
      algebraMap A (Localization.Away (e.1 * r.1)) a₀ := by
    rw [map_mul, hue, one_mul]; exact hS r a₀ ha₀
  obtain ⟨b₀, hb₀⟩ := hu₀.exists_left_inv
  have hw : algebraMap A (Localization.Away (e.1 * r.1)) b₀ *
      algebraMap A' (Localization.Away (e.1 * r.1)) (e.1 * r.1) = 1 := by
    rw [hur, ← map_mul, hb₀, map_one]
  intro z
  obtain ⟨⟨x, _, k, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (e.1 * r.1)) z
  obtain ⟨m, hm⟩ := hb x
  obtain ⟨c, hc⟩ := hN ⟨_, hm⟩
  have hcx : algebraMap A' (Localization.Away (e.1 * r.1)) (r.1 ^ m * x) =
      algebraMap A (Localization.Away (e.1 * r.1)) c := hS _ c hc
  have hrr : algebraMap A' (Localization.Away (e.1 * r.1)) r.1 =
      algebraMap A' (Localization.Away (e.1 * r.1)) (e.1 * r.1) := by rw [map_mul, hue, one_mul]
  rw [map_mul, map_pow, hrr] at hcx
  refine ⟨c * b₀ ^ (m + k), ?_⟩
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul]
  show _ = _ * algebraMap A' (Localization.Away (e.1 * r.1)) ((e.1 * r.1) ^ k)
  rw [map_mul, map_pow, map_pow (algebraMap A' _)]
  calc algebraMap A' (Localization.Away (e.1 * r.1)) x
      = algebraMap A' (Localization.Away (e.1 * r.1)) x *
        (algebraMap A (Localization.Away (e.1 * r.1)) b₀ *
          algebraMap A' (Localization.Away (e.1 * r.1)) (e.1 * r.1)) ^ (m + k) := by
        rw [hw, one_pow, mul_one]
    _ = (algebraMap A' (Localization.Away (e.1 * r.1)) (e.1 * r.1) ^ m *
          algebraMap A' (Localization.Away (e.1 * r.1)) x) *
        algebraMap A (Localization.Away (e.1 * r.1)) b₀ ^ (m + k) *
          algebraMap A' (Localization.Away (e.1 * r.1)) (e.1 * r.1) ^ k := by ring
    _ = _ := by rw [hcx]

end LateralTheory.E.FiniteChartSurjPf
