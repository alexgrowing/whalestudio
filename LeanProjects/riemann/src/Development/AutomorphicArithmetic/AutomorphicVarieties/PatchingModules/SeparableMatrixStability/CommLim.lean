import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem eventually_le_of_le_atTop {U : Filter ℕ} (h : U ≤ atTop) (n : ℕ) : ∀ᶠ N in U, n ≤ N :=
  h (eventually_ge_atTop n)

theorem UpperTheory.V.Pa.comm_lim :
    ∀ (l : ℕ) [Fact l.Prime] (Ph B : Type) [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph] [CompactSpace Ph] [TotallyDisconnectedSpace Ph] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [CompactSpace B] [TotallyDisconnectedSpace B] (Γ : ℕ → Type) [∀ N, Group (Γ N)] [∀ N, TopologicalSpace (Γ N)] [∀ N, IsTopologicalGroup (Γ N)] [∀ N, CompactSpace (Γ N)] [∀ N, TotallyDisconnectedSpace (Γ N)] (π : ∀ N, Ph →* Γ N) (πo : Ph →* B) (U : Ultrafilter ℕ) (ph ta : ∀ N, Γ N) (q : ℕ → ℕ) (a b : B), (U : Filter ℕ) ≤ atTop → (∀ N, Continuous (π N) ∧ Function.Surjective (π N)) → Continuous πo → (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), (π N).ker ⊔ V.toSubgroup = πo.ker ⊔ V.toSubgroup) → (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), Close (π N) πo V.toSubgroup (ph N) a) → (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), Close (π N) πo V.toSubgroup (ta N) b) → (∀ N, q N ≡ 1 [MOD l ^ N]) → (∀ N, (ph N)⁻¹ * ta N * ph N = ta N ^ q N) → (∀ N (W : OpenNormalSubgroup (Γ N)), ∃ e : ℕ, ta N ^ l ^ e ∈ W) → a * b = b * a := by
  intro l _ Ph B _ _ _ _ _ _ _ _ _ _ Γ _ _ _ _ _ π πo U ph ta q a b hUa hπ hπo hker hph hta hq hrel hlw
  have hl : l.Prime := Fact.out
  have key : ∀ W : OpenNormalSubgroup B, (a * b)⁻¹ * (b * a) ∈ W.toSubgroup := by
    intro W
    haveI : W.toSubgroup.Normal := W.isNormal'
    haveI : Finite (B ⧸ W.toSubgroup) :=
      W.toSubgroup.quotient_finite_of_isOpen W.toOpenSubgroup.isOpen
    haveI : W.toSubgroup.FiniteIndex := W.toSubgroup.finiteIndex_of_finite_quotient
    have hn0 : W.toSubgroup.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    let V : OpenNormalSubgroup Ph :=
      { toOpenSubgroup := ⟨W.toSubgroup.comap πo, W.toOpenSubgroup.isOpen.preimage hπo⟩
        isNormal' := Subgroup.Normal.comap W.isNormal' πo }
    have hVmem : ∀ x, x ∈ V.toSubgroup ↔ πo x ∈ W.toSubgroup := fun x => Iff.rfl
    obtain ⟨N, hNn, hk, h1, h2⟩ := ((eventually_le_of_le_atTop hUa W.toSubgroup.index).and
      ((hker V).and ((hph V).and (hta V)))).exists
    obtain ⟨g1, g1', e1, e1', hg1⟩ := h1
    obtain ⟨g2, g2', e2, e2', hg2⟩ := h2
    have hkV : (π N).ker ≤ V.toSubgroup := by
      have : (π N).ker ≤ πo.ker ⊔ V.toSubgroup := hk ▸ le_sup_left
      refine this.trans (sup_le ?_ le_rfl)
      intro x hx
      rw [hVmem, MonoidHom.mem_ker.mp hx]
      exact W.toSubgroup.one_mem
    set mk : B →* B ⧸ W.toSubgroup := QuotientGroup.mk' W.toSubgroup with hmk
    have eqmk : ∀ x y : Ph, x⁻¹ * y ∈ V.toSubgroup → mk (πo x) = mk (πo y) := by
      intro x y h
      rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have := (hVmem _).mp h
      simpa [map_mul, map_inv] using this
    have hA : mk (πo g1) = mk a := by rw [← e1']; exact eqmk _ _ hg1
    have hB : mk (πo g2) = mk b := by rw [← e2']; exact eqmk _ _ hg2
    have hrelq : (mk a)⁻¹ * mk b * mk a = mk b ^ q N := by
      have hk1 : (g1⁻¹ * g2 * g1) ⁻¹ * g2 ^ q N ∈ V.toSubgroup := by
        apply hkV
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv, map_pow, e1, e2, hrel N]
        group
      have := eqmk _ _ hk1
      simp only [map_mul, map_inv, map_pow, hA, hB] at this
      exact this
    have hW'ex : ∃ W' : OpenNormalSubgroup (Γ N), ∀ x, π N x ∈ W'.toSubgroup → x ∈ V.toSubgroup := by
      have hVc : IsClosed ((V.toSubgroup : Set Ph)ᶜ) := V.toOpenSubgroup.isOpen.isClosed_compl
      have hcm : IsClosedMap (π N) := (hπ N).1.isClosedMap
      have hS : IsOpen ((π N '' (V.toSubgroup : Set Ph)ᶜ)ᶜ) := (hcm _ hVc).isOpen_compl
      have h1S : (1 : Γ N) ∈ (π N '' (V.toSubgroup : Set Ph)ᶜ)ᶜ := by
        rintro ⟨x, hx, hx1⟩
        exact hx (hkV (MonoidHom.mem_ker.mpr hx1))
      obtain ⟨W', hW'⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hS h1S
      refine ⟨W', fun x hx => ?_⟩
      by_contra hxV
      exact hW' hx ⟨x, hxV, rfl⟩
    obtain ⟨W', hW'⟩ := hW'ex
    obtain ⟨e, he⟩ := hlw N W'
    have hbe : mk b ^ l ^ e = 1 := by
      have h3 : g2 ^ l ^ e ∈ V.toSubgroup := hW' _ (by rw [map_pow, e2]; exact he)
      have h' := eqmk 1 (g2 ^ l ^ e) (by simpa using h3)
      simp only [map_one, map_pow, hB] at h'
      exact h'.symm
    have hbn : mk b ^ W.toSubgroup.index = 1 := by
      rw [← map_pow, hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact W.toSubgroup.pow_index_mem b
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one hbe)
    have hc1 : l ^ c ≤ W.toSubgroup.index := by
      rw [← hc]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (orderOf_dvd_of_pow_eq_one hbn)
    have hc2 : c < l ^ c := Nat.lt_pow_self hl.one_lt
    have hdiv : orderOf (mk b) ∣ l ^ N := by
      rw [hc]
      exact pow_dvd_pow l (by omega)
    have hbq : mk b ^ q N = mk b := by
      have h4 : q N ≡ 1 [MOD orderOf (mk b)] := Nat.ModEq.of_dvd hdiv (hq N)
      simpa using pow_eq_pow_iff_modEq.mpr h4
    have hcomm : mk a * mk b = mk b * mk a := by
      rw [hbq] at hrelq
      calc mk a * mk b = mk a * ((mk a)⁻¹ * mk b * mk a) := by rw [hrelq]
        _ = mk b * mk a := by group
    have h5 : mk (a * b) = mk (b * a) := by simp only [map_mul, hcomm]
    rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h5
    exact h5
  by_contra hne
  have hx1 : (a * b)⁻¹ * (b * a) ≠ 1 := fun h => hne (inv_mul_eq_one.mp h)
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := (a * b)⁻¹ * (b * a))) (by simpa [eq_comm] using hx1)
  exact hH (key H) rfl
