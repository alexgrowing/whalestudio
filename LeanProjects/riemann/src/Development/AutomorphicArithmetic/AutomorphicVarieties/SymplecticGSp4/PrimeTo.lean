import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem pt_modEq_one (l d : ℕ) (hd : d ≠ 0) (h : l.Coprime d) :
    ∀ᶠ n : ℕ in Filter.atTop, l ^ n.factorial ≡ 1 [MOD d] := by
  filter_upwards [Filter.eventually_ge_atTop d.totient] with n hn
  obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.totient_pos.2 (Nat.pos_of_ne_zero hd)) hn
  rw [hk, pow_mul]
  simpa using (Nat.ModEq.pow_totient h).pow k

private theorem pt_dvd (l a : ℕ) : ∀ᶠ n : ℕ in Filter.atTop, l ^ a ∣ l ^ n.factorial := by
  filter_upwards [Filter.eventually_ge_atTop a] with n hn
  exact pow_dvd_pow _ (hn.trans (Nat.self_le_factorial n))

private theorem pt_const (l : ℕ) (hl : l.Prime) {H : Type} [Group H] [Finite H] (x : H) :
    ∃ y, ∀ᶠ n : ℕ in Filter.atTop, x ^ l ^ n.factorial = y := by
  have h0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨a, d, hnd, hod⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 l hl.one_lt.ne'
  have hcop : l.Coprime d := (Nat.Prime.coprime_iff_not_dvd hl).2 hnd
  have hd : d ≠ 0 := by
    rintro rfl
    exact h0 (by simpa using hod)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((pt_modEq_one l d hd hcop).and (pt_dvd l a))
  refine ⟨x ^ l ^ N.factorial, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  rw [pow_eq_pow_iff_modEq, hod, ← Nat.modEq_and_modEq_iff_modEq_mul (Nat.Coprime.pow_left a hcop)]
  obtain ⟨h1, h2⟩ := hN n hn
  obtain ⟨h1', h2'⟩ := hN N le_rfl
  exact ⟨(Nat.modEq_zero_iff_dvd.2 h2).trans (Nat.modEq_zero_iff_dvd.2 h2').symm, h1.trans h1'.symm⟩

private theorem pt_exists (l : ℕ) (hl : l.Prime) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (g : Γ) :
    ∃ g', Filter.Tendsto (fun n : ℕ => g ^ l ^ n.factorial) Filter.atTop (nhds g') := by
  obtain ⟨g', -, hg'⟩ : ∃ g' ∈ Set.univ, ClusterPt g' (Filter.map (fun n : ℕ => g ^ l ^ n.factorial) Filter.atTop) :=
    isCompact_univ.exists_clusterPt (Filter.le_principal_iff.2 Filter.univ_mem)
  refine ⟨g', ?_⟩
  rw [(nhds_basis_opens g').tendsto_right_iff]
  rintro V ⟨hgV, hVo⟩
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (hVo.preimage (continuous_mul_left g')) (by simpa using hgV)
  haveI : H.toSubgroup.Normal := H.isNormal'
  haveI : Finite (Γ ⧸ H.toSubgroup) := H.toSubgroup.quotient_finite_of_isOpen H.isOpen'
  obtain ⟨y, hy⟩ := pt_const l hl (QuotientGroup.mk (s := H.toSubgroup) g)
  have hnh : ∀ᶠ z in nhds g', g'⁻¹ * z ∈ H.toSubgroup := by
    have hc : Continuous (fun z : Γ => g'⁻¹ * z) := continuous_const.mul continuous_id
    refine hc.continuousAt.preimage_mem_nhds (H.isOpen'.mem_nhds ?_)
    show g'⁻¹ * g' ∈ H.toSubgroup
    rw [inv_mul_cancel]
    exact H.toSubgroup.one_mem
  have hfr := hg'.frequently hnh
  rw [Filter.frequently_map] at hfr
  obtain ⟨n, hn1, hn2⟩ := (hfr.and_eventually hy).exists
  have hy' : y = QuotientGroup.mk g' := by
    rw [← hn2, ← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq]
    exact hn1
  filter_upwards [hy] with m hm
  rw [hy', ← QuotientGroup.mk_pow, QuotientGroup.eq] at hm
  have := hH (H.toSubgroup.inv_mem hm)
  simpa using this

private theorem pt_step {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (I J : Ideal R) (hJ : J ≤ I) (l : ℕ)
    (hl : (l : R) ∈ I) (X : Matrix ι ι R) (hX : ∀ a b, (X - 1) a b ∈ J) : ∀ a b, (X ^ l - 1) a b ∈ I * J := by
  classical
  have hXi : ∀ i : ℕ, ∀ a b, (X ^ i - 1 : Matrix ι ι R) a b ∈ J := by
    intro i
    have h0 : (Ideal.Quotient.mk J).mapMatrix (X - 1) = 0 := by
      ext a b
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hX a b
    have h1 : (Ideal.Quotient.mk J).mapMatrix X = 1 := by
      rw [map_sub, map_one, sub_eq_zero] at h0
      exact h0
    have h2 : (Ideal.Quotient.mk J).mapMatrix (X ^ i - 1) = 0 := by
      rw [map_sub, map_pow, h1, one_pow, map_one, sub_self]
    intro a b
    have := congrFun (congrFun h2 a) b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  have hgeom : X ^ l - 1 = (X - 1) * ((l : Matrix ι ι R) + ∑ i ∈ Finset.range l, (X ^ i - 1)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_one, add_sub_cancel, mul_geom_sum]
  intro a b
  rw [hgeom, Matrix.mul_apply]
  refine Ideal.sum_mem _ (fun c _ => ?_)
  have hW : ((l : Matrix ι ι R) + ∑ i ∈ Finset.range l, (X ^ i - 1)) c b ∈ I := by
    rw [Matrix.add_apply, Matrix.sum_apply]
    refine I.add_mem ?_ (I.sum_mem fun i _ => hJ (hXi i c b))
    by_cases hcb : c = b <;> simp [hcb, hl, Matrix.natCast_apply]
  rw [mul_comm ((X - 1) a c)]
  exact Ideal.mul_mem_mul hW (hX a c)

private theorem pt_pow {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (I : Ideal R) (l : ℕ)
    (hl : (l : R) ∈ I) (X : Matrix ι ι R) (hX : ∀ a b, (X - 1) a b ∈ I) (k : ℕ) :
    ∀ a b, (X ^ l ^ k - 1) a b ∈ I ^ (k + 1) := by
  induction k with
  | zero => simpa using hX
  | succ k ih =>
    intro a b
    have h := pt_step I (I ^ (k + 1)) (Ideal.pow_le_self (Nat.succ_ne_zero k)) l hl (X ^ l ^ k) ih a b
    rw [← pow_mul, ← pow_succ] at h
    rw [pow_succ' I (k + 1)]
    exact h

theorem UpperTheory.V.GradeZeroInterpolatingElement.primeTo :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [T2Space Γ] (g : Γ), (∃ g', Filter.Tendsto (fun n : ℕ => g ^ l ^ n.factorial) Filter.atTop (nhds g')) ∧ ∀ g', Filter.Tendsto (fun n : ℕ => g ^ l ^ n.factorial) Filter.atTop (nhds g') → ∀ (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (ι : Type) [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (m : ℕ), l.Coprime m → rbar g ^ m = 1 → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : Lift O rbar R), rbar g' = rbar g ∧ ρ.hom g' ^ m = 1 := by
  intro l _ Γ _ _ _ _ _ _ g
  have hl : l.Prime := Fact.out
  refine ⟨pt_exists l hl Γ g, ?_⟩
  intro g' hlim O _ _ _ _ ι _ _ rbar m hcop hgm R _ _ _ ρ
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hl.one_lt.ne' (Nat.coprime_zero_right l |>.1 hcop)
  have key : ∀ {M : Type} [Monoid M] (x : M) (k : ℕ), x ^ m = 1 → k ≡ 1 [MOD m] → x ^ k = x := by
    intro M _ x k hx hk
    have hk' : k % orderOf x = 1 % orderOf x := Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hx) hk
    rw [← pow_mod_orderOf, hk', pow_mod_orderOf, pow_one]
  have hcong := pt_modEq_one l m hm0 hcop
  have hloc : ∀ N : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      (Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix (ρ.hom (g ^ l ^ n.factorial)) =
      (Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix (ρ.hom g') := by
    intro N
    have h1 : ∀ᶠ y in nhds g', ∀ a b, Ideal.Quotient.mk (maximalIdeal R ^ N) (ρ.hom y a b) =
        Ideal.Quotient.mk (maximalIdeal R ^ N) (ρ.hom g' a b) := by
      simp only [Filter.eventually_all]
      intro a b
      exact (ρ.cont a b N).eventually_eq g'
    filter_upwards [hlim.eventually h1] with n hn
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact hn a b
  have hres : ∀ x y : R, Ideal.Quotient.mk (maximalIdeal R ^ 1) x = Ideal.Quotient.mk (maximalIdeal R ^ 1) y →
      res O R x = res O R y := by
    intro x y h
    rw [Ideal.Quotient.eq, pow_one] at h
    rw [← sub_eq_zero, ← map_sub]
    exact (res_eq_zero_iff O R _).2 h
  have hA : rbar g' = rbar g := by
    obtain ⟨n, hn1, hn2⟩ := ((hloc 1).and hcong).exists
    ext a b
    rw [← ρ.red g' a b]
    have e1 := congrFun (congrFun hn1 a) b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    rw [← hres _ _ e1, ρ.red, map_pow, key (rbar g) _ hgm hn2]
  have hlM : ((l : ℕ) : R) ∈ maximalIdeal R := by
    rw [← res_eq_zero_iff O R, map_natCast]
    exact CharP.cast_eq_zero _ l
  have hX : ∀ a b, ((ρ.hom g) ^ m - 1) a b ∈ maximalIdeal R := by
    intro a b
    rw [← res_eq_zero_iff O R, Matrix.sub_apply, map_sub, ← map_pow, ρ.red, map_pow, hgm]
    by_cases hab : a = b <;> simp [hab, Matrix.one_apply]
  have hB : ∀ N : ℕ, ∀ a b, ((ρ.hom g') ^ m - 1) a b ∈ maximalIdeal R ^ N := by
    intro N
    have hfin : ∀ᶠ n : ℕ in Filter.atTop, N ≤ n.factorial + 1 := by
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      exact hn.trans ((Nat.self_le_factorial n).trans (Nat.le_succ _))
    obtain ⟨n, hn1, hn2⟩ := ((hloc N).and hfin).exists
    have hp := pt_pow (maximalIdeal R) l hlM _ hX n.factorial
    have hq : (Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix (((ρ.hom g) ^ m) ^ l ^ n.factorial) = 1 := by
      rw [← sub_eq_zero, ← map_one ((Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix), ← map_sub]
      ext a b
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_le_pow_right hn2 (hp a b)
    have e : (ρ.hom (g ^ l ^ n.factorial)) ^ m = ((ρ.hom g) ^ m) ^ l ^ n.factorial := by
      rw [map_pow, ← pow_mul, ← pow_mul, mul_comm]
    have hr : (Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix ((ρ.hom g') ^ m) = 1 := by
      rw [map_pow, ← hn1, ← map_pow, e]
      exact hq
    intro a b
    have h2 : (Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix ((ρ.hom g') ^ m - 1) = 0 := by
      rw [map_sub, hr, map_one, sub_self]
    have := congrFun (congrFun h2 a) b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  refine ⟨hA, ?_⟩
  have hbot : ⨅ i : ℕ, maximalIdeal R ^ i = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
  rw [← sub_eq_zero]
  ext a b
  have hmem : ((ρ.hom g') ^ m - 1) a b ∈ ⨅ i : ℕ, maximalIdeal R ^ i := Ideal.mem_iInf.2 (fun N => hB N a b)
  rw [hbot, Ideal.mem_bot] at hmem
  rw [Matrix.zero_apply]
  exact hmem
