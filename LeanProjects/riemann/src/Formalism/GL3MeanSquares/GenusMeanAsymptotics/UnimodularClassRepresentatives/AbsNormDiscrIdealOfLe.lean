import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ConjOMemConjIdeal

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallB

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem det_update_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (x : ι → V)
    (a : ι → K) (i : ι) : b.det (Function.update x i (∑ k, a k • x k)) = a i * b.det x := by
  rw [Basis.det_apply, Basis.det_apply, ← Matrix.det_transpose,
    ← Matrix.det_transpose (b.toMatrix x)]
  have e : Matrix.transpose (b.toMatrix (Function.update x i (∑ k, a k • x k))) =
      (Matrix.transpose (b.toMatrix x)).updateRow i (∑ k, a k • Matrix.transpose (b.toMatrix x) k) := by
    ext r s
    rcases eq_or_ne r i with rfl | hr
    · simp [Basis.toMatrix_apply, Matrix.updateRow_self, Finset.sum_apply, map_sum, map_smul]
    · simp [Basis.toMatrix_apply, Matrix.updateRow_ne hr, Function.update_apply, hr]
  rw [e, Matrix.det_updateRow_sum, smul_eq_mul]

theorem exists_adjust (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {c : 𝓞 K}
    (hc : c ∉ P) : ∃ π ∈ P, c + π ∉ P ∧ c + π ∉ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  have hadd : ∀ π ∈ P, c + π ∉ P := fun π hπ h => hc (by simpa using P.sub_mem h hπ)
  have hle2 : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≤ P.comap (conjO K) := by
    refine Ideal.span_le.2 ?_
    rintro r ⟨s, hs, hrs⟩
    show conjO K r ∈ P
    have e : conjO K r = s := by
      apply IsFractionRing.injective (𝓞 K) K
      have e1 : algebraMap (𝓞 K) K (conjO K r) = star (algebraMap (𝓞 K) K r) := by
        first | rfl | simp [conjO]
      rw [e1, hrs, star_star]
    rw [e]
    exact hs
  have hne_top : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ ⊤ := by
    intro htop
    have h1 : (1 : 𝓞 K) ∈ P.comap (conjO K) := hle2 (by rw [htop]; exact Submodule.mem_top)
    rw [Ideal.mem_comap, map_one] at h1
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 h1)
  by_cases hc' : c ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P
  · have hnle : ¬ P ≤ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
      intro hle
      have hPe := hP.eq_of_le hne_top hle
      exact hc (by rw [hPe]; exact hc')
    obtain ⟨π, hπ, hπ'⟩ := SetLike.not_le_iff_exists.1 hnle
    refine ⟨π, hπ, hadd π hπ, fun h => hπ' ?_⟩
    have h3 := (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).sub_mem h hc'
    simpa using h3
  · exact ⟨0, P.zero_mem, by simpa using hc, by simpa using hc'⟩

theorem step_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) {A B : Submodule (𝓞 K) V} {y : V} (S : IsStep P A B y)
    (hB : Formalism.HermitianLatticesTheory.IsIntegralLat h B) (b : Basis (Fin (finrank K V)) K V) :
    discrIdeal h A ≤ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P * discrIdeal h B := by
  refine discrIdeal_le b fun x hx z hz => ?_
  have hxB : ∀ i, x i ∈ B := fun i => S.le (hx i)
  by_cases hδ : b.det x = 0
  · have : z = 0 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [hz, hδ, mul_zero, map_zero]
    rw [this]; exact Ideal.zero_mem _
  have hbas := (b.is_basis_iff_det).2 (isUnit_iff_ne_zero.2 hδ)
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).1
    (hbas.2 ▸ Submodule.mem_top : y ∈ Submodule.span K (Set.range x))
  let f : Option (Fin (finrank K V)) → K := fun o => o.elim 1 a
  obtain ⟨t, c, hc, j, hj⟩ := exists_prim f (j₀ := none) (by simp [f]) hP.ne_top
  have hf0 : f none = 1 := rfl
  have hfs : ∀ i, f (some i) = a i := fun i => rfl
  have hc0 : c none ∈ P := by
    apply S.mem_of_smul_mem hP
    have : c none • y = ∑ i, c (some i) • x i := by
      rw [← algebraMap_smul K, hc none, ← ha, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← algebraMap_smul K (c (some i)), hc (some i), smul_smul, hf0, hfs, mul_one]
    rw [this]; exact A.sum_mem fun i _ => A.smul_mem _ (hx i)
  obtain ⟨i, rfl⟩ : ∃ i, j = some i := by
    cases j with
    | none => exact absurd hc0 hj
    | some i => exact ⟨i, rfl⟩
  have hδi : b.det (Function.update x i y) = a i * b.det x := by rw [← ha, det_update_sum]
  have hrel : algebraMap (𝓞 K) K (c (some i)) * b.det x =
      algebraMap (𝓞 K) K (c none) * b.det (Function.update x i y) := by
    rw [hc, hc, hδi, hf0, hfs]; ring
  obtain ⟨π, hπ, hcP, hcQ⟩ := exists_adjust hK hP hj
  set c₁ := c (some i) + π with hc₁
  set c₀ := c none with hc₀
  have hcδ : algebraMap (𝓞 K) K c₁ * b.det x =
      algebraMap (𝓞 K) K c₀ * b.det (Function.update x i y) + algebraMap (𝓞 K) K π * b.det x := by
    rw [hc₁, map_add, add_mul, hrel]
  have hxk : ∀ k, k ≠ i → x k ∈ B := fun k _ => hxB k
  have huy := update_mem hxk S.mem
  obtain ⟨zyy, hyy⟩ := exists_mixed hB b huy huy
  obtain ⟨zyx, hyx⟩ := exists_mixed hB b huy hxB
  obtain ⟨zxy, hxy⟩ := exists_mixed hB b hxB huy
  have myy := mem_discrIdeal b huy hyy
  have mxx := mem_discrIdeal b hxB hz
  have myx : zyx ∈ discrIdeal h B :=
    mixed_mem hK hB b hxk S.mem (hxB i) (by rw [Function.update_eq_self]; exact hyx)
  have mxy : zxy ∈ discrIdeal h B :=
    mixed_mem hK hB b hxk (hxB i) S.mem (by rw [Function.update_eq_self]; exact hxy)
  have heq : conjO K c₁ * c₁ * z = conjO K c₀ * c₀ * zyy + conjO K c₀ * π * zyx +
      conjO K π * c₀ * zxy + conjO K π * π * z := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    simp only [map_add, map_mul, algebraMap_conjO, hz, hyy, hyx, hxy]
    have h1 : star (algebraMap (𝓞 K) K c₁) * algebraMap (𝓞 K) K c₁ *
        (star (b.det x) * gdet h b * b.det x) =
        star (algebraMap (𝓞 K) K c₁ * b.det x) * gdet h b * (algebraMap (𝓞 K) K c₁ * b.det x) := by
      rw [star_mul']; ring
    rw [h1, hcδ, star_add, star_mul', star_mul']
    ring
  have hmem : conjO K c₁ * c₁ ∈ col (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P * discrIdeal h B) z := by
    rw [mem_col, heq]
    exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (term_mem hc0 hc0 myy)
      (term_mem hc0 hπ myx)) (term_mem hπ hc0 mxy)) (term_mem hπ hπ mxx)
  have hPP : P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≤
      col (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P * discrIdeal h B) z :=
    fun r hr => Ideal.mul_mem_mul hr mxx
  apply mem_of_col_eq_top
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hcc : ∀ w : 𝓞 K, conjO K w ∈ P → w ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    intro w hw; rw [conjIdeal_eq_comap, Ideal.mem_comap]; exact hw
  have hcc' : ∀ w : 𝓞 K, conjO K w ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P → w ∈ P := by
    intro w hw; rw [conjIdeal_eq_comap, Ideal.mem_comap, conjO_conjO] at hw; exact hw
  rcases hM.isPrime.mul_le.1 (hPP.trans hle) with h1 | h1
  · have hMP := hP.eq_of_le hM.ne_top h1
    rcases hM.isPrime.mem_or_mem (hle hmem) with h2 | h2
    · exact hcQ (hcc _ (hMP ▸ h2))
    · exact hcP (hMP ▸ h2)
  · have hMP := (conjIdeal_isMaximal hK hP).eq_of_le hM.ne_top h1
    rcases hM.isPrime.mem_or_mem (hle hmem) with h2 | h2
    · exact hcP (hcc' _ (hMP ▸ h2))
    · exact hcQ (hMP ▸ h2)

omit [StarRing K] [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem IsStep.relIndex {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {A B : Submodule (𝓞 K) V} {y : V}
    (S : IsStep P A B y) : A.toAddSubgroup.relIndex B.toAddSubgroup = Ideal.absNorm P := by
  classical
  let f : 𝓞 K →+ B.toAddSubgroup :=
    { toFun := fun c => ⟨c • y, B.smul_mem c S.mem⟩
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp [add_smul] }
  let g : 𝓞 K →+ B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup :=
    (QuotientAddGroup.mk' _).comp f
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨c, hc⟩ := S.gen x.1 x.2
    refine ⟨c, ?_⟩
    simp only [g, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply]
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simpa [f, neg_add_eq_sub] using hc
  have hker : g.ker = P.toAddSubgroup := by
    ext c
    simp only [AddMonoidHom.mem_ker, g, f, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact ⟨fun h => S.mem_of_smul_mem hP h, fun h => S.smul c h⟩
  rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card,
    ← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv, hker,
    Ideal.absNorm_apply]
  rfl

theorem absNorm_discrIdeal_of_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {B : Submodule (𝓞 K) V} (hB : Formalism.HermitianLatticesTheory.IsIntegralLat h B)
    (b : Basis (Fin (finrank K V)) K V) :
    ∀ (n : ℕ) (A : Submodule (𝓞 K) V), A ≤ B → A.toAddSubgroup.relIndex B.toAddSubgroup = n →
      n ≠ 0 → Ideal.absNorm (discrIdeal h A) = n ^ 2 * Ideal.absNorm (discrIdeal h B) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hAB hn hn0
  by_cases hBA : B ≤ A
  · have : A = B := le_antisymm hAB hBA
    subst this
    rw [AddSubgroup.relIndex_self] at hn
    rw [← hn, one_pow, one_mul]
  obtain ⟨y₀, hy₀B, hy₀A⟩ := SetLike.not_le_iff_exists.1 hBA
  let J : Ideal (𝓞 K) := A.comap (LinearMap.toSpanSingleton (𝓞 K) V y₀)
  have hJ : ∀ c, c ∈ J ↔ c • y₀ ∈ A := fun c => Iff.rfl
  have hJtop : J ≠ ⊤ := by
    intro hJt
    have : (1 : 𝓞 K) ∈ J := hJt ▸ Submodule.mem_top
    rw [hJ, one_smul] at this
    exact hy₀A this
  have hJbot : J ≠ ⊥ := by
    intro hJb
    obtain ⟨k, hk0, -, hk⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero
      (H := A.toAddSubgroup) (K := B.toAddSubgroup) (hn ▸ hn0) (a := y₀) hy₀B
    have h1 : (k : 𝓞 K) ∈ J := by
      rw [hJ, Nat.cast_smul_eq_nsmul]
      exact hk.1
    rw [hJb, Ideal.mem_bot] at h1
    exact hk0.ne' (by exact_mod_cast h1)
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJtop
  obtain ⟨J', hJ'⟩ := Ideal.dvd_iff_le.2 hJP
  have hJ'0 : J' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hJ'
    exact hJbot hJ'
  have hnle : ¬ J' ≤ J := by
    intro hle
    have h1 : P * J' = 1 * J' := by
      rw [one_mul, ← hJ']
      exact le_antisymm (hJ' ▸ Ideal.mul_le_right) hle
    exact hP.ne_top (by rw [mul_right_cancel₀ hJ'0 h1, Ideal.one_eq_top])
  obtain ⟨c, hcJ', hcJ⟩ := SetLike.not_le_iff_exists.1 hnle
  have S : IsStep P A (A ⊔ Submodule.span (𝓞 K) {c • y₀}) (c • y₀) := by
    refine ⟨le_sup_left, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _), hcJ,
      fun π hπ => ?_, fun x hx => ?_⟩
    · rw [smul_smul, ← hJ, hJ']
      exact Ideal.mul_mem_mul hπ hcJ'
    · obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.1 hw
      exact ⟨e, by rwa [add_sub_cancel_right]⟩
  have hA'B : A ⊔ Submodule.span (𝓞 K) {c • y₀} ≤ B :=
    sup_le hAB ((Submodule.span_singleton_le_iff_mem _ _).2 (B.smul_mem c hy₀B))
  have hA' : Formalism.HermitianLatticesTheory.IsIntegralLat h (A ⊔ Submodule.span (𝓞 K) {c • y₀}) :=
    fun x hx w hw => hB x (hA'B hx) w (hA'B hw)
  have hmul := AddSubgroup.relIndex_mul_relIndex A.toAddSubgroup
    (A ⊔ Submodule.span (𝓞 K) {c • y₀}).toAddSubgroup B.toAddSubgroup S.le hA'B
  rw [S.relIndex hP, hn] at hmul
  have hq1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  have hq0 : Ideal.absNorm P ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hmul; exact hn0 hmul.symm
  have hn'0 : (A ⊔ Submodule.span (𝓞 K) {c • y₀}).toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hmul; exact hn0 hmul.symm
  have hlt : (A ⊔ Submodule.span (𝓞 K) {c • y₀}).toAddSubgroup.relIndex B.toAddSubgroup < n := by
    rw [← hmul]
    have h2 : 2 ≤ Ideal.absNorm P := by omega
    nlinarith [Nat.pos_of_ne_zero hn'0]
  have hI : discrIdeal h A = P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P *
      discrIdeal h (A ⊔ Submodule.span (𝓞 K) {c • y₀}) :=
    le_antisymm (step_le hK hP S hA' b) (step_ge hK hP S hA' b)
  rw [hI, map_mul, map_mul, absNorm_conjIdeal hK, ih _ hlt _ hA'B rfl hn'0, ← hmul]
  ring

end Formalism.HermitianLattices.Ext.L3.BallB
