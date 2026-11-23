import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UniformizerOfResidueIndep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GoodPrimesProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormByPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ComponentFormProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FsumEqSum

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem fsum_le_of {α : Type*} (s : Set α) (f g : α → ℤ) (hf : {x | x ∈ s ∧ f x ≠ 0}.Finite)
    (hg : {x | x ∈ s ∧ g x ≠ 0}.Finite) (r : ℝ) (hle : ∀ x ∈ s, (f x : ℝ) ≤ r * g x) :
    ((∑ᶠ x ∈ s, f x : ℤ) : ℝ) ≤ r * ((∑ᶠ x ∈ s, g x : ℤ) : ℝ) := by
  classical
  set u : Finset α := (hf.union hg).toFinset with hu
  have hus : ∀ x ∈ u, x ∈ s := by
    intro x hx
    simp only [hu, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq] at hx
    rcases hx with h | h
    · exact h.1
    · exact h.1
  have ef : ∑ᶠ x ∈ s, f x = ∑ x ∈ u, f x := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext x
    simp only [hu, Set.Finite.coe_toFinset, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
      Function.mem_support]
    tauto
  have eg : ∑ᶠ x ∈ s, g x = ∑ x ∈ u, g x := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext x
    simp only [hu, Set.Finite.coe_toFinset, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
      Function.mem_support]
    tauto
  rw [ef, eg, Int.cast_sum, Int.cast_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun x hx => hle x (hus x hx)

theorem wx_mem (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) : d.wx x c ∈ 𝒜 c d.wL := by
  haveI := hd.tower c
  unfold wx
  rw [Finset.sum_apply]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [Pi.smul_apply, ← algebraMap_smul (Ω c) (x j) (d.w j c)]
  exact Submodule.smul_mem _ _ (hd.w_mem j c)

theorem pow_mem_ne (hd : d.AxH 𝒜) {G : WT} {ta : ∀ c, A c} (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0)
    (n : ℕ) : ∀ c, (ta ^ (n + 1)) c ∈ 𝒜 c ((n + 1) • G) ∧ (ta ^ (n + 1)) c ≠ 0 := by
  intro c
  haveI := hd.graded c
  induction n with
  | zero => simpa using hta c
  | succ n ih =>
    rw [pow_succ, Pi.mul_apply, succ_nsmul G (n + 1)]
    exact ⟨SetLike.mul_mem_graded ih.1 (hta c).1, hd.mul_ne_zero c ih.1 (hta c).1 ih.2 (hta c).2⟩

private lemma finsum_mem_const_mul {α : Type*} (s : Set α) (f : α → ℤ) (k : ℤ) (hk : k ≠ 0) :
    ∑ᶠ x ∈ s, k * f x = k * ∑ᶠ x ∈ s, f x := by
  classical
  have hs : s ∩ Function.support (fun x => k * f x) = s ∩ Function.support f := by
    ext x
    simp [hk]
  by_cases hf : (s ∩ Function.support f).Finite
  · rw [finsum_mem_eq_sum_of_inter_support_eq (fun x => k * f x) (t := hf.toFinset) (by
        ext x
        simp [hk]
        try tauto),
      finsum_mem_eq_sum_of_inter_support_eq f (t := hf.toFinset) (by
        ext x
        simp
        try tauto),
      Finset.mul_sum]
  · rw [finsum_mem_eq_zero_of_infinite hf, finsum_mem_eq_zero_of_infinite (by rwa [hs]), mul_zero]

private lemma nP_pow_succ_eq_succ_mul (hd : d.AxH 𝒜) (h : d.S1) {G : WT} {ta : ∀ c, A c}
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    (n : ℕ) : d.nP h c ((n + 1) • G) ((ta ^ (n + 1)) c) p = ((n : ℤ) + 1) * d.nP h c G (ta c) p := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (ta ^ (n + 1 + 1)) c = (ta ^ (n + 1)) c * ta c := by rw [pow_succ, Pi.mul_apply]
    rw [e, succ_nsmul G (n + 1), d.nP_mul hd h c (d.pow_mem_ne hd hta n c).1 (hta c).1
      (d.pow_mem_ne hd hta n c).2 (hta c).2 hp, ih]
    push_cast
    ring

theorem aG_pow (hd : d.AxH 𝒜) (h : d.S1) {G : WT} {ta : ∀ c, A c}
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) (n : ℕ) :
    d.aG h ((n + 1) • G) (ta ^ (n + 1)) = (n + 1) * d.aG h G ta := by
  unfold aG
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← finsum_mem_const_mul _ (fun p => d.nP h c G (ta c) p * (d.dg (d.gen p) : ℤ)) ((n : ℤ) + 1) (by positivity)]
  refine finsum_mem_congr rfl fun p hp => ?_
  rw [nP_pow_succ_eq_succ_mul d hd h hta c hp n, mul_assoc]

theorem aG_nonneg (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (ta : ∀ c, A c)
    (hord : ∀ c v, d.admitted c v → 0 ≤ d.ord c v G (ta c)) : 0 ≤ d.aG h G ta := by
  unfold aG
  refine Finset.sum_nonneg fun c _ => ?_
  refine finsum_nonneg fun p => finsum_nonneg fun hp => ?_
  exact mul_nonneg (d.nP_nonneg hd h c hp G (ta c) (hord c)) (by positivity)

private lemma ratio_zero_left {F0 V0 : Type*} [Field F0] [AddCommGroup V0] [Module F0 V0] {g : V0}
    (hg : g ≠ 0) : ratio (Ω := F0) (0 : V0) g = 0 := by
  unfold ratio
  split_ifs with h0
  · rcases smul_eq_zero.1 h0.choose_spec.symm with h1 | h1
    · exact h1
    · exact absurd h1 hg
  · rfl

theorem thp_ne (hd : d.AxH 𝒜) (c : ι) : ∃ k, d.thp k c ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨e, he, -, hy⟩ := hd.a4
  obtain ⟨q, hq, p, hp⟩ := hy 1
  have key := hp c
  simp only [Pi.one_apply, mul_one] at key
  rw [Finset.sum_eq_zero] at key
  · exact hq c key
  · intro k _
    rw [hcon, ratio_zero_left (he c).2, map_zero, mul_zero]

theorem aG_sb (hd : d.AxH 𝒜) (h : d.S1) :
    d.aG h d.wL (fun c => d.w (d.jc c) c) =
      d.del + ∑ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.Ep h c p * (d.dg (d.gen p) : ℤ) := by
  unfold aG del
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨F, -, -, -, h4, -⟩ := d.componentForm_properties hd h c
  have hf := (d.good_primes_properties hd h c).2.2.2 _ (hd.w_mem _ c) (hd.w_base c)
  have hE := d.Ep_ne hd h c _ (hd.w_mem _ c) (hd.w_base c)
  rw [← h4, ← finsum_mem_add_distrib']
  · exact finsum_mem_congr rfl fun p hp => by rw [d.nP_split hd h c hp]; ring
  · exact hf.subset fun p ⟨hp, hs⟩ => ⟨hp, fun h0 => hs (by simp [h0])⟩
  · exact hE.subset fun p ⟨hp, hs⟩ => ⟨hp, fun h0 => hs (by simp [h0])⟩

theorem aG_wx (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K) (hx : ∀ c, d.wx x c ≠ 0) :
    d.aG h d.wL (d.wx x) = d.aG h d.wL (fun c => d.w (d.jc c) c) :=
  (d.norm_factorization hd h).2.1 _ _ _ (fun c => ⟨d.wx_mem hd x c, hx c⟩) (fun c => ⟨hd.w_mem _ c, hd.w_base c⟩)

end Data

end ReciprocityTheory.ChartRestriction.G.T0
