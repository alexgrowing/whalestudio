import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem UpperTheory.V.CA.fl_nak {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (I : Ideal B)
    (P : Submodule B M) (h : P ⊔ I ^ 1 • ⊤ = ⊤) (N : ℕ) : P ⊔ I ^ N • ⊤ = ⊤ := by
  induction N with
  | zero => simp
  | succ n ih =>
    refine top_le_iff.1 (ih.ge.trans (sup_le le_sup_left ?_))
    have e : I ^ n • (⊤ : Submodule B M) = I ^ n • (P ⊔ I ^ 1 • ⊤) := by rw [h]
    rw [e, Submodule.smul_sup, pow_one, ← Submodule.mul_smul, ← pow_succ]
    exact sup_le_sup_right Submodule.smul_le_right _

private theorem UpperTheory.V.CA.fl_card {B M σ : Type} [CommRing B] [AddCommGroup M] [Module B M] [Fintype σ] (I : Ideal B)
    [Finite (B ⧸ I)] (v : σ → M) (P : Submodule B M) (hI : I • ⊤ ≤ P)
    (h : Submodule.span B (Set.range v) ⊔ P = ⊤) :
    P.toAddSubgroup.index ≠ 0 ∧ P.toAddSubgroup.index ≤ Nat.card (B ⧸ I) ^ Fintype.card σ := by
  classical
  let f : (σ → B ⧸ I) → M ⧸ P := fun a => Submodule.Quotient.mk (∑ i, (a i).out • v i)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P y
    have hy : y ∈ Submodule.span B (Set.range v) ⊔ P := h ▸ Submodule.mem_top
    obtain ⟨z, hz, p, hp, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B).1 hz
    refine ⟨fun i => Ideal.Quotient.mk I (a i), ?_⟩
    simp only [f]
    rw [Submodule.Quotient.eq, ← sub_sub, ← Finset.sum_sub_distrib]
    refine P.sub_mem (P.sum_mem fun i _ => ?_) hp
    rw [← sub_smul]
    refine hI (Submodule.smul_mem_smul ?_ Submodule.mem_top)
    rw [← Ideal.Quotient.eq]
    exact Ideal.Quotient.mk_out _
  have hfin : Finite (M ⧸ P) := Finite.of_surjective f hf
  have e : P.toAddSubgroup.index = Nat.card (M ⧸ P) := rfl
  rw [e]
  refine ⟨Nat.card_pos.ne', ?_⟩
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_fun, Nat.card_eq_fintype_card (α := σ)] at this

private theorem UpperTheory.V.CA.fl_stab {B M ι : Type} [CommRing B] [AddCommGroup M] [Module B M] [SemilatticeInf ι]
    [Nonempty ι] (J : ι → Submodule B M) (hJ : Monotone J) (C : ℕ)
    (h : ∀ U, (J U).toAddSubgroup.index ≠ 0 ∧ (J U).toAddSubgroup.index ≤ C) :
    ∃ U₀, ∀ U, J U₀ ≤ J U := by
  have hb : BddAbove (Set.range fun U => (J U).toAddSubgroup.index) := ⟨C, by
    rintro _ ⟨U, rfl⟩; exact (h U).2⟩
  obtain ⟨U₀, hU₀⟩ := Nat.sSup_mem (Set.range_nonempty _) hb
  refine ⟨U₀, fun U => le_trans ?_ (hJ (inf_le_right : U₀ ⊓ U ≤ U))⟩
  have hle : (J (U₀ ⊓ U)).toAddSubgroup ≤ (J U₀).toAddSubgroup := fun x hx => hJ inf_le_left hx
  have h1 := AddSubgroup.relIndex_mul_index hle
  have h2 : (J (U₀ ⊓ U)).toAddSubgroup.index ≤ (J U₀).toAddSubgroup.index := by
    simp only at hU₀
    rw [hU₀]; exact le_csSup hb ⟨_, rfl⟩
  have h3 := (h (U₀ ⊓ U)).1
  have h4 := (h U₀).1
  have h5 : (J (U₀ ⊓ U)).toAddSubgroup.relIndex (J U₀).toAddSubgroup = 1 := by
    generalize (J (U₀ ⊓ U)).toAddSubgroup.relIndex (J U₀).toAddSubgroup = r at h1
    generalize (J (U₀ ⊓ U)).toAddSubgroup.index = a at *
    generalize (J U₀).toAddSubgroup.index = b at *
    subst h1
    have : r ≠ 0 := by rintro rfl; simp at h3
    have : r * b ≤ 1 * b := by simpa using h2
    have := Nat.le_of_mul_le_mul_right this (Nat.pos_of_ne_zero h4)
    omega
  exact fun x hx => AddSubgroup.relIndex_eq_one.1 h5 hx

private theorem UpperTheory.V.CA.fl_approx {B M σ : Type} [CommRing B] [AddCommGroup M] [Module B M] [Fintype σ]
    (I : Ideal B) [IsPrecomplete I B] (v : σ → M) (L : ℕ → Submodule B M) (hL : Antitone L)
    (hI : ∀ n, I ^ n • ⊤ ≤ L n) (hs : ∀ n, L n ≤ L (n + 1) ⊔ I ^ n • ⊤)
    (h : ∀ n, Submodule.span B (Set.range v) ⊔ L n = ⊤) (N : ℕ) (x : M) (hx : x ∈ L N) :
    ∃ a : σ → B, (∀ i, a i ∈ I ^ N) ∧ ∀ n, x - ∑ i, a i • v i ∈ L n := by
  classical
  have step : ∀ (n : ℕ) (y : M), ∃ a : σ → B, (∀ i, a i ∈ I ^ n) ∧
      (y ∈ L n → y - ∑ i, a i • v i ∈ L (n + 1)) ∧ (y ∈ L (n + 1) → a = 0) := by
    intro n y
    by_cases h1 : y ∈ L (n + 1)
    · exact ⟨0, fun i => zero_mem _, fun _ => by simpa using h1, fun _ => rfl⟩
    by_cases h2 : y ∈ L n
    swap
    · exact ⟨0, fun i => zero_mem _, fun h => (h2 h).elim, fun _ => rfl⟩
    have h3 : L n ≤ L (n + 1) ⊔ I ^ n • Submodule.span B (Set.range v) := by
      refine (hs n).trans (sup_le le_sup_left ?_)
      rw [← h (n + 1), Submodule.smul_sup]
      exact sup_le le_sup_right (Submodule.smul_le_right.trans le_sup_left)
    obtain ⟨p, hp, z, hz, rfl⟩ := Submodule.mem_sup.1 (h3 h2)
    obtain ⟨a, ha, rfl⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum _ v z).1 hz
    refine ⟨a, ha, fun _ => ?_, fun h => (h1 h).elim⟩
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simpa using hp
  choose g hg1 hg2 hg3 using step
  let f : ℕ → σ → B := fun n => Nat.rec 0 (fun n a => a + g n (x - ∑ i, a i • v i)) n
  have f0 : f 0 = 0 := rfl
  have fs : ∀ n, f (n + 1) = f n + g n (x - ∑ i, f n i • v i) := fun n => rfl
  have h0 : L 0 = ⊤ := by simpa using hI 0
  have hf : ∀ n, x - ∑ i, f n i • v i ∈ L n := by
    intro n
    induction n with
    | zero => rw [h0]; trivial
    | succ n ih =>
      have := hg2 n _ ih
      rw [fs]
      simpa only [Pi.add_apply, add_smul, Finset.sum_add_distrib, sub_sub] using this
  have hz : ∀ n, n ≤ N → f n = 0 := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [fs, ih (by omega), hg3 n _ (by simpa using hL hn hx), add_zero]
  have hc : ∀ i, ∃ a : B, ∀ n, f n i - a ∈ I ^ n := by
    intro i
    obtain ⟨a, ha⟩ := IsPrecomplete.prec (I := I) (M := B) inferInstance (f := fun n => f n i) (by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        rw [fs, Pi.add_apply, ← sub_sub]
        exact sub_mem ih (Ideal.pow_le_pow_right hmn (hg1 n _ i)))
    refine ⟨a, fun n => ?_⟩
    have := ha n
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  choose a ha using hc
  refine ⟨a, fun i => ?_, fun n => ?_⟩
  · have := ha i N
    rw [hz N le_rfl] at this
    simpa using this
  · have : ∑ i, (f n i - a i) • v i ∈ L n :=
      Submodule.sum_mem _ fun i _ => hI n (Submodule.smul_mem_smul (ha i n) Submodule.mem_top)
    have := add_mem (hf n) this
    simpa only [sub_smul, Finset.sum_sub_distrib, sub_add_sub_cancel] using this

private theorem UpperTheory.V.CA.fl_abs {B M ι G : Type} [CommRing B] [AddCommGroup M] [Module B M] [SemilatticeInf ι]
    [Nonempty ι] (I : Ideal B) [IsPrecomplete I B] (hfin : ∀ n, Finite (B ⧸ I ^ n)) (K : ι → Submodule B M)
    (hK : Monotone K) (v : G → M) (c : ℕ)
    (h : ∀ U, ∃ s : Finset G, s.card ≤ c ∧ Submodule.span B (v '' (s : Set G)) ⊔ (K U ⊔ I ^ 1 • ⊤) = ⊤) :
    ∃ s : Finset G, s.card ≤ c ∧
      (∀ y, ∃ z ∈ Submodule.span B (v '' (s : Set G)), ∀ n U, y - z ∈ K U ⊔ I ^ n • ⊤) ∧
      ∀ N : ℕ, ∃ U₀, ∀ y ∈ K U₀, ∃ z ∈ I ^ N • (⊤ : Submodule B M), ∀ n U, y - z ∈ K U ⊔ I ^ n • ⊤ := by
  classical
  have hr : ∀ s : Finset G, v '' (s : Set G) = Set.range fun i : s => v i := fun s => Set.image_eq_range _ _
  have hst : ∀ n : ℕ, ∃ U₀, ∀ U, K U₀ ⊔ I ^ n • ⊤ ≤ K U ⊔ I ^ n • ⊤ := by
    intro n
    have := hfin n
    refine fl_stab (fun U => K U ⊔ I ^ n • ⊤) (fun U V hUV => sup_le_sup_right (hK hUV) _)
      (Nat.card (B ⧸ I ^ n) ^ c) fun U => ?_
    obtain ⟨s, hs, h1⟩ := h U
    rw [← sup_assoc] at h1
    have h2 := fl_nak I _ h1 n
    rw [sup_assoc, hr] at h2
    obtain ⟨h3, h4⟩ := fl_card (I ^ n) _ _ le_sup_right h2
    refine ⟨h3, h4.trans (Nat.pow_le_pow_right Nat.card_pos (by simpa using hs))⟩
  choose U hU using hst
  obtain ⟨s, hs, h1⟩ := h (U 1)
  let L : ℕ → Submodule B M := fun n => K (U n) ⊔ I ^ n • ⊤
  have hpow : ∀ {m n : ℕ}, m ≤ n → I ^ n • (⊤ : Submodule B M) ≤ I ^ m • ⊤ := fun hmn =>
    Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)
  have hL : Antitone L := fun m n hmn =>
    (hU n (U m)).trans (sup_le_sup_left (hpow hmn) _)
  have hstep : ∀ n, L n ≤ L (n + 1) ⊔ I ^ n • ⊤ := fun n =>
    (hU n (U (n + 1))).trans (sup_le_sup_right le_sup_left _)
  have hsp : ∀ n, Submodule.span B (Set.range fun i : s => v i) ⊔ L n = ⊤ := by
    intro n
    have h2 : Submodule.span B (v '' (s : Set G)) ⊔ (K (U n) ⊔ I ^ 1 • ⊤) = ⊤ :=
      top_le_iff.1 (h1.ge.trans (sup_le_sup_left (hU 1 (U n)) _))
    rw [← sup_assoc] at h2
    have h3 := fl_nak I _ h2 n
    rwa [sup_assoc, hr] at h3
  have key := fl_approx I (fun i : s => v i) L hL (fun n => le_sup_right) hstep hsp
  refine ⟨s, hs, fun y => ?_, fun N => ⟨U N, fun y hy => ?_⟩⟩
  · obtain ⟨a, -, ha⟩ := key 0 y (Submodule.mem_sup_right (by simp))
    refine ⟨_, ?_, fun n V => hU n V (ha n)⟩
    rw [hr]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · obtain ⟨a, ha', ha⟩ := key N y (Submodule.mem_sup_left hy)
    exact ⟨_, Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (ha' i) Submodule.mem_top,
      fun n V => hU n V (ha n)⟩

private theorem UpperTheory.V.CA.fl_mem {B G : Type} [CommRing B] [Group G] (S T : Set (MonoidAlgebra B G)) (I : Ideal B)
    (x : MonoidAlgebra B G) :
    x ∈ TwoSidedIdeal.span (S ∪ {z | ∃ a ∈ I, z = MonoidAlgebra.single 1 a} ∪ T) ↔
      x ∈ (TwoSidedIdeal.span (S ∪ T)).asIdeal.restrictScalars B ⊔ I • ⊤ := by
  have hl : ∀ (a z : MonoidAlgebra B G), z ∈ I • (⊤ : Submodule B (MonoidAlgebra B G)) →
      a * z ∈ I • (⊤ : Submodule B (MonoidAlgebra B G)) ∧ z * a ∈ I • (⊤ : Submodule B (MonoidAlgebra B G)) := by
    intro a z hz
    refine Submodule.smul_induction_on hz (fun r hr n _ => ?_) (fun x y hx hy => ?_)
    · rw [mul_smul_comm, smul_mul_assoc]
      exact ⟨Submodule.smul_mem_smul hr trivial, Submodule.smul_mem_smul hr trivial⟩
    · rw [mul_add, add_mul]
      exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
  have hm : ∀ z, z ∈ (TwoSidedIdeal.span (S ∪ T)).asIdeal.restrictScalars B ↔ z ∈ TwoSidedIdeal.span (S ∪ T) :=
    fun z => Iff.rfl
  constructor
  · intro hx
    induction hx using TwoSidedIdeal.span_induction with
    | mem x hx =>
      rcases hx with (hx | ⟨a, ha, rfl⟩) | hx
      · exact Submodule.mem_sup_left ((hm _).2 (TwoSidedIdeal.subset_span (Or.inl hx)))
      · refine Submodule.mem_sup_right ?_
        have := Submodule.smul_mem_smul ha (Submodule.mem_top (x := MonoidAlgebra.single (1 : G) (1 : B)))
        simpa using this
      · exact Submodule.mem_sup_left ((hm _).2 (TwoSidedIdeal.subset_span (Or.inr hx)))
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
    | left_absorb a x _ hx =>
      obtain ⟨p, hp, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
      rw [mul_add]
      exact Submodule.add_mem_sup ((hm _).2 (TwoSidedIdeal.mul_mem_left _ _ _ ((hm _).1 hp))) (hl a z hz).1
    | right_absorb a x _ hx =>
      obtain ⟨p, hp, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
      rw [add_mul]
      exact Submodule.add_mem_sup ((hm _).2 (TwoSidedIdeal.mul_mem_right _ _ _ ((hm _).1 hp))) (hl a z hz).2
  · intro hx
    obtain ⟨p, hp, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    refine add_mem (TwoSidedIdeal.span_mono (Set.union_subset_union_left _ Set.subset_union_left) ((hm _).1 hp)) ?_
    refine Submodule.smul_induction_on hz (fun r hr n _ => ?_) (fun x y hx hy => add_mem hx hy)
    have e : r • n = MonoidAlgebra.single 1 r * n := by
      rw [Algebra.smul_def]; rfl
    rw [e]
    exact TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.subset_span (Or.inl (Or.inr ⟨r, hr, rfl⟩)))

theorem UpperTheory.V.CA.f_limit :
    ∀ {B G : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Finite (ResidueField B)] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (S : Set (MonoidAlgebra B G)) (c : ℕ), (∀ U : OpenNormalSubgroup G, ∃ s : Finset G, s.card ≤ c ∧ ∀ y : MonoidAlgebra B G, ∃ z ∈ Submodule.span B ((fun g => MonoidAlgebra.single g (1 : B)) '' (s : Set G)), y - z ∈ TwoSidedIdeal.span (S ∪ {z | ∃ a ∈ maximalIdeal B ^ 1, z = MonoidAlgebra.single 1 a} ∪ {z | ∃ u ∈ U, z = MonoidAlgebra.single u 1 - 1})) → ∃ s : Finset G, s.card ≤ c ∧ (∀ y : MonoidAlgebra B G, ∃ z ∈ Submodule.span B ((fun g => MonoidAlgebra.single g (1 : B)) '' (s : Set G)), y - z ∈ closureIdeal (maximalIdeal B) S) ∧ ∀ N : ℕ, ∃ U : OpenNormalSubgroup G, ∀ u ∈ U, ∃ z ∈ (maximalIdeal B ^ N) • (⊤ : Submodule B (MonoidAlgebra B G)), MonoidAlgebra.single u 1 - 1 - z ∈ closureIdeal (maximalIdeal B) S := by
  intro B G _ _ _ _ _ _ _ _ _ _ S c h
  have hfin : ∀ n, Finite (B ⧸ maximalIdeal B ^ n) := fun n =>
    haveI : Finite (B ⧸ maximalIdeal B) := ‹Finite (ResidueField B)›
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  have : Nonempty (OpenNormalSubgroup G) := ⟨⟨⊤, Subgroup.normal_top⟩⟩
  obtain ⟨s, hs, h1, h2⟩ := fl_abs (maximalIdeal B) hfin
    (fun U : OpenNormalSubgroup G => (TwoSidedIdeal.span
      (S ∪ {z | ∃ u ∈ U, z = MonoidAlgebra.single u 1 - 1})).asIdeal.restrictScalars B)
    (fun U V hUV x hx => TwoSidedIdeal.span_mono (Set.union_subset_union_right _ (by
      rintro _ ⟨u, hu, rfl⟩; exact ⟨u, hUV hu, rfl⟩)) hx)
    (fun g => MonoidAlgebra.single g (1 : B)) c (fun U => by
      obtain ⟨s, hs, hy⟩ := h U
      refine ⟨s, hs, top_le_iff.1 fun y _ => ?_⟩
      obtain ⟨z, hz, hyz⟩ := hy y
      have := Submodule.add_mem_sup hz ((fl_mem _ _ _ _).1 hyz)
      simpa using this)
  have hcl : ∀ x : MonoidAlgebra B G, (∀ (n : ℕ) (U : OpenNormalSubgroup G), x ∈ (TwoSidedIdeal.span
      (S ∪ {z | ∃ u ∈ U, z = MonoidAlgebra.single u 1 - 1})).asIdeal.restrictScalars B ⊔ maximalIdeal B ^ n • ⊤) →
      x ∈ closureIdeal (maximalIdeal B) S := by
    intro x hx
    simp only [closureIdeal, TwoSidedIdeal.mem_iInf]
    exact fun n U => (fl_mem _ _ _ _).2 (hx n U)
  refine ⟨s, hs, fun y => ?_, fun N => ?_⟩
  · obtain ⟨z, hz, hyz⟩ := h1 y
    exact ⟨z, hz, hcl _ hyz⟩
  · obtain ⟨U, hU⟩ := h2 N
    refine ⟨U, fun u hu => ?_⟩
    obtain ⟨z, hz, hyz⟩ := hU (MonoidAlgebra.single u 1 - 1) (TwoSidedIdeal.subset_span (Or.inr ⟨u, hu, rfl⟩))
    exact ⟨z, hz, hcl _ hyz⟩
