import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

namespace Hint

theorem relIndex_ne_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H K : Subgroup G}
    (hH : IsOpen (H : Set G)) (hK : IsCompact (K : Set G)) : H.relIndex K ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let U : OpenSubgroup K := ⟨H.subgroupOf K, hH.preimage continuous_subtype_val⟩
  have : Finite (K ⧸ (U : Subgroup K)) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
  exact Subgroup.index_ne_zero_of_finite

theorem mem_rStab {H : Type} [Group H] {u : H → ℂ} {k : H} (h : ∀ x, u (x * k) = u x) : k ∈ rStab u := h

theorem rStab_apply {H : Type} [Group H] {u : H → ℂ} {k : H} (h : k ∈ rStab u) (x : H) : u (x * k) = u x := h x

theorem ind_mul {H : Type} [Group H] (K : Subgroup H) {k : H} (hk : k ∈ K) (x : H) :
    (K : Set H).indicator (1 : H → ℂ) (x * k) = (K : Set H).indicator 1 x := by
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem (show x * k ∈ (K : Set H) from K.mul_mem hx hk),
      Set.indicator_of_mem (show x ∈ (K : Set H) from hx)]
    rfl
  · rw [Set.indicator_of_notMem (show x * k ∉ (K : Set H) from fun h => hx ((K.mul_mem_cancel_right hk).1 h)),
      Set.indicator_of_notMem (show x ∉ (K : Set H) from hx)]

theorem out_mem {H : Type} [Group H] (K : Subgroup H) (q : H ⧸ K) : q.out ∈ K ↔ q = ((1 : H) : H ⧸ K) := by
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rw [QuotientGroup.eq, mul_one, inv_mem_iff]

theorem hint_ind {H : Type} [Group H] (K : Subgroup H) : hint K ((K : Set H).indicator 1) = 1 := by
  have hle : K ≤ rStab ((K : Set H).indicator (1 : H → ℂ)) := fun k hk => mem_rStab (ind_mul K hk)
  rw [hint, inf_eq_right.2 hle, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_mul,
    finsum_eq_single _ ((1 : H) : H ⧸ K)]
  · exact Set.indicator_of_mem (show _ ∈ (K : Set H) from (out_mem K _).2 rfl) _
  · intro q hq
    exact Set.indicator_of_notMem (show q.out ∉ (K : Set H) from fun h => hq ((out_mem K q).1 h)) _

theorem idx_eq {H : Type} [Group H] (K L : Subgroup H) (hLK : L ≤ K) (hidx : L.relIndex K ≠ 0) :
    ∑ᶠ q : H ⧸ L, (K : Set H).indicator (1 : H → ℂ) q.out = ((L.relIndex K : ℕ) : ℂ) := by
  have h := GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K L _ hLK (fun k hk => mem_rStab (ind_mul K (hLK hk))) hidx
  rw [hint_ind] at h
  have hc : ((L.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hidx
  rw [eq_inv_mul_iff_mul_eq₀ hc, mul_one] at h
  exact h.symm

theorem coset_mem {G : Type} [Group G] (W : Subgroup G) (q : G ⧸ W) (y : G) :
    y ∈ (fun y => q.out⁻¹ * y) ⁻¹' (W : Set G) ↔ (y : G ⧸ W) = q := by
  show q.out⁻¹ * y ∈ W ↔ _
  rw [← QuotientGroup.eq, QuotientGroup.out_eq', eq_comm]

theorem fin_supp {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (W : Subgroup G)
    (hW : IsOpen (W : Set G)) (g : G → ℂ) (hg : HasCompactSupport g) :
    (Function.support fun q : G ⧸ W => g q.out).Finite := by
  obtain ⟨t, ht⟩ := hg.isCompact.elim_finite_subcover
    (fun q : G ⧸ W => (fun y => q.out⁻¹ * y) ⁻¹' (W : Set G))
    (fun q => hW.preimage (continuous_const_mul _))
    (fun y _ => Set.mem_iUnion.2 ⟨(y : G ⧸ W), (coset_mem W _ y).2 rfl⟩)
  refine t.finite_toSet.subset fun q hq => ?_
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport g hq))
  have h := (coset_mem W i _).1 hyi
  rw [QuotientGroup.out_eq'] at h
  rw [h]
  exact hi

theorem int_cosets {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [MeasurableSpace Γ]
    [BorelSpace Γ] (ν : Measure Γ) [ν.IsMulLeftInvariant] (V : Subgroup Γ) (hV : IsOpen (V : Set Γ))
    (hVf : ν V ≠ ⊤) (g : Γ → ℂ) (hg : HasCompactSupport g) (hr : ∀ v ∈ V, ∀ x, g (x * v) = g x) :
    ∫ x, g x ∂ν = (ν.real V : ℂ) * ∑ᶠ q : Γ ⧸ V, g q.out := by
  set C : Γ ⧸ V → Set Γ := fun q => (fun y => q.out⁻¹ * y) ⁻¹' (V : Set Γ)
  have hCm : ∀ q, MeasurableSet (C q) := fun q => (hV.preimage (continuous_const_mul _)).measurableSet
  have hCν : ∀ q, ν (C q) = ν V := fun q => measure_preimage_mul ν _ _
  have hval : ∀ x, g x = g (x : Γ ⧸ V).out := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul V x
    rw [hh, hr _ h.2 x]
  have hfin := fin_supp V hV g hg
  have hpt : ∀ x, g x = ∑ q ∈ hfin.toFinset, (C q).indicator (fun _ => g q.out) x := by
    intro x
    rw [Finset.sum_eq_single (x : Γ ⧸ V)]
    · rw [Set.indicator_of_mem ((coset_mem V _ x).2 rfl)]
      exact hval x
    · intro q _ hq
      exact Set.indicator_of_notMem (fun hm => hq ((coset_mem V q x).1 hm).symm) _
    · intro hx
      rw [Set.indicator_of_mem ((coset_mem V _ x).2 rfl)]
      by_contra h
      exact hx (hfin.mem_toFinset.2 h)
  calc ∫ x, g x ∂ν = ∫ x, ∑ q ∈ hfin.toFinset, (C q).indicator (fun _ => g q.out) x ∂ν := by
        congr 1
        funext x
        exact hpt x
    _ = ∑ q ∈ hfin.toFinset, ∫ x, (C q).indicator (fun _ => g q.out) x ∂ν :=
        integral_finsetSum _ fun q _ =>
          (integrable_indicator_iff (hCm q)).2 (integrableOn_const (by rw [hCν q]; exact hVf))
    _ = ∑ q ∈ hfin.toFinset, (ν.real V : ℂ) * g q.out := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [integral_indicator_const _ (hCm q), Complex.real_smul]
        simp only [measureReal_def, hCν q]
    _ = (ν.real V : ℂ) * ∑ᶠ q : Γ ⧸ V, g q.out := by
        rw [← Finset.mul_sum, finsum_eq_sum_of_support_subset _ hfin.coe_toFinset.ge]

end Hint

theorem intHint : IntHint := by
  intro Γ _ _ _ _ _ ν _ K U f hKo hKc hUo hf hfU _
  have hVo : IsOpen ((U ⊓ K : Subgroup Γ) : Set Γ) := hUo.inter hKo
  have hVK : U ⊓ K ≤ K := inf_le_right
  have hidx : (U ⊓ K).relIndex K ≠ 0 := Hint.relIndex_ne_zero hVo hKc
  have hKf : ν K ≠ ⊤ := hKc.measure_lt_top.ne
  have hVf : ν (U ⊓ K : Subgroup Γ) ≠ ⊤ := ne_top_of_le_ne_top hKf (measure_mono hVK)
  have h1 := Hint.int_cosets ν (U ⊓ K) hVo hVf f hf fun v hv => hfU v (Subgroup.mem_inf.1 hv).1
  have h2 := Hint.int_cosets ν (U ⊓ K) hVo hVf ((K : Set Γ).indicator 1)
    (HasCompactSupport.intro hKc fun x hx => Set.indicator_of_notMem hx _)
    fun v hv => Hint.ind_mul K (Subgroup.mem_inf.1 hv).2
  have h3 : ∫ x, (K : Set Γ).indicator (1 : Γ → ℂ) x ∂ν = (ν.real K : ℂ) := by
    rw [show (1 : Γ → ℂ) = fun _ => (1 : ℂ) from rfl, integral_indicator_const _ hKo.measurableSet,
      Complex.real_smul, mul_one]
  rw [h3, Hint.idx_eq K (U ⊓ K) hVK hidx] at h2
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level Γ K (U ⊓ K) f hVK
    (fun k hk => Hint.mem_rStab fun x => hfU k (Subgroup.mem_inf.1 hk).1 x) hidx, h1, h2]
  have hc : (((U ⊓ K).relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hidx
  rw [mul_assoc, ← mul_assoc (((U ⊓ K).relIndex K : ℕ) : ℂ), mul_inv_cancel₀ hc, one_mul]

namespace Hint

theorem finsum_prod {κ : Type} [Fintype κ] {A : κ → Type} (g : ∀ k, A k → ℂ)
    (hs : ∀ k, (Function.support (g k)).Finite) :
    ∑ᶠ c : (∀ k, A k), ∏ k, g k (c k) = ∏ k, ∑ᶠ x, g k x := by
  have e : ∀ k, ∑ᶠ x, g k x = ∑ x ∈ (hs k).toFinset, g k x := fun k =>
    finsum_eq_sum_of_support_subset (g k) (hs k).coe_toFinset.ge
  simp only [e]
  rw [Finset.prod_univ_sum]
  refine finsum_eq_sum_of_support_subset _ fun c hc => ?_
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro k
  rw [Set.Finite.mem_toFinset]
  exact Function.mem_support.2 fun h0 =>
    (Function.mem_support.1 hc) (Finset.prod_eq_zero (Finset.mem_univ k) h0)

theorem count {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] (p : ∀ i, Γ →* Hl i)
    (KH W : ∀ i, Subgroup (Hl i)) (T : Finset ι) (h : ∀ i, Hl i → ℂ)
    (hsurj : ∀ y : ∀ i, Hl i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : Γ, ∀ i, p i x = y i)
    (hfin : ∀ x : Γ, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hW : ∀ i ∉ T, W i = KH i) (hWs : ∀ i, W i ≤ rStab (h i))
    (hT : ∀ i ∉ T, h i = (KH i : Set (Hl i)).indicator 1)
    (hs : ∀ i, (Function.support fun c : Hl i ⧸ W i => h i c.out).Finite) :
    ∑ᶠ q : Γ ⧸ (⨅ i, (W i).comap (p i)), ∏ᶠ i, h i (p i q.out) =
      ∏ i ∈ T, ∑ᶠ c : Hl i ⧸ W i, h i c.out := by
  set V : Subgroup Γ := ⨅ i, (W i).comap (p i) with hV
  have hmemV : ∀ x, x ∈ V ↔ ∀ i, p i x ∈ W i := fun x => by
    rw [hV, Subgroup.mem_iInf]
    rfl
  set F : Γ → ℂ := fun x => ∏ᶠ i, h i (p i x) with hF
  have hFV : ∀ x, ∀ v ∈ V, F (x * v) = F x := by
    intro x v hv
    simp only [hF, map_mul]
    exact finprod_congr fun i => rStab_apply (hWs i ((hmemV v).1 hv i)) (p i x)
  have hFout : ∀ x : Γ, F ((x : Γ ⧸ V).out) = F x := by
    intro x
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V x
    rw [hv, hFV x v v.2]
  let y : (∀ i : T, Hl i ⧸ W i) → ∀ i, Hl i := fun c i => if hi : i ∈ T then (c ⟨i, hi⟩).out else 1
  have hy_out : ∀ c (i : T), y c i = (c i).out := fun c i => dif_pos i.2
  have hy_one : ∀ c i, i ∉ T → y c i = 1 := fun c i hi => dif_neg hi
  have hy : ∀ c, ∀ᶠ i in cofinite, y c i ∈ KH i := fun c =>
    Filter.eventually_cofinite.2 (T.finite_toSet.subset fun i hi => by
      by_contra hiT
      exact hi (by rw [hy_one c i hiT]; exact (KH i).one_mem))
  choose X hX using fun c => hsurj (y c) (hy c)
  let Φ : (∀ i : T, Hl i ⧸ W i) → Γ ⧸ V := fun c => (X c : Γ ⧸ V)
  have hΦinj : Function.Injective Φ := by
    intro c c' hcc
    have h1 : (X c)⁻¹ * X c' ∈ V := QuotientGroup.eq.1 hcc
    funext i
    have h2 := (hmemV _).1 h1 i.1
    rw [map_mul, map_inv, hX, hX, hy_out c i, hy_out c' i] at h2
    have h3 : (((c i).out : Hl i.1) : Hl i.1 ⧸ W i.1) = (c' i).out := QuotientGroup.eq.2 h2
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h3
    exact h3
  have hmulS : ∀ x : Γ, (Function.mulSupport fun j => h j (p j x)).Finite := by
    intro x
    refine (T.finite_toSet.union (Filter.eventually_cofinite.1 (hfin x))).subset fun j hj => ?_
    by_contra hn
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq, not_or, not_not] at hn
    exact (Function.mem_mulSupport.1 hj) (by
      show h j (p j x) = 1
      rw [hT j hn.1]
      exact Set.indicator_of_mem hn.2 _)
  have hsupp : ∀ q : Γ ⧸ V, F q.out ≠ 0 → q ∈ Set.range Φ := by
    intro q hq
    have hK : ∀ i ∉ T, p i q.out ∈ KH i := by
      intro i hi
      by_contra hn
      apply hq
      show (∏ᶠ j, h j (p j q.out)) = 0
      exact finprod_eq_zero _ i (by
        show h i (p i q.out) = 0
        rw [hT i hi]
        exact Set.indicator_of_notMem hn _) (hmulS _)
    refine ⟨fun i => (p i.1 q.out : Hl i.1 ⧸ W i.1), ?_⟩
    show (X _ : Γ ⧸ V) = q
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    refine QuotientGroup.eq.2 ((hmemV _).2 fun i => ?_)
    rw [map_mul, map_inv, hX]
    by_cases hi : i ∈ T
    · simp only [y, dif_pos hi]
      exact QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    · simp only [y, dif_neg hi, inv_one, one_mul]
      rw [hW i hi]
      exact hK i hi
  have hval : ∀ c, F (Φ c).out = ∏ i : T, h i (c i).out := by
    intro c
    show F (X c : Γ ⧸ V).out = _
    rw [hFout]
    show (∏ᶠ i, h i (p i (X c))) = _
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) ?_, ← Finset.prod_coe_sort T]
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [hX, hy_out c i]
    · intro j hj
      by_contra hn
      exact (Function.mem_mulSupport.1 hj) (by
        show h j (p j (X c)) = 1
        rw [hX, hy_one c j hn, hT j hn]
        exact Set.indicator_of_mem (KH j).one_mem _)
  calc ∑ᶠ q : Γ ⧸ V, ∏ᶠ i, h i (p i q.out) = ∑ᶠ q : Γ ⧸ V, F q.out := rfl
    _ = ∑ᶠ q ∈ Set.range Φ, F q.out := by
        rw [← finsum_mem_univ]
        exact finsum_mem_inter_support_eq _ _ _
          (Set.ext fun q => ⟨fun hq => ⟨hsupp q hq.2, hq.2⟩, fun hq => ⟨Set.mem_univ _, hq.2⟩⟩)
    _ = ∑ᶠ c, F (Φ c).out := finsum_mem_range hΦinj
    _ = ∑ᶠ c, ∏ i : T, h i (c i).out := finsum_congr hval
    _ = ∏ i : T, ∑ᶠ x : Hl i ⧸ W i, h i x.out :=
        finsum_prod (fun (i : T) (x : Hl i ⧸ W i) => h i x.out) fun i => hs i
    _ = ∏ i ∈ T, ∑ᶠ c : Hl i ⧸ W i, h i c.out := Finset.prod_coe_sort T fun i => ∑ᶠ c : Hl i ⧸ W i, h i c.out

end Hint

theorem hintProd : HintProd := by
  intro ι Γ _ Hl _ _ _ p K KH U f hinj hsurj hfin hK hloc hcof
  have hTf : {i | ¬ f i = (KH i : Set (Hl i)).indicator 1}.Finite := Filter.eventually_cofinite.1 hcof
  set T := hTf.toFinset
  have hT : ∀ i ∉ T, f i = (KH i : Set (Hl i)).indicator 1 := fun i hi => by
    by_contra hn
    exact hi (hTf.mem_toFinset.2 hn)
  let W : ∀ i, Subgroup (Hl i) := fun i => KH i ⊓ rStab (f i)
  have hWo : ∀ i, IsOpen (W i : Set (Hl i)) := fun i =>
    (hloc i).2.1.inter (Subgroup.isOpen_mono (fun u hu => Hint.mem_rStab ((hloc i).2.2.2.2 u hu))
      (hloc i).2.2.1)
  have hWK : ∀ i, W i ≤ KH i := fun i => inf_le_left
  have hWs : ∀ i, W i ≤ rStab (f i) := fun i => inf_le_right
  have hW : ∀ i ∉ T, W i = KH i := fun i hi => inf_eq_left.2 (by
    rw [hT i hi]
    exact fun k hk => Hint.mem_rStab (Hint.ind_mul (KH i) hk))
  have hidxi : ∀ i, (W i).relIndex (KH i) ≠ 0 := fun i => Hint.relIndex_ne_zero (hWo i) (hloc i).1
  set V : Subgroup Γ := ⨅ i, (W i).comap (p i) with hV
  have hmemV : ∀ x, x ∈ V ↔ ∀ i, p i x ∈ W i := fun x => by
    rw [hV, Subgroup.mem_iInf]
    rfl
  have hVK : V ≤ K := fun x hx => (hK x).2 fun i => hWK i ((hmemV x).1 hx i)
  have hidx : V.relIndex K ≠ 0 := by
    have hle : (⨅ j : T, (W j).comap (p j)) ⊓ K ≤ V := by
      intro x hx
      rw [Subgroup.mem_inf, Subgroup.mem_iInf] at hx
      refine (hmemV x).2 fun i => ?_
      by_cases hi : i ∈ T
      · exact hx.1 ⟨i, hi⟩
      · rw [hW i hi]
        exact (hK x).1 hx.2 i
    intro h0
    have h1 := Subgroup.relIndex_eq_zero_of_le_left hle h0
    rw [Subgroup.inf_relIndex_right] at h1
    exact Subgroup.relIndex_iInf_ne_zero (fun j => by
      rw [Subgroup.relIndex_comap]
      exact fun h2 => hidxi j (Subgroup.relIndex_eq_zero_of_le_right
        (Subgroup.map_le_iff_le_comap.2 fun x hx => (hK x).1 hx j.1) h2)) h1
  have hrF : V ≤ rStab (fun x => ∏ᶠ i, f i (p i x)) := fun v hv => Hint.mem_rStab fun x => by
    simp only [map_mul]
    exact finprod_congr fun i => Hint.rStab_apply (hWs i ((hmemV v).1 hv i)) (p i x)
  have hfs : ∀ i, (Function.support fun c : Hl i ⧸ W i => f i c.out).Finite := fun i =>
    Hint.fin_supp (W i) (hWo i) (f i) (hloc i).2.2.2.1
  have his : ∀ i, (Function.support fun c : Hl i ⧸ W i =>
      (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) c.out).Finite := fun i =>
    Hint.fin_supp (W i) (hWo i) _ (HasCompactSupport.intro (hloc i).1 fun x hx => Set.indicator_of_notMem hx _)
  have c1 := Hint.count p KH W T f hsurj hfin hW hWs hT hfs
  have c2 := Hint.count p KH W T (fun i => (KH i : Set (Hl i)).indicator 1) hsurj hfin hW
    (fun i k hk => Hint.mem_rStab (Hint.ind_mul (KH i) (hWK i hk))) (fun i _ => rfl) his
  have hindK : ∀ x, ∏ᶠ i, (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) (p i x) =
      (K : Set Γ).indicator 1 x := by
    intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem (show x ∈ (K : Set Γ) from hx)]
      exact finprod_eq_one_of_forall_eq_one fun i => Set.indicator_of_mem ((hK x).1 hx i) _
    · rw [Set.indicator_of_notMem (show x ∉ (K : Set Γ) from hx)]
      obtain ⟨i, hi⟩ : ∃ i, p i x ∉ KH i := by
        by_contra hn
        push_neg at hn
        exact hx ((hK x).2 hn)
      refine finprod_eq_zero _ i (Set.indicator_of_notMem hi _) ?_
      refine (Filter.eventually_cofinite.1 (hfin x)).subset fun j hj => ?_
      show ¬ p j x ∈ KH j
      exact fun hj' => (Function.mem_mulSupport.1 hj) (Set.indicator_of_mem hj' _)
  have hcK : ((V.relIndex K : ℕ) : ℂ) = ∏ i ∈ T, (((W i).relIndex (KH i) : ℕ) : ℂ) := by
    rw [← Hint.idx_eq K V hVK hidx]
    calc ∑ᶠ q : Γ ⧸ V, (K : Set Γ).indicator (1 : Γ → ℂ) q.out
        = ∑ᶠ q : Γ ⧸ V, ∏ᶠ i, (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) (p i q.out) :=
          finsum_congr fun q => (hindK _).symm
      _ = ∏ i ∈ T, ∑ᶠ c : Hl i ⧸ W i, (KH i : Set (Hl i)).indicator (1 : Hl i → ℂ) c.out := c2
      _ = ∏ i ∈ T, (((W i).relIndex (KH i) : ℕ) : ℂ) :=
          Finset.prod_congr rfl fun i _ => Hint.idx_eq (KH i) (W i) (hWK i) (hidxi i)
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level Γ K V _ hVK hrF hidx]
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) ?_]
  · rw [Finset.prod_congr (rfl : T = T) fun i _ =>
      GlobalTheory.CompanionTheory.HintLevel.hint_eq_level (Hl i) (KH i) (W i) (f i) (hWK i) (hWs i) (hidxi i)]
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← hcK]
    congr 1
  · intro i hi
    by_contra hn
    exact (Function.mem_mulSupport.1 hi) (by
      show hint (KH i) (f i) = 1
      rw [hT i hn]
      exact Hint.hint_ind (KH i))

end PositivityTheory.Rg.BcB.F

end
