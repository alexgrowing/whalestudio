import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

namespace E1

section Gen

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

def cmp (F : GMod B R k) (h : DirectSum.IsInternal F.gr) (x : F.M) (m : Deg k) : F.M :=
  letI := h.chooseDecomposition
  (DirectSum.decompose F.gr x m : F.M)

theorem cmp_mem (F : GMod B R k) (h : DirectSum.IsInternal F.gr) (x : F.M) (m : Deg k) :
    cmp F h x m ∈ F.gr m := by
  let _ := h.chooseDecomposition
  exact (DirectSum.decompose F.gr x m).2

theorem cmp_of_mem (F : GMod B R k) (h : DirectSum.IsInternal F.gr) {x : F.M} {m : Deg k}
    (hx : x ∈ F.gr m) : cmp F h x m = x := by
  let _ := h.chooseDecomposition
  exact DirectSum.decompose_of_mem_same F.gr hx

theorem cmp_of_mem_ne (F : GMod B R k) (h : DirectSum.IsInternal F.gr) {x : F.M} {n m : Deg k}
    (hx : x ∈ F.gr n) (hn : n ≠ m) : cmp F h x m = 0 := by
  let _ := h.chooseDecomposition
  exact DirectSum.decompose_of_mem_ne F.gr hx hn

theorem cmp_zero (F : GMod B R k) (h : DirectSum.IsInternal F.gr) (m : Deg k) :
    cmp F h 0 m = 0 := by
  let _ := h.chooseDecomposition
  simp [cmp]

theorem cmp_add (F : GMod B R k) (h : DirectSum.IsInternal F.gr) (x y : F.M) (m : Deg k) :
    cmp F h (x + y) m = cmp F h x m + cmp F h y m := by
  let _ := h.chooseDecomposition
  simp [cmp]

theorem sum_cmp (F : GMod B R k) (h : DirectSum.IsInternal F.gr) (x : F.M) :
    ∃ S : Finset (Deg k), ∑ m ∈ S, cmp F h x m = x := by
  classical
  let _ := h.chooseDecomposition
  exact ⟨_, DirectSum.sum_support_decompose F.gr x⟩

theorem hom_cmp {G H : GMod B R k} (hG : DirectSum.IsInternal G.gr)
    (hH : DirectSum.IsInternal H.gr) (φ : G.M →ₗ[R] H.M)
    (hφ : ∀ m, ∀ x ∈ G.gr m, φ x ∈ H.gr m) (x : G.M) (m : Deg k) :
    cmp H hH (φ x) m = φ (cmp G hG x m) := by
  let _ := hG.chooseDecomposition
  induction x using DirectSum.Decomposition.inductionOn G.gr with
  | zero => rw [map_zero, cmp_zero, cmp_zero, map_zero]
  | @homogeneous n y =>
    by_cases hn : n = m
    · subst hn
      rw [cmp_of_mem _ _ y.2, cmp_of_mem _ _ (hφ _ _ y.2)]
    · rw [cmp_of_mem_ne _ _ y.2 hn, cmp_of_mem_ne _ _ (hφ _ _ y.2) hn, map_zero]
  | add a b ha hb => rw [map_add, cmp_add, cmp_add, map_add, ha, hb]

theorem isHomSub_of_cmp (F : GMod B R k) (h : DirectSum.IsInternal F.gr) (N : Submodule R F.M)
    (hN : ∀ x ∈ N, ∀ m, cmp F h x m ∈ N) : F.IsHomSub N := by
  apply le_antisymm
  · intro x hx
    obtain ⟨S, hS⟩ := sum_cmp F h x
    rw [← hS]
    exact Submodule.sum_mem _ (fun m _ => Submodule.subset_span ⟨hN x hx m, m, cmp_mem F h x m⟩)
  · exact Submodule.span_le.2 (fun x hx => hx.1)

theorem isHomSub_ker {G H : GMod B R k} (hG : DirectSum.IsInternal G.gr)
    (hH : DirectSum.IsInternal H.gr) (φ : G.M →ₗ[R] H.M)
    (hφ : ∀ m, ∀ x ∈ G.gr m, φ x ∈ H.gr m) : G.IsHomSub (LinearMap.ker φ) := by
  refine isHomSub_of_cmp G hG _ (fun x hx m => ?_)
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← hom_cmp hG hH φ hφ, hx, cmp_zero]

theorem isHomSub_range {G H : GMod B R k} (hG : DirectSum.IsInternal G.gr)
    (hH : DirectSum.IsInternal H.gr) (φ : G.M →ₗ[R] H.M)
    (hφ : ∀ m, ∀ x ∈ G.gr m, φ x ∈ H.gr m) : H.IsHomSub (LinearMap.range φ) := by
  refine isHomSub_of_cmp H hH _ ?_
  rintro _ ⟨x, rfl⟩ m
  exact ⟨cmp G hG x m, (hom_cmp hG hH φ hφ x m).symm⟩

def sesHom {G H : GMod B R k} (hG : DirectSum.IsInternal G.gr)
    (hH : DirectSum.IsInternal H.gr) (φ : G.M →ₗ[R] H.M)
    (hφ : ∀ m, ∀ x ∈ G.gr m, φ x ∈ H.gr m) :
    SES (G.sub (LinearMap.ker φ)) G (H.sub (LinearMap.range φ)) where
  f := (LinearMap.ker φ).subtype
  g := φ.rangeRestrict
  inj := Subtype.val_injective
  surj := φ.surjective_rangeRestrict
  exact := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, congrArg Subtype.val hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact Subtype.ext y.2
  f_gr := fun m => rfl
  g_gr := by
    intro m
    ext y
    obtain ⟨_, x, rfl⟩ := y
    constructor
    · intro hy
      have hy' : φ x ∈ H.gr m := hy
      refine ⟨cmp G hG x m, cmp_mem G hG x m, Subtype.ext ?_⟩
      show φ (cmp G hG x m) = φ x
      rw [← hom_cmp hG hH φ hφ, cmp_of_mem _ _ hy']
    · rintro ⟨z, hz, hzy⟩
      have h1 : φ z = φ x := congrArg Subtype.val hzy
      show φ x ∈ H.gr m
      rw [← h1]
      exact hφ m z hz

theorem chi_subsingleton (ts : List (Deg k × R)) :
    ∀ (F : GMod B R k), Subsingleton F.M → ∀ m, chi ts F m = 0 := by
  induction ts with
  | nil =>
    intro F hF m
    simp only [chi]
    rw [Module.length_eq_zero]
    rfl
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro F hF m
    simp only [chi]
    have h1 : Subsingleton (F.quot s).M :=
      inferInstanceAs (Subsingleton (F.M ⧸ LinearMap.range (LinearMap.lsmul R F.M s)))
    have h2 : Subsingleton (F.ann s d).M :=
      inferInstanceAs (Subsingleton (LinearMap.ker (LinearMap.lsmul R F.M s)))
    rw [ih _ h1, ih _ h2, sub_zero]

def topIso (H : GMod B R k) (N : Submodule R H.M) (hN : N = ⊤) : GIso (H.sub N) H where
  e := LinearEquiv.ofTop N hN
  map_gr m := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hN ▸ Submodule.mem_top⟩, hx, rfl⟩

end Gen

section Step

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

def annMap {G H : GMod B R k} (φ : G.M →ₗ[R] H.M) (s : R) (d : Deg k) :
    (G.ann s d).M →ₗ[R] (H.ann s d).M :=
  LinearMap.restrict φ (p := LinearMap.ker (LinearMap.lsmul R G.M s))
    (q := LinearMap.ker (LinearMap.lsmul R H.M s)) (by
      intro x hx
      have hx' : s • x = 0 := hx
      show s • φ x = 0
      rw [← map_smul, hx', map_zero])

def quotMap {G H : GMod B R k} (φ : G.M →ₗ[R] H.M) (s : R) :
    (G.quot s).M →ₗ[R] (H.quot s).M :=
  Submodule.mapQ (LinearMap.range (LinearMap.lsmul R G.M s))
    (LinearMap.range (LinearMap.lsmul R H.M s)) φ (by
      rintro _ ⟨x, rfl⟩
      exact ⟨φ x, (map_smul φ s x).symm⟩)

theorem annMap_gr {G H : GMod B R k} (φ : G.M →ₗ[R] H.M)
    (hφ : ∀ m, ∀ x ∈ G.gr m, φ x ∈ H.gr m) (s : R) (d : Deg k) :
    ∀ m, ∀ x ∈ (G.ann s d).gr m, annMap φ s d x ∈ (H.ann s d).gr m :=
  fun m x hx => hφ (m - d) x.1 hx

theorem quotMap_gr {G H : GMod B R k} (φ : G.M →ₗ[R] H.M)
    (hφ : ∀ m, ∀ x ∈ G.gr m, φ x ∈ H.gr m) (s : R) :
    ∀ m, ∀ x ∈ (G.quot s).gr m, quotMap φ s x ∈ (H.quot s).gr m := by
  rintro m _ ⟨x, hx, rfl⟩
  exact ⟨φ x, hφ m x hx, rfl⟩

variable {F' F F'' : GMod B R k} (S : SES F' F F'') (s : R) (d : Deg k)

theorem f_gr' : ∀ m, ∀ x ∈ F'.gr m, S.f x ∈ F.gr m := by
  intro m x hx
  rw [S.f_gr] at hx
  exact hx

theorem g_gr' : ∀ m, ∀ x ∈ F.gr m, S.g x ∈ F''.gr m := by
  intro m x hx
  rw [S.g_gr]
  exact ⟨x, hx, rfl⟩

def delta : (F''.ann s d).M →ₗ[R] (F'.quot s).M :=
  SnakeLemma.δ' (LinearMap.lsmul R F'.M s) (LinearMap.lsmul R F.M s) (LinearMap.lsmul R F''.M s)
    S.f S.g S.exact S.f S.g S.exact (by ext x; simp) (by ext x; simp)
    (LinearMap.ker (LinearMap.lsmul R F''.M s)).subtype (LinearMap.exact_subtype_ker_map _)
    (LinearMap.range (LinearMap.lsmul R F'.M s)).mkQ (LinearMap.exact_map_mkQ_range _)
    S.surj S.inj

theorem delta_eq (x : (F''.ann s d).M) (y : F.M) (hy : S.g y = x.1) (z : F'.M)
    (hz : S.f z = s • y) :
    delta S s d x = (LinearMap.range (LinearMap.lsmul R F'.M s)).mkQ z :=
  SnakeLemma.δ'_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x y hy z hz

theorem exact_ann_delta : Function.Exact (annMap S.g s d) (delta S s d) :=
  SnakeLemma.exact_δ'_right _ _ _ _ _ _ _ _ _ _ _
    (LinearMap.ker (LinearMap.lsmul R F.M s)).subtype (LinearMap.exact_subtype_ker_map _)
    _ _ _ _ _ _ (annMap S.g s d) (by ext x; rfl) Subtype.val_injective

theorem exact_delta_quot : Function.Exact (delta S s d) (quotMap S.f s) :=
  SnakeLemma.exact_δ'_left _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (LinearMap.range (LinearMap.lsmul R F.M s)).mkQ (LinearMap.exact_map_mkQ_range _)
    _ _ (quotMap S.f s) (by ext x; rfl) (Submodule.mkQ_surjective _)

theorem delta_gr (hs : ∀ m, ∀ x ∈ F.gr m, s • x ∈ F.gr (d + m)) :
    ∀ m, ∀ x ∈ (F''.ann s d).gr m, delta S s d x ∈ (F'.quot s).gr m := by
  intro m x hx
  have hx' : (x.1 : F''.M) ∈ F''.gr (m - d) := hx
  rw [S.g_gr] at hx'
  obtain ⟨y, hy, hyx⟩ := hx'
  have hyx' : S.g y = x.1 := hyx
  have h0 : S.g (s • y) = 0 := by
    rw [map_smul, hyx']
    exact x.2
  obtain ⟨z, hz⟩ := (S.exact _).1 h0
  rw [delta_eq S s d x y hyx' z hz]
  refine ⟨z, ?_, rfl⟩
  rw [S.f_gr]
  show S.f z ∈ F.gr m
  rw [hz]
  have := hs (m - d) y hy
  rwa [add_sub_cancel] at this

theorem annMap_f_inj : Function.Injective (annMap S.f s d) := by
  intro x y hxy
  exact Subtype.ext (S.inj (congrArg Subtype.val hxy))

theorem exact_ann : Function.Exact (annMap S.f s d) (annMap S.g s d) := by
  intro x
  constructor
  · intro hx
    have hx' : S.g x.1 = 0 := congrArg Subtype.val hx
    obtain ⟨y, hy⟩ := (S.exact _).1 hx'
    refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
    show s • y = 0
    apply S.inj
    rw [map_smul, hy, map_zero]
    exact x.2
  · rintro ⟨y, rfl⟩
    exact Subtype.ext ((S.exact _).2 ⟨y.1, rfl⟩)

theorem exact_quot : Function.Exact (quotMap S.f s) (quotMap S.g s) := by
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  constructor
  · intro hx
    have hx' : (LinearMap.range (LinearMap.lsmul R F''.M s)).mkQ (S.g x) = 0 := hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx'
    obtain ⟨w, hw⟩ := hx'
    obtain ⟨z, rfl⟩ := S.surj w
    have hw' : s • S.g z = S.g x := hw
    have h0 : S.g (x - s • z) = 0 := by rw [map_sub, map_smul, hw', sub_self]
    obtain ⟨y, hy⟩ := (S.exact _).1 h0
    refine ⟨(LinearMap.range (LinearMap.lsmul R F'.M s)).mkQ y, ?_⟩
    show (LinearMap.range (LinearMap.lsmul R F.M s)).mkQ (S.f y) = _
    rw [hy, map_sub, sub_eq_self, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨z, rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    rw [← hy]
    show (LinearMap.range (LinearMap.lsmul R F''.M s)).mkQ (S.g (S.f y)) = 0
    rw [(S.exact _).2 ⟨y, rfl⟩, map_zero]

theorem quotMap_g_surj : Function.Surjective (quotMap S.g s) := by
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨y, rfl⟩ := S.surj x
  exact ⟨(LinearMap.range (LinearMap.lsmul R F.M s)).mkQ y, rfl⟩

include S in
theorem ann_le_left : F.Ann ≤ F'.Ann := by
  intro a ha
  rw [GMod.Ann, Module.mem_annihilator] at ha ⊢
  intro x
  apply S.inj
  rw [map_smul, ha, map_zero]

include S in
theorem ann_le_right : F.Ann ≤ F''.Ann := by
  intro a ha
  rw [GMod.Ann, Module.mem_annihilator] at ha ⊢
  intro x
  obtain ⟨y, rfl⟩ := S.surj x
  rw [← map_smul, ha, map_zero]

theorem ann_le_ann (G : GMod B R k) : G.Ann ≤ (G.ann s d).Ann := by
  intro a ha
  rw [GMod.Ann, Module.mem_annihilator] at ha ⊢
  intro x
  exact Subtype.ext (ha x.1)

theorem mem_ann_ann (G : GMod B R k) : s ∈ (G.ann s d).Ann := by
  rw [GMod.Ann, Module.mem_annihilator]
  intro x
  exact Subtype.ext x.2

theorem ann_le_quot (G : GMod B R k) : G.Ann ≤ (G.quot s).Ann := by
  intro a ha
  rw [GMod.Ann, Module.mem_annihilator] at ha ⊢
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  show (a • (LinearMap.range (LinearMap.lsmul R G.M s)).mkQ y :
    G.M ⧸ LinearMap.range (LinearMap.lsmul R G.M s)) = 0
  rw [← map_smul, ha, map_zero]

theorem mem_ann_quot (G : GMod B R k) : s ∈ (G.quot s).Ann := by
  rw [GMod.Ann, Module.mem_annihilator]
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
  show (s • (LinearMap.range (LinearMap.lsmul R G.M s)).mkQ y :
    G.M ⧸ LinearMap.range (LinearMap.lsmul R G.M s)) = 0
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨y, rfl⟩

theorem adm_of_section_mem [IsLocalRing B] (𝒜 : Deg k → Submodule B R) {ts : List (Deg k × R)}
    {J J' : Ideal R} (h : admitted 𝒜 ((d, s) :: ts) J) (hJ : J ≤ J') (hs : s ∈ J') :
    admitted 𝒜 ts J' := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, hN.trans (sup_le (hJ.trans le_sup_left) ?_)⟩
  refine Ideal.span_le.2 ?_
  rintro t ⟨d', ht⟩
  rcases List.mem_cons.1 ht with h1 | h1
  · have h2 : t = s := (Prod.ext_iff.1 h1).2
    rw [h2]
    exact Ideal.mem_sup_left hs
  · exact Ideal.mem_sup_right (Ideal.subset_span ⟨d', h1⟩)

include S in

theorem length_add (m : Deg k) :
    Module.length B (F.gr m) = Module.length B (F'.gr m) + Module.length B (F''.gr m) := by
  refine Module.length_eq_add_of_exact
    (LinearMap.restrict (S.f.restrictScalars B) (p := F'.gr m) (q := F.gr m) (f_gr' S m))
    (LinearMap.restrict (S.g.restrictScalars B) (p := F.gr m) (q := F''.gr m) (g_gr' S m))
    ?_ ?_ ?_
  · intro x y hxy
    exact Subtype.ext (S.inj (congrArg Subtype.val hxy))
  · rintro ⟨x, hx⟩
    rw [S.g_gr] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  · intro x
    constructor
    · intro hx
      have hx' : S.g x.1 = 0 := congrArg Subtype.val hx
      obtain ⟨y, hy⟩ := (S.exact _).1 hx'
      refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
      rw [S.f_gr]
      show S.f y ∈ F.gr m
      rw [hy]
      exact x.2
    · rintro ⟨y, rfl⟩
      exact Subtype.ext ((S.exact _).2 ⟨y.1, rfl⟩)

theorem chi_sub_bot (ts : List (Deg k × R)) (G : GMod B R k) (N : Submodule R G.M) (hN : N = ⊥)
    (m : Deg k) : chi ts (G.sub N) m = 0 := by
  subst hN
  exact chi_subsingleton ts _ (inferInstanceAs (Subsingleton (⊥ : Submodule R G.M))) m

end Step

theorem add_of_hom {k : ℕ} (X : HidaSetting k) (hGr : RuleGr) (ts : List (Deg k × X.R))
    (ih : ∀ F' F F'' : X.Mod, F'.IsGr X.𝒜 → F.IsGr X.𝒜 → F''.IsGr X.𝒜 → SES F' F F'' →
      admitted X.𝒜 ts F.Ann → ∀ᶠ m in atTop, chi ts F m = chi ts F' m + chi ts F'' m)
    {G H : X.Mod} (hG : G.IsGr X.𝒜) (hH : H.IsGr X.𝒜) (φ : G.M →ₗ[X.R] H.M)
    (hφ : ∀ m, ∀ x ∈ G.gr m, φ x ∈ H.gr m) (hA : admitted X.𝒜 ts G.Ann) :
    ∀ᶠ m in atTop, chi ts G m =
      chi ts (G.sub (LinearMap.ker φ)) m + chi ts (H.sub (LinearMap.range φ)) m :=
  ih _ _ _ ((hGr k X G hG).1 _ (isHomSub_ker hG.internal hH.internal φ hφ)).1 hG
    ((hGr k X H hH).1 _ (isHomSub_range hG.internal hH.internal φ hφ)).1
    (sesHom hG.internal hH.internal φ hφ) hA

end E1

open E1 in

theorem euler_additivity_of_rules : RuleGr → RuleFin → RuleIso → EulerAdditivityExactSequence := by
  intro hGr hFin hIso k X ts
  induction ts with
  | nil =>
    intro F' F F'' _ hF' hF hF'' S hA
    filter_upwards [(hFin k X F hF).2 hA] with m hm
    simp only [chi]
    rw [length_add S m] at hm ⊢
    rw [ENat.toNat_add (fun h => hm (by rw [h, top_add])) (fun h => hm (by rw [h, add_top]))]
    push_cast
    rfl
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro F' F F'' hV hF' hF hF'' S hA
    have hs : s ∈ X.𝒜 d := (hV (d, s) List.mem_cons_self).2
    have hV' : Valid X.𝒜 ts := fun p hp => hV p (List.mem_cons_of_mem _ hp)
    have ih' := fun A B C => ih A B C hV'
    obtain ⟨hq', ha'⟩ := (hGr k X F' hF').2.2 d s hs
    obtain ⟨hq, ha⟩ := (hGr k X F hF).2.2 d s hs
    obtain ⟨hq'', ha''⟩ := (hGr k X F'' hF'').2.2 d s hs
    have e1 := add_of_hom X hGr ts ih' ha' ha (annMap S.f s d) (annMap_gr _ (f_gr' S) s d)
      (adm_of_section_mem s d X.𝒜 hA ((ann_le_left S).trans (ann_le_ann s d F')) (mem_ann_ann s d F'))
    have e2 := add_of_hom X hGr ts ih' ha ha'' (annMap S.g s d) (annMap_gr _ (g_gr' S) s d)
      (adm_of_section_mem s d X.𝒜 hA (ann_le_ann s d F) (mem_ann_ann s d F))
    have e3 := add_of_hom X hGr ts ih' ha'' hq' (delta S s d)
      (delta_gr S s d (fun m x hx => hF.smul_mem hs hx))
      (adm_of_section_mem s d X.𝒜 hA ((ann_le_right S).trans (ann_le_ann s d F'')) (mem_ann_ann s d F''))
    have e4 := add_of_hom X hGr ts ih' hq' hq (quotMap S.f s) (quotMap_gr _ (f_gr' S) s)
      (adm_of_section_mem s d X.𝒜 hA ((ann_le_left S).trans (ann_le_quot s F')) (mem_ann_quot s F'))
    have e5 := add_of_hom X hGr ts ih' hq hq'' (quotMap S.g s) (quotMap_gr _ (g_gr' S) s)
      (adm_of_section_mem s d X.𝒜 hA (ann_le_quot s F) (mem_ann_quot s F))
    filter_upwards [e1, e2, e3, e4, e5] with m e1 e2 e3 e4 e5
    simp only [chi]
    rw [chi_sub_bot ts _ _ (LinearMap.ker_eq_bot.2 (annMap_f_inj S s d)), zero_add,
      ← LinearMap.exact_iff.1 (exact_ann S s d)] at e1
    rw [← LinearMap.exact_iff.1 (exact_ann_delta S s d)] at e2
    rw [← LinearMap.exact_iff.1 (exact_delta_quot S s d)] at e3
    rw [← LinearMap.exact_iff.1 (exact_quot S s)] at e4
    rw [hIso k X ts _ _ (topIso _ _ (LinearMap.range_eq_top.2 (quotMap_g_surj S s))) m] at e5
    linarith

end Formalism.MainNotions.V.Pf.V2.Calc
