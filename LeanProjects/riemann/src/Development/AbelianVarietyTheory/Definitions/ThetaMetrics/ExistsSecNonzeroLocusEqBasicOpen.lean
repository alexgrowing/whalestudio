import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

open LBGerm

variable {X : Scheme.{0}}

theorem exists_sec_of_refinement {M : LB X} (hM : M.IsLB) {α : Type} (W : α → X.Opens) (i : α → M.ι)
    (hW : ∀ a, W a ≤ M.U (i a)) (hc : ∀ y : X, ∃ a, y ∈ W a) (t : ∀ a, Γ(X, W a))
    (ht : ∀ (y : X) a b, y ∈ W a → y ∈ W b → gs (𝟙 X) y _ (t a) =
      (gm (𝟙 X) y (M.U (i a) ⊓ M.U (i b)) (M.g (i a) (i b))).val * gs (𝟙 X) y _ (t b)) :
    ∃ u : M.Sec, ∀ (y : X) k a, y ∈ M.U k → y ∈ W a → gs (𝟙 X) y _ (u.f k) =
      (gm (𝟙 X) y (M.U k ⊓ M.U (i a)) (M.g k (i a))).val * gs (𝟙 X) y _ (t a) := by
  have glue : ∀ k, ∃ c : Γ(X, M.U k), ∀ (y : X) a, y ∈ M.U k → y ∈ W a → gs (𝟙 X) y _ c =
      (gm (𝟙 X) y (M.U k ⊓ M.U (i a)) (M.g k (i a))).val * gs (𝟙 X) y _ (t a) := by
    intro k
    obtain ⟨v, hv⟩ : ∃ v : ∀ a, Γ(X, M.U k ⊓ W a), ∀ (y : X) a, y ∈ M.U k ⊓ W a → gs (𝟙 X) y _ (v a) =
        (gm (𝟙 X) y (M.U k ⊓ M.U (i a)) (M.g k (i a))).val * gs (𝟙 X) y _ (t a) :=
      ⟨fun a => resG X (inf_le_inf_left _ (hW a)) (M.g k (i a)).val * resG X inf_le_right (t a), fun y a hy => by
        rw [gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy,
          gs_unit (𝟙 X) y (M.U k ⊓ M.U (i a)) ⟨hy.1, hW a hy.2⟩]⟩
    obtain ⟨c, hc', -⟩ := DVR.sec_glue (M.U k) (fun a => M.U k ⊓ W a) (fun _ => inf_le_left) (fun y hy => by
        obtain ⟨a, ha⟩ := hc y
        exact Opens.mem_iSup.2 ⟨a, hy, ha⟩) v (fun a b => fn_ext fun y hy => by
        rw [gs_res _ y _ hy, gs_res _ y _ hy, hv y a hy.1, hv y b hy.2, ht y a b hy.1.2 hy.2.2, ← mul_assoc,
          ← Units.val_mul, gm_cocycle hM (𝟙 X) y hy.1.1 (hW a hy.1.2) (hW b hy.2.2)])
    refine ⟨c, fun y a hk ha => ?_⟩
    have hy : y ∈ M.U k ⊓ W a := ⟨hk, ha⟩
    exact (gs_res (𝟙 X) y inf_le_left hy c).symm.trans ((congrArg (gs (𝟙 X) y _) (hc' a)).trans (hv y a hy))
  choose c hc' using glue
  refine ⟨secOfGerm c fun y k k' hk hk' => ?_, fun y k a hk ha => hc' k y a hk ha⟩
  obtain ⟨a, ha⟩ := hc y
  rw [hc' k y a hk ha, hc' k' y a hk' ha, ← mul_assoc, ← Units.val_mul, gm_cocycle hM (𝟙 X) y hk hk' (hW a ha)]

theorem exists_finite_affine_refinement [CompactSpace X] {M : LB X} (hM : M.IsLB) :
    ∃ (α : Type) (_ : Fintype α) (W : α → X.Opens) (i : α → M.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ M.U (i a)) ∧ ∀ y : X, ∃ a, y ∈ W a := by
  have hcov : ∀ y : X, ∃ k, y ∈ M.U k := fun y => by
    have hy : y ∈ (⨆ k, M.U k) := by rw [hM.cover]; simp
    exact Opens.mem_iSup.1 hy
  choose k hk using hcov
  have hV : ∀ y : X, ∃ V : X.Opens, IsAffineOpen V ∧ y ∈ V ∧ V ≤ M.U (k y) := fun y => by
    obtain ⟨V, hVa, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset (hk y)
    exact ⟨V, hVa, hyV, hVU⟩
  choose V hVa hyV hVU using hV
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (V y : Set X)) (fun y => (V y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hyV y⟩)
  refine ⟨t, inferInstance, fun a => V a.1, fun a => k a.1, fun a => hVa a.1, fun a => hVU a.1, fun y => ?_⟩
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  exact ⟨⟨z, hz⟩, hyz⟩

theorem exists_pow_mul_gs_eq_zero {U : X.Opens} (hU : IsCompact (U : Set X)) (f x : Γ(X, U))
    (h : ∀ y ∈ X.basicOpen f, gs (𝟙 X) y U x = 0) :
    ∃ e : ℕ, ∀ y ∈ U, gs (𝟙 X) y U f ^ e * gs (𝟙 X) y U x = 0 := by
  obtain ⟨e, he⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hU x f
    (show resG X (X.basicOpen_le f) x = 0 from fn_ext fun y hy => by
      rw [gs_res _ y _ hy, gs_zero _ y _ hy]; exact h y hy)
  refine ⟨e, fun y hy => ?_⟩
  rw [← gs_pow _ y _ hy, ← gs_mul _ y _ hy, he, gs_zero _ y _ hy]

variable {L : LB X} {m n : ℕ}

theorem exists_pow_mul_powFn_eq_zero [CompactSpace X] (hL : L.IsLB) (s : (lbPow L n).Sec) (u : (lbPow L m).Sec)
    (h : ∀ J, resG X (inf_le_right : nonzeroLocus s ⊓ powChart L J ≤ powChart L J) (powFn u J) = 0) :
    ∃ k : ℕ, ∀ J, powFn s J ^ k * powFn u J = 0 := by
  obtain ⟨α, _, W, J, hWa, hW, hc⟩ : ∃ (α : Type) (_ : Fintype α) (W : α → X.Opens) (J : α → PUnit → L.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ powChart L (J a)) ∧ ∀ y : X, ∃ a, y ∈ W a :=
    exists_finite_affine_refinement (isLB_lbPow hL 0)
  have step : ∀ a, ∃ e : ℕ, ∀ y ∈ W a,
      gs (𝟙 X) y _ (powFn s (J a)) ^ e * gs (𝟙 X) y _ (powFn u (J a)) = 0 := fun a => by
    obtain ⟨e, he⟩ := exists_pow_mul_gs_eq_zero (hWa a).isCompact (resG X (hW a) (powFn s (J a)))
      (resG X (hW a) (powFn u (J a))) fun y hy => by
        have hy₁ : y ∈ W a := X.basicOpen_le _ hy
        have hs := (isUnit_gs_iff (𝟙 X) y _ hy₁ _).2 hy
        rw [gs_res _ y _ hy₁, ← mem_nonzeroLocus_iff_powFn s (hW a hy₁)] at hs
        have hy₂ : y ∈ nonzeroLocus s ⊓ powChart L (J a) := ⟨hs, hW a hy₁⟩
        have e := congrArg (gs (𝟙 X) y _) (h (J a))
        rw [gs_res _ y _ hy₂, gs_zero _ y _ hy₂] at e
        rw [gs_res _ y _ hy₁, e]
    refine ⟨e, fun y hy => ?_⟩
    have := he y hy
    rwa [gs_res _ y _ hy, gs_res _ y _ hy] at this
  choose e he using step
  refine ⟨Finset.univ.sup e, fun I => fn_ext fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := hc y
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := e) (Finset.mem_univ a))
  rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_zero _ y _ hy, gs_powFn_compat s (𝟙 X) y I (J a) hy (hW a ha),
    gs_powFn_compat u (𝟙 X) y I (J a) hy (hW a ha), hd]
  have e₁ := he a y ha
  generalize gs (𝟙 X) y _ (powFn s (J a)) = σ at e₁ ⊢
  generalize gs (𝟙 X) y _ (powFn u (J a)) = υ at e₁ ⊢
  generalize Units.val (gm (𝟙 X) y _ (L.g (I PUnit.unit) (J a PUnit.unit))) = γ
  linear_combination (γ ^ (n * (e a + d)) * γ ^ m * σ ^ d) * e₁

theorem exists_sec_eq_pow_mul [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) (s : (lbPow L n).Sec)
    (t : ∀ J : PUnit → L.ι, Γ(X, nonzeroLocus s ⊓ powChart L J)) (ht : t ∈ secOn (lbPow L m) (nonzeroLocus s)) :
    ∃ N : ℕ, ∀ k, N ≤ k → ∃ u : (lbPow L (m + n * k)).Sec, ∀ J,
      resG X (inf_le_right : nonzeroLocus s ⊓ powChart L J ≤ powChart L J) (powFn u J) =
        resG X (inf_le_right : nonzeroLocus s ⊓ powChart L J ≤ powChart L J) (powFn s J) ^ k * t J := by
  obtain ⟨α, _, W, J, hWa, hW, hc⟩ : ∃ (α : Type) (_ : Fintype α) (W : α → X.Opens) (J : α → PUnit → L.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ powChart L (J a)) ∧ ∀ y : X, ∃ a, y ∈ W a :=
    exists_finite_affine_refinement (isLB_lbPow hL 0)
  have htc : ∀ (y : X) (I I' : PUnit → L.ι), y ∈ nonzeroLocus s → y ∈ powChart L I → y ∈ powChart L I' →
      gs (𝟙 X) y _ (t I) = (gm (𝟙 X) y (L.U (I PUnit.unit) ⊓ L.U (I' PUnit.unit))
        (L.g (I PUnit.unit) (I' PUnit.unit))).val ^ m * gs (𝟙 X) y _ (t I') := fun y I I' hs hI hI' => by
    have e := gs_secOn ht y I I' hs hI hI'
    rw [gm_lbPow_g m (𝟙 X) y I I' hI hI', Units.val_pow_eq_pow_val] at e
    exact e
  have hb : ∀ (V : X.Opens) (I : PUnit → L.ι) (hV : V ≤ powChart L I) (y : X),
      y ∈ X.basicOpen (resG X hV (powFn s I)) → y ∈ nonzeroLocus s := fun V I hV y hy => by
    have hy₁ : y ∈ V := X.basicOpen_le _ hy
    have hs := (isUnit_gs_iff (𝟙 X) y _ hy₁ _).2 hy
    rwa [gs_res _ y _ hy₁, ← mem_nonzeroLocus_iff_powFn s (hV hy₁)] at hs
  have step₁ : ∀ a, ∃ (e : ℕ) (v : Γ(X, W a)), ∀ y ∈ W a, y ∈ nonzeroLocus s →
      gs (𝟙 X) y _ v = gs (𝟙 X) y _ (powFn s (J a)) ^ e * gs (𝟙 X) y _ (t (J a)) := fun a => by
    have le : X.basicOpen (resG X (hW a) (powFn s (J a))) ≤ nonzeroLocus s ⊓ powChart L (J a) :=
      fun y hy => ⟨hb _ _ _ y hy, hW a (X.basicOpen_le _ hy)⟩
    obtain ⟨e, v, hv⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X (W a) (hWa a).isCompact
      (hWa a).isQuasiSeparated (resG X (hW a) (powFn s (J a))) (resG X le (t (J a)))
    have hv' : resG X (X.basicOpen_le _) v =
        resG X (X.basicOpen_le _) (resG X (hW a) (powFn s (J a))) ^ e * resG X le (t (J a)) := hv
    refine ⟨e, v, fun y hy hs => ?_⟩
    have hy' : y ∈ X.basicOpen (resG X (hW a) (powFn s (J a))) := (isUnit_gs_iff (𝟙 X) y _ hy _).1 (by
      rw [gs_res _ y _ hy]; exact (mem_nonzeroLocus_iff_powFn s (hW a hy)).1 hs)
    have e₁ := congrArg (gs (𝟙 X) y _) hv'
    rwa [gs_res _ y _ hy', gs_mul _ y _ hy', gs_pow _ y _ hy', gs_res _ y _ hy', gs_res _ y _ hy,
      gs_res _ y _ hy'] at e₁
  choose e v hv using step₁
  obtain ⟨N₁, v', hv'⟩ : ∃ (N₁ : ℕ) (v' : ∀ a, Γ(X, W a)), ∀ a, ∀ y ∈ W a, y ∈ nonzeroLocus s →
      gs (𝟙 X) y _ (v' a) = gs (𝟙 X) y _ (powFn s (J a)) ^ N₁ * gs (𝟙 X) y _ (t (J a)) :=
    ⟨Finset.univ.sup e, fun a => resG X (hW a) (powFn s (J a)) ^ (Finset.univ.sup e - e a) * v a, fun a y hy hs => by
      rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, hv a y hy hs, ← mul_assoc, ← pow_add,
        Nat.sub_add_cancel (Finset.le_sup (f := e) (Finset.mem_univ a))]⟩
  have step₂ : ∀ p : α × α, ∃ d : ℕ, ∀ y ∈ W p.1 ⊓ W p.2, gs (𝟙 X) y _ (powFn s (J p.1)) ^ d *
      (gs (𝟙 X) y _ (v' p.1) - (gm (𝟙 X) y (L.U (J p.1 PUnit.unit) ⊓ L.U (J p.2 PUnit.unit))
        (L.g (J p.1 PUnit.unit) (J p.2 PUnit.unit))).val ^ (m + n * N₁) * gs (𝟙 X) y _ (v' p.2)) = 0 := by
    rintro ⟨a, b⟩
    have hcpt : IsCompact ((W a ⊓ W b : X.Opens) : Set X) :=
      QuasiSeparatedSpace.inter_isCompact _ _ (W a).isOpen (hWa a).isCompact (W b).isOpen (hWa b).isCompact
    have le : W a ⊓ W b ≤ L.U (J a PUnit.unit) ⊓ L.U (J b PUnit.unit) :=
      fun y hy => ⟨mem_powChart.1 (hW a hy.1), mem_powChart.1 (hW b hy.2)⟩
    have hx : ∀ y ∈ W a ⊓ W b, gs (𝟙 X) y (W a ⊓ W b) (resG X inf_le_left (v' a) -
        resG X le (L.g (J a PUnit.unit) (J b PUnit.unit)).val ^ (m + n * N₁) * resG X inf_le_right (v' b)) =
        gs (𝟙 X) y _ (v' a) - (gm (𝟙 X) y (L.U (J a PUnit.unit) ⊓ L.U (J b PUnit.unit))
          (L.g (J a PUnit.unit) (J b PUnit.unit))).val ^ (m + n * N₁) * gs (𝟙 X) y _ (v' b) := fun y hy => by
      rw [gs_sub _ y _ hy, gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy,
        gs_unit (𝟙 X) y _ (le hy)]
    obtain ⟨d, hd⟩ := exists_pow_mul_gs_eq_zero hcpt (resG X (inf_le_left.trans (hW a)) (powFn s (J a))) _
      fun y hy => by
        have hy₁ : y ∈ W a ⊓ W b := X.basicOpen_le _ hy
        have hs := hb _ _ _ y hy
        refine (hx y hy₁).trans ?_
        rw [hv' a y hy₁.1 hs, hv' b y hy₁.2 hs, htc y (J a) (J b) hs (hW a hy₁.1) (hW b hy₁.2),
          gs_powFn_compat s (𝟙 X) y (J a) (J b) (hW a hy₁.1) (hW b hy₁.2)]
        ring
    refine ⟨d, fun y hy => ?_⟩
    have := hd y hy
    rwa [hx y hy, gs_res _ y _ hy] at this
  choose d hd using step₂
  refine ⟨N₁ + Finset.univ.sup d, fun k hk => ?_⟩
  obtain ⟨c, rfl⟩ : ∃ c, k = N₁ + c := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right _ _) hk)
  have hc' : Finset.univ.sup d ≤ c := Nat.le_of_add_le_add_left hk
  have hz : ∀ a, ∀ y ∈ W a, gs (𝟙 X) y _ (resG X (hW a) (powFn s (J a)) ^ c * v' a) =
      gs (𝟙 X) y _ (powFn s (J a)) ^ c * gs (𝟙 X) y _ (v' a) := fun a y hy => by
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy]
  obtain ⟨u, hu⟩ := exists_sec_of_refinement (isLB_lbPow hL (m + n * (N₁ + c))) W J hW hc
    (fun a => resG X (hW a) (powFn s (J a)) ^ c * v' a) fun y a b ha hb => by
      obtain ⟨c', hc''⟩ := Nat.exists_eq_add_of_le ((Finset.le_sup (f := d) (Finset.mem_univ (a, b))).trans hc')
      have e₁ := hd (a, b) y ⟨ha, hb⟩
      have e₂ := gs_powFn_compat s (𝟙 X) y (J a) (J b) (hW a ha) (hW b hb)
      rw [hz a y ha, hz b y hb, gm_lbPow_g _ (𝟙 X) y (J a) (J b) (hW a ha) (hW b hb), Units.val_pow_eq_pow_val]
      dsimp only at e₁
      rw [e₂] at e₁ ⊢
      rw [hc'']
      generalize gs (𝟙 X) y _ (powFn s (J b)) = σ at e₁ ⊢
      generalize Units.val (gm (𝟙 X) y _ (L.g (J a PUnit.unit) (J b PUnit.unit))) = γ at e₁ ⊢
      linear_combination (γ ^ n * σ) ^ c' * e₁
  refine ⟨u, fun I => fn_ext fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := hc y
  have e₁ := hu y I a hy.2 ha
  rw [hz a y ha, gm_lbPow_g _ (𝟙 X) y I (J a) hy.2 (hW a ha), Units.val_pow_eq_pow_val, hv' a y ha hy.1] at e₁
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, htc y I (J a) hy.1 hy.2 (hW a ha),
    gs_powFn_compat s (𝟙 X) y I (J a) hy.2 (hW a ha)]
  refine Eq.trans e₁ ?_
  ring

theorem exists_nonzeroLocus_eq_basicOpen [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) (s : (lbPow L n).Sec)
    (f : Γ(X, nonzeroLocus s)) :
    ∃ k, 1 ≤ k ∧ ∃ u : (lbPow L (n * k)).Sec, nonzeroLocus u = X.basicOpen f := by
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul (m := 0) hL s (fun J => resG X inf_le_left f)
    (mem_secOn_of_germ (M := lbPow L 0) _ fun y J J' hs hJ hJ' => by
      rw [gm_lbPow_g 0 (𝟙 X) y J J' hJ hJ', pow_zero, Units.val_one, one_mul]
      exact (gs_res (𝟙 X) y inf_le_left ⟨hs, hJ⟩ f).trans (gs_res (𝟙 X) y inf_le_left ⟨hs, hJ'⟩ f).symm)
  obtain ⟨u, hu⟩ := hN N le_rfl
  refine ⟨N + 1, Nat.le_add_left _ _, secCast (by ring) (secMul u s), ?_⟩
  rw [nonzeroLocus_secCast, nonzeroLocus_secMul]
  have key : ∀ y ∈ nonzeroLocus s, y ∈ nonzeroLocus u ↔ y ∈ X.basicOpen f := fun y hs => by
    obtain ⟨J, hJ⟩ : ∃ J, y ∈ powChart L J := exists_chart_of_mem_nonzeroLocus hs
    have hy : y ∈ nonzeroLocus s ⊓ powChart L J := ⟨hs, hJ⟩
    have e := congrArg (gs (𝟙 X) y _) (hu J)
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy] at e
    rw [mem_nonzeroLocus_iff_powFn u hJ, e, IsUnit.mul_iff, isUnit_gs_iff (𝟙 X) y _ hs f]
    exact and_iff_right (((mem_nonzeroLocus_iff_powFn s hJ).1 hs).pow N)
  exact le_antisymm (fun y hy => (key y hy.2).1 hy.1)
    (fun y hy => ⟨(key y (X.basicOpen_le f hy)).2 hy, X.basicOpen_le f hy⟩)

theorem exists_sec_nonzeroLocus_eq_basicOpen [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) (r : Γ(X, ⊤))
    (i : L.ι) (hr : X.basicOpen r ≤ L.U i) : ∃ u : L.Sec, nonzeroLocus u = X.basicOpen r := by
  have hs := nonzeroLocus_secOfFn hL r
  have le : ∀ J : PUnit → L.ι, nonzeroLocus (secOfFn L r) ⊓ powChart L J ≤ L.U (J PUnit.unit) ⊓ L.U i :=
    fun J y hy => ⟨mem_powChart.1 hy.2, hr (hs.le hy.1)⟩
  have hg : ∀ (J : PUnit → L.ι) (y : X), y ∈ nonzeroLocus (secOfFn L r) ⊓ powChart L J →
      gs (𝟙 X) y _ (resG X (le J) (L.g (J PUnit.unit) i).val) =
        (gm (𝟙 X) y (L.U (J PUnit.unit) ⊓ L.U i) (L.g (J PUnit.unit) i)).val := fun J y hy =>
    (gs_res (𝟙 X) y _ hy _).trans (gs_unit (𝟙 X) y _ (le J hy) _)
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul (m := 1) hL (secOfFn L r) (fun J => resG X (le J) (L.g (J PUnit.unit) i).val)
    (mem_secOn_of_germ (M := lbPow L 1) _ fun y J J' h hJ hJ' => by
      rw [gm_lbPow_g 1 (𝟙 X) y J J' hJ hJ', pow_one]
      refine (hg J y ⟨h, hJ⟩).trans (Eq.trans ?_ (congrArg _ (hg J' y ⟨h, hJ'⟩)).symm)
      rw [← Units.val_mul, gm_cocycle hL (𝟙 X) y (mem_powChart.1 hJ) (mem_powChart.1 hJ') (hr (hs.le h))])
  obtain ⟨u, hu⟩ := hN N le_rfl
  refine ⟨secOfPowOne (secCast (by simp) (secMul u (secOfFn L r))), ?_⟩
  rw [nonzeroLocus_secOfPowOne, nonzeroLocus_secCast, nonzeroLocus_secMul, ← hs, inf_eq_right]
  intro y h
  obtain ⟨J, hJ⟩ : ∃ J, y ∈ powChart L J := exists_chart_of_mem_nonzeroLocus h
  have hy : y ∈ nonzeroLocus (secOfFn L r) ⊓ powChart L J := ⟨h, hJ⟩
  have e := congrArg (gs (𝟙 X) y _) (hu J)
  rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, hg J y hy] at e
  rw [mem_nonzeroLocus_iff_powFn u hJ, e]
  exact (((mem_nonzeroLocus_iff_powFn _ hJ).1 h).pow N).mul (Units.isUnit _)

end GlobalTheory
