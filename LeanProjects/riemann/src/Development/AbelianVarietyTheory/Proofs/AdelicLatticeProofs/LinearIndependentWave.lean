import Mathlib

noncomputable section

namespace GlobalTheory.PlaceModel

variable {G : Type} [AddCommGroup G]

open Classical in

def ind (L : AddSubgroup G) (t : G) : ℂ := if t ∈ L then 1 else 0

def wave (χ : G → G → ℂ) (L : AddSubgroup G) (x y : G) : G → ℂ := fun t => χ (t + x) y * ind L (t + x)

def waveSpan (χ : G → G → ℂ) (X Y L : AddSubgroup G) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ {Φ | ∃ x ∈ X, ∃ y ∈ Y, Φ = wave χ L x y}

structure IsBichar (χ : G → G → ℂ) : Prop where
  left : ∀ a b y, χ (a + b) y = χ a y * χ b y
  right : ∀ a y z, χ a (y + z) = χ a y * χ a z
  zero_left : ∀ y, χ 0 y = 1
  zero_right : ∀ a, χ a 0 = 1

theorem isBichar_one : IsBichar (fun _ _ : G => (1 : ℂ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> simp

theorem isBichar_neg_one_zpow : IsBichar (fun a b : ℤ => (-1 : ℂ) ^ (a * b)) := by
  have h0 : (-1 : ℂ) ≠ 0 := by norm_num
  refine ⟨fun a b y => ?_, fun a y z => ?_, fun y => ?_, fun a => ?_⟩
  · rw [add_mul, zpow_add₀ h0]
  · rw [mul_add, zpow_add₀ h0]
  · simp
  · simp

variable {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}

theorem ind_add (L : AddSubgroup G) (t : G) {u : G} (hu : u ∈ L) : ind L (t + u) = ind L t := by
  unfold ind
  by_cases ht : t ∈ L
  · rw [if_pos ht, if_pos ((L.add_mem_cancel_right hu).mpr ht)]
  · rw [if_neg ht, if_neg fun h' => ht ((L.add_mem_cancel_right hu).mp h')]

theorem IsBichar.neg_mul (h : IsBichar χ) (x y : G) : χ (-x) y * χ x y = 1 := by
  rw [← h.left, neg_add_cancel, h.zero_left]

theorem IsBichar.nsmul (h : IsBichar χ) (k : ℕ) (x y : G) : χ (k • x) y = χ x (k • y) := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, h.zero_left, h.zero_right]
  | succ k ih => rw [succ_nsmul, succ_nsmul, h.left, h.right, ih]

theorem wave_trans (x x' y : G) : (fun t => wave χ L x y (t + x')) = wave χ L (x' + x) y := by
  funext t
  simp only [wave, add_assoc]

theorem wave_modul (h : IsBichar χ) (x y y' : G) :
    (fun t => χ t y' * wave χ L x y t) = χ (-x) y' • wave χ L x (y' + y) := by
  funext t
  simp only [wave, Pi.smul_apply, smul_eq_mul]
  rw [h.right, h.left t x y']
  linear_combination (-(χ t y' * χ (t + x) y * ind L (t + x))) * h.neg_mul x y'

theorem wave_zero (h : IsBichar χ) : wave χ L 0 0 = ind L := by
  funext t
  simp [wave, h.zero_right]

theorem wave_add (h : IsBichar χ) (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1) (x y : G) {l l' : G} (hl : l ∈ L)
    (hl' : l' ∈ L') : wave χ L (x + l) (y + l') = χ l y • wave χ L x y := by
  funext t
  simp only [wave, Pi.smul_apply, smul_eq_mul]
  rw [← add_assoc, ind_add L (t + x) hl]
  by_cases ht : t + x ∈ L
  · rw [h.left (t + x) l (y + l'), h.right (t + x) y l', h.right l y l', hLL' _ ht l' hl',
      hLL' l hl l' hl']
    ring
  · simp [ind, ht]

theorem linearIndependent_wave (h : IsBichar χ) (hY : ∀ y ∈ Y, (∀ u ∈ L, χ u y = 1) → y ∈ L') :
    LinearIndependent ℂ fun i : (X ⧸ L.addSubgroupOf X) × (Y ⧸ L'.addSubgroupOf Y) =>
      wave χ L (i.1.out : X) (i.2.out : Y) := by
  classical

  let ψ : (Y ⧸ L'.addSubgroupOf Y) → (Multiplicative L →* ℂ) := fun d =>
    { toFun := fun u => χ ((Multiplicative.toAdd u : L) : G) ((d.out : Y) : G)
      map_one' := by simp [h.zero_left]
      map_mul' := fun u w => by simp [h.left] }
  have hψ : Function.Injective ψ := by
    intro d d' hdd
    have hval : ∀ u ∈ L, χ u ((d.out : Y) : G) = χ u ((d'.out : Y) : G) := fun u hu =>
      DFunLike.congr_fun hdd (Multiplicative.ofAdd (⟨u, hu⟩ : L))
    rw [← QuotientAddGroup.out_eq' d, ← QuotientAddGroup.out_eq' d', QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    refine hY _ (Y.add_mem (Y.neg_mem (d.out).2) (d'.out).2) fun u hu => ?_
    rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, h.right, ← hval u hu, ← h.right, neg_add_cancel,
      h.zero_right]
  have hind := (linearIndependent_monoidHom (Multiplicative L) ℂ).comp ψ hψ
  rw [linearIndependent_iff'] at hind ⊢
  intro s g hg i hi
  obtain ⟨a, c⟩ := i

  have hsupp : ∀ (b : X ⧸ L.addSubgroupOf X) (y u : G), u ∈ L →
      wave χ L ((b.out : X) : G) y (u - ((a.out : X) : G)) = if b = a then χ u y else 0 := by
    intro b y u hu
    simp only [wave]
    by_cases hb : b = a
    · subst hb
      simp [ind, hu]
    · rw [if_neg hb]
      have hn : u - ((a.out : X) : G) + ((b.out : X) : G) ∉ L := by
        intro hm
        apply hb
        rw [← QuotientAddGroup.out_eq' a, ← QuotientAddGroup.out_eq' b, QuotientAddGroup.eq,
          AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg]
        have h2 := L.add_mem (L.neg_mem hm) hu
        convert h2 using 1
        abel
      simp [ind, hn]
  let T : Finset (Y ⧸ L'.addSubgroupOf Y) := (s.filter (fun i => i.1 = a)).image Prod.snd
  have hrel : ∑ d ∈ T, g (a, d) • ((fun f : Multiplicative L →* ℂ => (f : Multiplicative L → ℂ)) ∘ ψ) d
      = 0 := by
    funext u
    have e := congrFun hg (((Multiplicative.toAdd u : L) : G) - ((a.out : X) : G))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    rw [Finset.sum_image (fun i hi j hj hij => ?_)]
    · rw [Finset.sum_filter]
      refine (Finset.sum_congr rfl fun i _ => ?_).trans e
      rw [hsupp i.1 _ _ (Multiplicative.toAdd u).2]
      by_cases h1 : i.1 = a
      · rw [if_pos h1, if_pos h1]
        obtain ⟨i1, i2⟩ := i
        simp only at h1
        subst h1
        rfl
      · rw [if_neg h1, if_neg h1, mul_zero]
    · simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hi hj
      exact Prod.ext (hi.2.trans hj.2.symm) hij
  exact hind T (fun d => g (a, d)) hrel c
    (Finset.mem_image.mpr ⟨(a, c), Finset.mem_filter.mpr ⟨hi, rfl⟩, rfl⟩)

theorem exists_map_wave {V : Type} [AddCommGroup V] [Module ℂ V] (h : IsBichar χ) (hL : L ≤ X) (hL' : L' ≤ Y)
    (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1) (hY : ∀ y ∈ Y, (∀ u ∈ L, χ u y = 1) → y ∈ L')
    (ρ : G → V →ₗ[ℂ] V) (ρX : ∀ x ∈ X, ∀ x' ∈ X, ∀ f, ρ x (ρ x' f) = ρ (x + x') f)
    (ρY : ∀ y ∈ Y, ∀ y' ∈ Y, ∀ f, ρ y (ρ y' f) = ρ (y + y') f)
    (ρXY : ∀ x ∈ X, ∀ y ∈ Y, ∀ f, ρ x (ρ y f) = χ x y • ρ y (ρ x f))
    (f₀ : V) (hf : ∀ u ∈ L, ρ u f₀ = f₀) (hf' : ∀ u ∈ L', ρ u f₀ = f₀) :
    ∃ T : (G → ℂ) →ₗ[ℂ] V, ∀ x ∈ X, ∀ y ∈ Y, T (wave χ L x y) = ρ x (ρ y f₀) := by
  classical
  have hli := linearIndependent_wave (χ := χ) (X := X) (L := L) (L' := L') h hY
  let B := Module.Basis.span hli
  let T₀ := B.constr ℂ (fun i : (X ⧸ L.addSubgroupOf X) × (Y ⧸ L'.addSubgroupOf Y) =>
    ρ ((i.1.out : X) : G) (ρ ((i.2.out : Y) : G) f₀))
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T₀

  have hTv : ∀ i : (X ⧸ L.addSubgroupOf X) × (Y ⧸ L'.addSubgroupOf Y),
      T (wave χ L ((i.1.out : X) : G) ((i.2.out : Y) : G)) =
        ρ ((i.1.out : X) : G) (ρ ((i.2.out : Y) : G) f₀) := by
    intro i
    have e1 : ((B i : Submodule.span ℂ _) : G → ℂ) =
        wave χ L ((i.1.out : X) : G) ((i.2.out : Y) : G) := by
      simp [B]
    have e2 := LinearMap.congr_fun hT (B i)
    rw [LinearMap.comp_apply, Submodule.subtype_apply, e1] at e2
    rw [e2]
    exact Module.Basis.constr_basis B ℂ _ i
  refine ⟨T, fun x hx y hy => ?_⟩
  obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_add (L.addSubgroupOf X) (⟨x, hx⟩ : X)
  obtain ⟨l', hl'⟩ := QuotientAddGroup.mk_out_eq_add (L'.addSubgroupOf Y) (⟨y, hy⟩ : Y)
  have hlL : ((l : X) : G) ∈ L := l.2
  have hlL' : ((l' : Y) : G) ∈ L' := l'.2
  have e := hTv (((⟨x, hx⟩ : X) : X ⧸ L.addSubgroupOf X), ((⟨y, hy⟩ : Y) : Y ⧸ L'.addSubgroupOf Y))
  dsimp only at e
  rw [hl, hl'] at e
  change T (wave χ L (x + ((l : X) : G)) (y + ((l' : Y) : G))) =
    ρ (x + ((l : X) : G)) (ρ (y + ((l' : Y) : G)) f₀) at e

  have hρ : ρ (x + ((l : X) : G)) (ρ (y + ((l' : Y) : G)) f₀) = χ ((l : X) : G) y • ρ x (ρ y f₀) := by
    have hlX : ((l : X) : G) ∈ X := hL hlL
    have hlY : ((l' : Y) : G) ∈ Y := hL' hlL'
    rw [← ρY y hy _ hlY, hf' _ hlL', ← ρX x hx _ hlX, ρXY _ hlX y hy, hf _ hlL, map_smul]
  rw [wave_add h hLL' x y hlL hlL', map_smul, hρ] at e
  have hne : χ ((l : X) : G) y ≠ 0 := by
    intro h0
    have h1 := h.neg_mul ((l : X) : G) y
    rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  exact smul_right_injective V hne e

theorem trans_mem {Φ : G → ℂ} (hΦ : Φ ∈ waveSpan χ X Y L) {x : G} (hx : x ∈ X) :
    (fun t => Φ (t + x)) ∈ waveSpan χ X Y L := by
  have hle : waveSpan χ X Y L ≤ (waveSpan χ X Y L).comap (LinearMap.funLeft ℂ ℂ (fun t : G => t + x)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x₀, hx₀, y, hy, rfl⟩
    show (fun t => wave χ L x₀ y (t + x)) ∈ waveSpan χ X Y L
    rw [wave_trans]
    exact Submodule.subset_span ⟨x + x₀, X.add_mem hx hx₀, y, hy, rfl⟩
  exact hle hΦ

theorem modul_mem (h : IsBichar χ) {Φ : G → ℂ} (hΦ : Φ ∈ waveSpan χ X Y L) {y : G} (hy : y ∈ Y) :
    (fun t => χ t y * Φ t) ∈ waveSpan χ X Y L := by
  have hle : waveSpan χ X Y L ≤
      (waveSpan χ X Y L).comap (LinearMap.mulLeft ℂ (fun t : G => χ t y)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x₀, hx₀, y₀, hy₀, rfl⟩
    show (fun t => χ t y * wave χ L x₀ y₀ t) ∈ waveSpan χ X Y L
    rw [wave_modul h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x₀, hx₀, y + y₀, Y.add_mem hy hy₀, rfl⟩)
  exact hle hΦ

theorem ind_nsmul_mem (h : IsBichar χ) (hL : L ≤ X) (hL' : L' ≤ Y) (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1)
    (hX : ∀ x ∈ X, (∀ y ∈ L', χ x y = 1) → x ∈ L) {k : ℕ}
    (dX : ∀ x ∈ X, ∃ x' ∈ X, k • x' = x) (dY : ∀ y ∈ Y, ∃ y' ∈ Y, k • y' = y)
    (R : Set G) (hR : R.Finite) (hfin : ∀ t ∈ L, ∃ r ∈ R, ∃ u ∈ L, t = r + k • u) :
    ind (L.map (nsmulAddMonoidHom k)) ∈ waveSpan χ X Y L := by
  classical
  set K := L.map (nsmulAddMonoidHom k) with hK
  have memK : ∀ t, t ∈ K ↔ ∃ u ∈ L, k • u = t := by
    intro t
    simp [hK, AddSubgroup.mem_map]

  have hsep : ∀ t ∈ L, t ∉ K → ∃ y ∈ Y, k • y ∈ L' ∧ χ t y ≠ 1 := by
    intro t ht htK
    by_contra hcon
    push Not at hcon
    obtain ⟨x', hx', hkx⟩ := dX t (hL ht)
    apply htK
    rw [memK]
    refine ⟨x', hX x' hx' fun y' hy' => ?_, hkx⟩
    obtain ⟨y, hy, hky⟩ := dY y' (hL' hy')
    rw [← hky, ← h.nsmul, hkx]
    exact hcon y hy (by rw [hky]; exact hy')
  have hRf : (R ∩ {r | r ∈ L ∧ r ∉ K}).Finite := hR.subset Set.inter_subset_left
  let F := hRf.toFinset
  have hmemF : ∀ r, r ∈ F ↔ r ∈ R ∧ r ∈ L ∧ r ∉ K := by
    intro r
    simp [F]
  choose! yr hyrY hyrL' hyr using fun r (hr : r ∈ F) =>
    hsep r ((hmemF r).mp hr).2.1 ((hmemF r).mp hr).2.2

  have hstep : ∀ Φ ∈ waveSpan χ X Y L, ∀ y ∈ Y, ∀ α β : ℂ,
      (fun t => Φ t * (α * χ t y + β)) ∈ waveSpan χ X Y L := by
    intro Φ hΦ y hy α β
    have e : (fun t => Φ t * (α * χ t y + β)) = α • (fun t => χ t y * Φ t) + β • Φ := by
      funext t
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact add_mem (Submodule.smul_mem _ _ (modul_mem h hΦ hy)) (Submodule.smul_mem _ _ hΦ)
  have hind0 : ind L ∈ waveSpan χ X Y L := by
    rw [← wave_zero (χ := χ) (L := L) h]
    exact Submodule.subset_span ⟨0, X.zero_mem, 0, Y.zero_mem, rfl⟩
  have hprod : ∀ S : Finset G, S ⊆ F → (fun t => ind L t *
      ∏ r ∈ S, (χ t (yr r) - χ r (yr r)) / (1 - χ r (yr r))) ∈ waveSpan χ X Y L := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro _
      simpa using hind0
    · intro r S hrS ih hsub
      have hrF := hsub (Finset.mem_insert_self r S)
      have h1 := hstep _ (ih fun z hz => hsub (Finset.mem_insert_of_mem hz)) (yr r) (hyrY r hrF)
        (1 - χ r (yr r))⁻¹ (-(χ r (yr r)) * (1 - χ r (yr r))⁻¹)
      convert h1 using 1
      funext t
      rw [Finset.prod_insert hrS]
      ring
  convert hprod F (subset_refl _) using 1
  funext t
  by_cases htL : t ∈ L
  · obtain ⟨r0, hr0, u, hu, rfl⟩ := hfin t htL
    have hshift : ∀ r ∈ F, χ (r0 + k • u) (yr r) = χ r0 (yr r) := fun r hr => by
      rw [h.left, h.nsmul, hLL' u hu _ (hyrL' r hr), mul_one]
    rw [show ind L (r0 + k • u) = 1 by simp [ind, htL], one_mul]
    by_cases hK0 : r0 + k • u ∈ K
    · rw [show ind K (r0 + k • u) = 1 by simp [ind, hK0]]
      symm
      refine Finset.prod_eq_one fun r hr => ?_
      obtain ⟨w, hw, hkw⟩ := (memK _).mp hK0
      rw [← hkw, h.nsmul, hLL' w hw _ (hyrL' r hr), div_self (sub_ne_zero.mpr (hyr r hr).symm)]
    · rw [show ind K (r0 + k • u) = 0 by simp [ind, hK0]]
      symm
      have hr0L : r0 ∈ L := by
        have h2 := L.sub_mem htL (L.nsmul_mem hu k)
        simpa using h2
      have hr0K : r0 ∉ K := fun hm => hK0 (K.add_mem hm ((memK _).mpr ⟨u, hu, rfl⟩))
      have hr0F : r0 ∈ F := (hmemF r0).mpr ⟨hr0, hr0L, hr0K⟩
      refine Finset.prod_eq_zero hr0F ?_
      rw [hshift r0 hr0F, sub_self, zero_div]
  · have htK : t ∉ K := fun hm => htL (by
      obtain ⟨w, hw, hkw⟩ := (memK _).mp hm
      rw [← hkw]
      exact L.nsmul_mem hw k)
    simp [ind, htL, htK]

theorem mem_of_finite_cosets {K : AddSubgroup G} (hK : ind K ∈ waveSpan χ X Y L) (P : Finset G) :
    ∀ Φ : G → ℂ, (∀ t, Φ t ≠ 0 → t ∈ X) → (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) →
      (∀ t, Φ t ≠ 0 → ∃ s ∈ P, ∃ u ∈ K, t = s + u) → Φ ∈ waveSpan χ X Y L := by
  classical
  refine Finset.induction_on P ?_ ?_
  · intro Φ _ _ hP
    have hz : Φ = 0 := by
      funext t
      by_contra ht
      obtain ⟨s, hs, -⟩ := hP t ht
      simp at hs
    rw [hz]
    exact zero_mem _
  · intro s P0 hsP0 ih Φ hΦX hinv hP
    by_cases hex : ∃ u ∈ K, Φ (s + u) ≠ 0
    · obtain ⟨u0, hu0, hw⟩ := hex
      have hwX : s + u0 ∈ X := hΦX _ hw

      have hconst : ∀ t, t + -(s + u0) ∈ K → Φ t = Φ (s + u0) := by
        intro t ht
        have h1 := hinv _ ht (s + u0)
        rwa [show s + u0 + (t + -(s + u0)) = t by abel] at h1
      have hΨeq : ∀ t, Φ t - Φ (s + u0) * ind K (t + -(s + u0)) =
          if t + -(s + u0) ∈ K then 0 else Φ t := by
        intro t
        by_cases ht : t + -(s + u0) ∈ K
        · rw [if_pos ht, hconst t ht]
          unfold ind
          rw [if_pos ht, mul_one, sub_self]
        · rw [if_neg ht]
          unfold ind
          rw [if_neg ht, mul_zero, sub_zero]
      have hΨ : (fun t => Φ t - Φ (s + u0) * ind K (t + -(s + u0))) ∈ waveSpan χ X Y L := by
        refine ih _ ?_ ?_ ?_
        · intro t ht
          rw [hΨeq] at ht
          split_ifs at ht with h1
          · exact absurd rfl ht
          · exact hΦX t ht
        · intro u hu t
          simp only [hΨeq]
          have hiff : t + u + -(s + u0) ∈ K ↔ t + -(s + u0) ∈ K := by
            rw [show t + u + -(s + u0) = t + -(s + u0) + u by abel]
            exact K.add_mem_cancel_right hu
          rw [if_congr hiff rfl (hinv u hu t)]
        · intro t ht
          rw [hΨeq] at ht
          split_ifs at ht with h1
          · exact absurd rfl ht
          · obtain ⟨s', hs', u, hu, rfl⟩ := hP _ ht
            rcases Finset.mem_insert.mp hs' with rfl | hs'0
            · exact absurd (by
                rw [show s' + u + -(s' + u0) = u + -u0 by abel]
                exact K.add_mem hu (K.neg_mem hu0)) h1
            · exact ⟨s', hs'0, u, hu, rfl⟩
      have htr := trans_mem hK (X.neg_mem hwX)
      have hsum := add_mem hΨ (Submodule.smul_mem _ (Φ (s + u0)) htr)
      convert hsum using 1
      funext t
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · push Not at hex
      refine ih Φ hΦX hinv fun t ht => ?_
      obtain ⟨s', hs', u, hu, rfl⟩ := hP t ht
      rcases Finset.mem_insert.mp hs' with rfl | hs'0
      · exact absurd (hex u hu) ht
      · exact ⟨s', hs'0, u, hu, rfl⟩

theorem exists_intertwiner {V : Type} [AddCommGroup V] [Module ℂ V] (h : IsBichar χ) (hL : L ≤ X) (hL' : L' ≤ Y)
    (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1) (hX : ∀ x ∈ X, (∀ y ∈ L', χ x y = 1) → x ∈ L)
    (hY : ∀ y ∈ Y, (∀ u ∈ L, χ u y = 1) → y ∈ L')
    (dX : ∀ k : ℕ, 0 < k → ∀ x ∈ X, ∃ x' ∈ X, k • x' = x) (dY : ∀ k : ℕ, 0 < k → ∀ y ∈ Y, ∃ y' ∈ Y, k • y' = y)
    (tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : G => k • t)
    (hfin : ∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L, ∃ r ∈ R, ∃ u ∈ L, t = r + k • u)
    (ρ : G → V →ₗ[ℂ] V) (ρX : ∀ x ∈ X, ∀ x' ∈ X, ∀ f, ρ x (ρ x' f) = ρ (x + x') f)
    (ρY : ∀ y ∈ Y, ∀ y' ∈ Y, ∀ f, ρ y (ρ y' f) = ρ (y + y') f)
    (ρXY : ∀ x ∈ X, ∀ y ∈ Y, ∀ f, ρ x (ρ y f) = χ x y • ρ y (ρ x f))
    (f₀ : V) (hf : ∀ u ∈ L, ρ u f₀ = f₀) (hf' : ∀ u ∈ L', ρ u f₀ = f₀) :
    ∃ T : (G → ℂ) →ₗ[ℂ] V, T (ind L) = f₀ ∧ ∀ Φ : G → ℂ, (∀ t, Φ t ≠ 0 → t ∈ X) → ∀ k : ℕ, 0 < k →
      (∀ u ∈ L, ∀ t, Φ (t + k • u) = Φ t) → (∀ t, Φ t ≠ 0 → k • t ∈ L) →
      (∀ x ∈ X, T (fun t => Φ (t + x)) = ρ x (T Φ)) ∧ ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ) := by
  classical
  obtain ⟨T, hT⟩ := exists_map_wave h hL hL' hLL' hY ρ ρX ρY ρXY f₀ hf hf'

  have htrans : ∀ Φ ∈ waveSpan χ X Y L, ∀ x ∈ X, T (fun t => Φ (t + x)) = ρ x (T Φ) := by
    intro Φ hΦ x hx
    unfold waveSpan at hΦ
    induction hΦ using Submodule.span_induction with
    | mem Ψ hΨ =>
      obtain ⟨x₀, hx₀, y₀, hy₀, rfl⟩ := hΨ
      rw [wave_trans, hT _ (X.add_mem hx hx₀) _ hy₀, hT _ hx₀ _ hy₀, ρX x hx x₀ hx₀]
    | zero =>
      have e : (fun t => (0 : G → ℂ) (t + x)) = 0 := rfl
      rw [e]
      simp only [map_zero]
    | add Φ₁ Φ₂ _ _ h₁ h₂ =>
      have e : (fun t => (Φ₁ + Φ₂) (t + x)) = (fun t => Φ₁ (t + x)) + (fun t => Φ₂ (t + x)) := rfl
      rw [e]
      simp only [map_add, h₁, h₂]
    | smul a Φ₁ _ h₁ =>
      have e : (fun t => (a • Φ₁) (t + x)) = a • (fun t => Φ₁ (t + x)) := rfl
      rw [e]
      simp only [map_smul, h₁]

  have hmod : ∀ Φ ∈ waveSpan χ X Y L, ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ) := by
    intro Φ hΦ y hy
    unfold waveSpan at hΦ
    induction hΦ using Submodule.span_induction with
    | mem Ψ hΨ =>
      obtain ⟨x₀, hx₀, y₀, hy₀, rfl⟩ := hΨ
      rw [wave_modul h, map_smul, hT _ hx₀ _ (Y.add_mem hy hy₀), hT _ hx₀ _ hy₀,
        ← ρY y hy y₀ hy₀, ρXY x₀ hx₀ y hy, smul_smul, h.neg_mul, one_smul]
    | zero =>
      have e : (fun t => χ t y * (0 : G → ℂ) t) = 0 := by
        funext t
        simp
      rw [e]
      simp only [map_zero]
    | add Φ₁ Φ₂ _ _ h₁ h₂ =>
      have e : (fun t => χ t y * (Φ₁ + Φ₂) t) =
          (fun t => χ t y * Φ₁ t) + (fun t => χ t y * Φ₂ t) := by
        funext t
        simp [mul_add]
      rw [e]
      simp only [map_add, h₁, h₂]
    | smul a Φ₁ _ h₁ =>
      have e : (fun t => χ t y * (a • Φ₁) t) = a • (fun t => χ t y * Φ₁ t) := by
        funext t
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      simp only [map_smul, h₁]
  refine ⟨T, ?_, fun Φ hΦX k hk hinv hsupp => ?_⟩
  · rw [← wave_zero (χ := χ) (L := L) h, hT 0 X.zero_mem 0 Y.zero_mem, hf 0 L.zero_mem,
      hf 0 L.zero_mem]
  obtain ⟨R, hR, hcov⟩ := hfin k hk
  have hKmem := ind_nsmul_mem h hL hL' hLL' hX (dX k hk) (dY k hk) R hR hcov

  let σ : G → G := fun r => if hr : ∃ s, k • s = r then hr.choose else 0
  let P : Finset G := (hR.toFinset ×ˢ hR.toFinset).image fun p => σ p.1 + p.2
  have hΦ : Φ ∈ waveSpan χ X Y L := by
    refine mem_of_finite_cosets hKmem P Φ hΦX ?_ ?_
    · intro u hu t
      obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.mp hu
      exact hinv w hw t
    · intro t ht
      obtain ⟨r, hr, u, hu, hku⟩ := hcov _ (hsupp t ht)
      have hex : ∃ s, k • s = r := ⟨t - u, by rw [smul_sub, hku, add_sub_cancel_right]⟩
      have hσ : σ r = t - u := by
        apply tf k hk
        simp only [σ, dif_pos hex]
        rw [hex.choose_spec, smul_sub, hku, add_sub_cancel_right]
      obtain ⟨r', hr', u', hu', rfl⟩ := hcov u hu
      refine ⟨σ r + r', Finset.mem_image.mpr ⟨(r, r'), ?_, rfl⟩, k • u',
        AddSubgroup.mem_map.mpr ⟨u', hu', rfl⟩, ?_⟩
      · simp [hr, hr']
      · rw [hσ]
        abel
  exact ⟨fun x hx => htrans Φ hΦ x hx, fun y hy => hmod Φ hΦ y hy⟩

end GlobalTheory.PlaceModel

end
