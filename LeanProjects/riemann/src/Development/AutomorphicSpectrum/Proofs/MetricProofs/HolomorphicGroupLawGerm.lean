import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsConstAddEquivOfRangeEq
open Set

namespace GlobalTheory.CompanionTheory.Ar.Flat

def IsHolMarkingOn {n g : ℕ} {Λ : Type} [AddCommGroup Λ]
    (Γ : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)) (Q : (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℝ)
    (e : Λ → Λ → ℝ) (U : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))) : Prop :=
  (∀ x, DifferentiableOn ℂ (fun b => P b x) U) ∧
    ∀ b ∈ U, Function.Injective (P b) ∧ (P b).range = Γ b ∧ ∀ x y, Q b (P b x) (P b y) = e x y

section
variable {n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Countable Λ]
  {Γ : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)} {Q : (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℝ}
  {e : Λ → Λ → ℝ}

omit [Countable Λ] in
theorem IsHolMarkingOn.mono {U V : Set (Fin n → ℂ)} {P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))}
    (h : IsHolMarkingOn Γ Q e U P) (hVU : V ⊆ U) : IsHolMarkingOn Γ Q e V P :=
  ⟨fun x => (h.1 x).mono hVU, fun b hb => h.2 b (hVU hb)⟩

theorem IsHolMarkingOn.exists_twist {U V : Set (Fin n → ℂ)} (hU : IsOpen U) (hV : IsOpen V)
    (hc : IsPreconnected (U ∩ V)) (hne : (U ∩ V).Nonempty)
    {P P' : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))}
    (h : IsHolMarkingOn Γ Q e U P) (h' : IsHolMarkingOn Γ Q e V P') :
    ∃ R : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), IsHolMarkingOn Γ Q e V R ∧
      ∀ b ∈ U ∩ V, R b = P b := by
  obtain ⟨T, hT⟩ := exists_const_addEquiv_of_range_eq n g Λ Λ (U ∩ V) (hU.inter hV) hc hne P P'
    (fun x => (h.1 x).mono inter_subset_left) (fun x => (h'.1 x).mono inter_subset_right)
    (fun b hb => ⟨(h.2 b hb.1).1, (h'.2 b hb.2).1, by
      rw [(h.2 b hb.1).2.1, (h'.2 b hb.2).2.1]⟩)
  have hR : ∀ b ∈ U ∩ V, ∀ x, P' b (T.symm x) = P b x := fun b hb x => by
    rw [hT b hb, T.apply_symm_apply]
  refine ⟨fun b => (P' b).comp T.symm.toAddMonoidHom, ⟨fun x => h'.1 (T.symm x), ?_⟩, ?_⟩
  · intro b hb
    obtain ⟨hi, hr, hq⟩ := h'.2 b hb
    refine ⟨hi.comp T.symm.injective, ?_, ?_⟩
    · rw [← hr]
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨T.symm x, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨T x, by simp⟩
    · intro x y
      obtain ⟨c, hc'⟩ := hne
      have h1 := (h.2 c hc'.1).2.2 x y
      have h2 := (h'.2 c hc'.2).2.2 (T.symm x) (T.symm y)
      rw [hR c hc' x, hR c hc' y, h1] at h2
      simpa using (hq (T.symm x) (T.symm y)).trans h2.symm
  · intro b hb
    ext1 x
    exact hR b hb x

theorem IsHolMarkingOn.exists_glue {U V : Set (Fin n → ℂ)} (hU : IsOpen U) (hV : IsOpen V)
    (hc : IsPreconnected (U ∩ V)) (hne : (U ∩ V).Nonempty)
    {P P' : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))}
    (h : IsHolMarkingOn Γ Q e U P) (h' : IsHolMarkingOn Γ Q e V P') :
    ∃ R, IsHolMarkingOn Γ Q e (U ∪ V) R := by
  classical
  obtain ⟨R, hR, hRP⟩ := h.exists_twist hU hV hc hne h'
  have eU : ∀ b ∈ U, (if b ∈ U then P b else R b) = P b := fun b hb => if_pos hb
  have eV : ∀ b ∈ V, (if b ∈ U then P b else R b) = R b := fun b hb => by
    by_cases hbU : b ∈ U
    · rw [if_pos hbU, hRP b ⟨hbU, hb⟩]
    · rw [if_neg hbU]
  refine ⟨fun b => if b ∈ U then P b else R b, fun x => ?_, ?_⟩
  · have d1 : DifferentiableOn ℂ (fun b => (if b ∈ U then P b else R b) x) U :=
      (h.1 x).congr fun b hb => by rw [eU b hb]
    have d2 : DifferentiableOn ℂ (fun b => (if b ∈ U then P b else R b) x) V :=
      (hR.1 x).congr fun b hb => by rw [eV b hb]
    rintro b (hb | hb)
    · exact ((d1 b hb).differentiableAt (hU.mem_nhds hb)).differentiableWithinAt
    · exact ((d2 b hb).differentiableAt (hV.mem_nhds hb)).differentiableWithinAt
  · rintro b (hb | hb)
    · simpa only [eU b hb] using h.2 b hb
    · simpa only [eV b hb] using hR.2 b hb

theorem IsHolMarkingOn.eq_of_eq_at {W : Set (Fin n → ℂ)} (hW : IsOpen W) (hc : IsPreconnected W)
    {P P' : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))}
    (h : IsHolMarkingOn Γ Q e W P) (h' : IsHolMarkingOn Γ Q e W P')
    {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ W) (h0 : P b₀ = P' b₀) : ∀ b ∈ W, P b = P' b := by
  obtain ⟨T, hT⟩ := exists_const_addEquiv_of_range_eq n g Λ Λ W hW hc ⟨b₀, hb₀⟩ P P' h.1 h'.1
    (fun b hb => ⟨(h.2 b hb).1, (h'.2 b hb).1, by rw [(h.2 b hb).2.1, (h'.2 b hb).2.1]⟩)
  have hid : ∀ x, T x = x := fun x => (h.2 b₀ hb₀).1 (by rw [← hT b₀ hb₀, h0])
  intro b hb
  ext1 x
  rw [hT b hb, hid]

theorem exists_marking_of_convex_family {B : Set (Fin n → ℂ)} {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ B)
    (H : ∀ b ∈ B, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ Convex ℝ U ∧ U ⊆ B ∧ b₀ ∈ U ∧ b ∈ U ∧
      ∃ P, IsHolMarkingOn Γ Q e U P) :
    ∃ P, IsHolMarkingOn Γ Q e B P := by
  obtain ⟨U₀, hU₀, hC₀, -, hbU₀, -, P₀, hP₀⟩ := H b₀ hb₀
  have H' : ∀ b ∈ B, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ Convex ℝ U ∧ U ⊆ B ∧ b₀ ∈ U ∧ b ∈ U ∧
      ∃ R, IsHolMarkingOn Γ Q e U R ∧ R b₀ = P₀ b₀ := by
    intro b hb
    obtain ⟨U, hU, hC, hUB, h0, h1, P, hP⟩ := H b hb
    obtain ⟨R, hR, hRP⟩ := hP₀.exists_twist hU₀ hU (hC₀.inter hC).isPreconnected ⟨b₀, hbU₀, h0⟩ hP
    exact ⟨U, hU, hC, hUB, h0, h1, R, hR, hRP b₀ ⟨hbU₀, h0⟩⟩
  choose! U hU hC hUB h0 h1 R hR hRb using H'
  have key : ∀ b ∈ B, ∀ c ∈ U b, R c c = R b c := fun b hb c hcb => by
    have hc : c ∈ B := hUB b hb hcb
    exact ((hR c hc).mono inter_subset_left).eq_of_eq_at ((hU c hc).inter (hU b hb))
      ((hC c hc).inter (hC b hb)).isPreconnected ((hR b hb).mono inter_subset_right)
      ⟨h0 c hc, h0 b hb⟩ ((hRb c hc).trans (hRb b hb).symm) c ⟨h1 c hc, hcb⟩
  refine ⟨fun b => R b b, fun x b hb => ?_, fun b hb => (hR b hb).2 b (h1 b hb)⟩
  have hn := (hU b hb).mem_nhds (h1 b hb)
  have hev : (fun c => R c c x) =ᶠ[nhds b] fun c => R b c x := by
    filter_upwards [hn] with c hc
    rw [key b hb c hc]
  exact (((hR b hb).1 x b (h1 b hb)).differentiableAt hn).congr_of_eventuallyEq hev
    |>.differentiableWithinAt

theorem exists_marking_tube {B : Set (Fin n → ℂ)} (hconv : Convex ℝ B)
    (H : ∀ b₀ ∈ B, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ b₀ ∈ N ∧ N ⊆ B ∧
      ∃ P, IsHolMarkingOn Γ Q e N P)
    {a b : Fin n → ℂ} (ha : a ∈ B) (hb : b ∈ B) :
    ∃ U : Set (Fin n → ℂ), IsOpen U ∧ Convex ℝ U ∧ U ⊆ B ∧ a ∈ U ∧ b ∈ U ∧
      ∃ P, IsHolMarkingOn Γ Q e U P := by
  let γ : ℝ →ᵃ[ℝ] (Fin n → ℂ) := AffineMap.lineMap a b
  have hγ : Continuous γ := by
    have : (γ : ℝ → Fin n → ℂ) = fun t => t • (b - a) + a :=
      funext fun t => AffineMap.lineMap_apply_module' a b t
    rw [this]
    fun_prop
  have hγ0 : γ 0 = a := AffineMap.lineMap_apply_zero a b
  have hγ1 : γ 1 = b := AffineMap.lineMap_apply_one a b
  have hmem : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ B := fun r hr =>
    hconv.segment_subset ha hb (by rw [segment_eq_image_lineMap]; exact ⟨r, hr, rfl⟩)
  let ι := {N : Set (Fin n → ℂ) // IsOpen N ∧ N ⊆ B ∧ ∃ P, IsHolMarkingOn Γ Q e N P}
  let c : ι → Set unitInterval := fun N => (fun s : unitInterval => γ s) ⁻¹' N.1
  obtain ⟨t, ht0, hmono, ⟨m, hm⟩, hcov⟩ := exists_monotone_Icc_subset_open_cover_unitInterval
    (c := c) (fun N => N.2.1.preimage (hγ.comp continuous_subtype_val)) (fun s _ => by
      obtain ⟨N, h1, h2, h3, h4⟩ := H _ (hmem s s.2)
      exact mem_iUnion.2 ⟨⟨N, h1, h3, h4⟩, h2⟩)
  have claim : ∀ k, ∃ δ : ℝ, 0 < δ ∧ Metric.thickening δ (γ '' Icc 0 (t k : ℝ)) ⊆ B ∧
      ∃ P, IsHolMarkingOn Γ Q e (Metric.thickening δ (γ '' Icc 0 (t k : ℝ))) P := by
    intro k
    induction k with
    | zero =>
      obtain ⟨N, hN, haN, hNB, P, hP⟩ := H a ha
      have hsub : γ '' Icc 0 (t 0 : ℝ) ⊆ N := by
        rintro _ ⟨r, hr, rfl⟩
        have hr0 : r = 0 := le_antisymm (by simpa [ht0] using hr.2) hr.1
        rw [hr0, hγ0]
        exact haN
      obtain ⟨δ, hδ, hth⟩ := (isCompact_Icc.image hγ).exists_thickening_subset_open hN hsub
      exact ⟨δ, hδ, hth.trans hNB, P, hP.mono hth⟩
    | succ k ih =>
      obtain ⟨δ₁, hδ₁, hB₁, P₁, hP₁⟩ := ih
      obtain ⟨N, hN⟩ := hcov k
      obtain ⟨hNo, hNB, P₂, hP₂⟩ := N.2
      have hle : (t k : ℝ) ≤ t (k + 1) := hmono (Nat.le_succ k)
      have h0 : (0 : ℝ) ≤ t k := (t k).2.1
      have hsub : γ '' Icc (t k : ℝ) (t (k + 1)) ⊆ N.1 := by
        rintro _ ⟨r, hr, rfl⟩
        have hr' : r ∈ Icc (0 : ℝ) 1 := ⟨h0.trans hr.1, hr.2.trans (t (k + 1)).2.2⟩
        exact hN (show (⟨r, hr'⟩ : unitInterval) ∈ Icc (t k) (t (k + 1)) from ⟨hr.1, hr.2⟩)
      obtain ⟨δ₂, hδ₂, hth⟩ := (isCompact_Icc.image hγ).exists_thickening_subset_open hNo hsub
      have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
      have hA : Metric.thickening (min δ₁ δ₂) (γ '' Icc 0 (t k : ℝ)) ⊆
          Metric.thickening δ₁ (γ '' Icc 0 (t k : ℝ)) :=
        Metric.thickening_mono (min_le_left _ _) _
      have hC : Metric.thickening (min δ₁ δ₂) (γ '' Icc (t k : ℝ) (t (k + 1))) ⊆ N.1 :=
        (Metric.thickening_mono (min_le_right _ _) _).trans hth
      have hKs : γ '' Icc 0 (t (k + 1) : ℝ) =
          γ '' Icc 0 (t k : ℝ) ∪ γ '' Icc (t k : ℝ) (t (k + 1)) := by
        rw [← image_union, Icc_union_Icc_eq_Icc h0 hle]
      have hconvA := ((convex_Icc (0 : ℝ) (t k)).affine_image γ).thickening (min δ₁ δ₂)
      have hconvC := ((convex_Icc (t k : ℝ) (t (k + 1))).affine_image γ).thickening (min δ₁ δ₂)
      have hpt : γ (t k) ∈ Metric.thickening (min δ₁ δ₂) (γ '' Icc 0 (t k : ℝ)) ∩
          Metric.thickening (min δ₁ δ₂) (γ '' Icc (t k : ℝ) (t (k + 1))) :=
        ⟨Metric.self_subset_thickening hδ _ ⟨_, ⟨h0, le_rfl⟩, rfl⟩,
          Metric.self_subset_thickening hδ _ ⟨_, ⟨le_rfl, hle⟩, rfl⟩⟩
      obtain ⟨R, hR⟩ := (hP₁.mono hA).exists_glue (P' := P₂) Metric.isOpen_thickening
        Metric.isOpen_thickening (hconvA.inter hconvC).isPreconnected ⟨_, hpt⟩ (hP₂.mono hC)
      refine ⟨min δ₁ δ₂, hδ, ?_, R, ?_⟩
      · rw [hKs, Metric.thickening_union]
        exact union_subset (hA.trans hB₁) (hC.trans hNB)
      · rw [hKs, Metric.thickening_union]
        exact hR
  obtain ⟨δ, hδ, hδB, P, hP⟩ := claim m
  have htm : (t m : ℝ) = 1 := by rw [hm m le_rfl]; rfl
  rw [htm] at hδB hP
  exact ⟨_, Metric.isOpen_thickening, ((convex_Icc (0 : ℝ) 1).affine_image γ).thickening δ, hδB,
    Metric.self_subset_thickening hδ _ ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩,
    Metric.self_subset_thickening hδ _ ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩, P, hP⟩

end

theorem exists_global_marking_of_local : ∀ (n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Countable Λ] (B : Set (Fin n → ℂ)), IsOpen B → Convex ℝ B → ∀ (Γ : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)) (Q : (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℝ) (e : Λ → Λ → ℝ), (∀ b₀ ∈ B, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ b₀ ∈ N ∧ N ⊆ B ∧ ∃ P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun b => P b x) N) ∧ ∀ b ∈ N, Function.Injective (P b) ∧ (P b).range = Γ b ∧ ∀ x y, Q b (P b x) (P b y) = e x y) → ∃ P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun b => P b x) B) ∧ ∀ b ∈ B, Function.Injective (P b) ∧ (P b).range = Γ b ∧ ∀ x y, Q b (P b x) (P b y) = e x y := by
  intro n g Λ _ _ B _ hconv Γ Q e H
  rcases B.eq_empty_or_nonempty with rfl | ⟨b₀, hb₀⟩
  · exact ⟨fun _ => 0, fun x => by simp, by simp⟩
  · have H' : ∀ b₀ ∈ B, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ b₀ ∈ N ∧ N ⊆ B ∧
        ∃ P, IsHolMarkingOn Γ Q e N P := fun b hb => by
      obtain ⟨N, h1, h2, h3, P, h4, h5⟩ := H b hb
      exact ⟨N, h1, h2, h3, P, h4, h5⟩
    obtain ⟨P, hP⟩ := exists_marking_of_convex_family hb₀
      (fun b hb => exists_marking_tube hconv H' hb₀ hb)
    exact ⟨P, hP.1, hP.2⟩

end GlobalTheory.CompanionTheory.Ar.Flat
