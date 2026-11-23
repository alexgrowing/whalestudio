import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreDefs

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem words {M : Type} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ (Module.End ℂ M))
    (hS : ∀ E ∈ S, ∀ F ∈ S, E * F - F * E ∈ S) (L : Set (Module.End ℂ M)) (hL : L ⊆ S) (z : M)
    (hz : ∀ E ∈ S, ∃ F ∈ Submodule.span ℂ L, ∃ c : ℂ, E z = F z + c • z)
    (W : Submodule ℂ M) (hW : W = sInf {N | z ∈ N ∧ ∀ F ∈ L, ∀ x ∈ N, F x ∈ N}) :
    z ∈ W ∧ (∀ E ∈ S, ∀ x ∈ W, E x ∈ W) ∧ W = Submodule.span ℂ {z} ⊔ ⨆ F ∈ L, W.map F := by
  have hz0 : z ∈ W := by rw [hW]; exact Submodule.mem_sInf.2 fun N hN => hN.1
  have hLW : ∀ F ∈ L, ∀ x ∈ W, F x ∈ W := by
    intro F hF x hx
    rw [hW] at hx ⊢
    exact Submodule.mem_sInf.2 fun N hN => hN.2 F hF x (Submodule.mem_sInf.1 hx N hN)
  have hmin : ∀ N : Submodule ℂ M, z ∈ N → (∀ F ∈ L, ∀ x ∈ N, F x ∈ N) → W ≤ N := by
    intro N h1 h2
    rw [hW]
    exact sInf_le ⟨h1, h2⟩
  have hspan : ∀ F ∈ Submodule.span ℂ L, F z ∈ W := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F hF => exact hLW F hF z hz0
    | zero => simp
    | add F G _ _ h1 h2 => exact W.add_mem h1 h2
    | smul c F _ h1 => exact W.smul_mem c h1
  refine ⟨hz0, ?_, ?_⟩
  · have hle : W ≤ W ⊓ ⨅ E ∈ S, W.comap E := by
      refine hmin _ ?_ ?_
      · refine ⟨hz0, ?_⟩
        simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap]
        intro E hE
        obtain ⟨F, hF, c, hc⟩ := hz E hE
        rw [hc]
        exact W.add_mem (hspan F hF) (W.smul_mem c hz0)
      · intro F hF x hx
        obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
        simp only [Submodule.mem_iInf, Submodule.mem_comap] at hx2
        refine Submodule.mem_inf.2 ⟨hLW F hF x hx1, ?_⟩
        simp only [Submodule.mem_iInf, Submodule.mem_comap]
        intro E hE
        have e : E (F x) = F (E x) + (E * F - F * E) x := by
          simp [Module.End.mul_apply]
        rw [e]
        exact W.add_mem (hLW F hF _ (hx2 E hE)) (hx2 _ (hS E hE F (hL hF)))
    intro E hE x hx
    have h2 := (Submodule.mem_inf.1 (hle hx)).2
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at h2
    exact h2 E hE
  · have hge : Submodule.span ℂ {z} ⊔ ⨆ F ∈ L, W.map F ≤ W := by
      refine sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hz0) (iSup₂_le fun F hF => ?_)
      rintro _ ⟨x, hx, rfl⟩
      exact hLW F hF x hx
    refine le_antisymm (hmin _ ?_ ?_) hge
    · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self z)
    · intro F hF x hx
      refine Submodule.mem_sup_right ?_
      exact (le_iSup₂_of_le (f := fun F (_ : F ∈ L) => W.map F) F hF le_rfl) ⟨x, hge hx, rfl⟩

variable {r s : ℕ}

theorem sb_refl (a : Ix r s) : sameBlock a a := by cases a <;> trivial

theorem sb_symm {a b : Ix r s} (h : sameBlock a b) : sameBlock b a := by
  cases a <;> cases b <;> simp_all [sameBlock]

theorem sb_trans {a b c : Ix r s} (h : sameBlock a b) (h' : sameBlock b c) : sameBlock a c := by
  cases a <;> cases b <;> cases c <;> simp_all [sameBlock]

theorem sb_of_pos {a b : Ix r s} (h : posC a b) : sameBlock a b := by
  cases a <;> cases b <;> simp_all [sameBlock, posC]

theorem pos_irrefl (a : Ix r s) : ¬ posC a a := by cases a <;> simp [posC]

theorem pos_asymm {a b : Ix r s} (h : posC a b) : ¬ posC b a := by
  cases a <;> cases b <;> simp only [posC] at h ⊢
  · exact not_lt.2 h.le
  · exact not_lt.2 h.le

theorem sb_tri {a b : Ix r s} (h : sameBlock a b) : a = b ∨ posC a b ∨ posC b a := by
  cases a <;> cases b <;> simp only [sameBlock, posC, Sum.inl.injEq, Sum.inr.injEq] at h ⊢
  · rename_i i j
    rcases lt_trichotomy i j with h | h | h <;> simp [h]
  · rename_i i j
    rcases lt_trichotomy i j with h | h | h <;> simp [h]

theorem eab_mul (a b c d : Ix r s) : Eab a b * Eab c d = if b = c then Eab a d else 0 := by
  unfold Eab
  split_ifs with h
  · subst h; simp
  · exact Matrix.single_mul_single_of_ne _ _ _ _ h _

theorem hw_comm {M : Type} [AddCommGroup M] [Module ℂ M] {ρ : Ix r s → Ix r s → Module.End ℂ M}
    (hρ : GlK ρ) {μ : Ix r s → ℚ} {f : M} (hf : HwK ρ μ f) {a b : Ix r s} (hab : posC a b) :
    ρ a b (ρ b a f) = ((μ a - μ b : ℚ) : ℂ) • f := by
  have h := LinearMap.congr_fun (hρ a b b a (sb_of_pos hab) (sb_symm (sb_of_pos hab))) f
  simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply, hf.2 a b hab, map_zero, sub_zero,
    hf.1] at h
  rw [h, ← sub_smul]
  push_cast
  rfl

theorem norm_low {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    {ρ : Ix r s → Ix r s → Module.End ℂ A} (hadj : AdjK ρ) (hρ : GlK ρ) {μ : Ix r s → ℚ} {f : A}
    (hf : HwK ρ μ f) {a b : Ix r s} (hab : posC a b) :
    ‖ρ b a f‖ ^ 2 = ((μ a - μ b : ℚ) : ℝ) * ‖f‖ ^ 2 := by
  have h := hadj b a (sb_symm (sb_of_pos hab)) f (ρ b a f)
  rw [hw_comm hρ hf hab, inner_smul_right, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ((‖ρ b a f‖ ^ 2 : ℝ) : ℂ) = ((((μ a - μ b : ℚ) : ℝ) * ‖f‖ ^ 2 : ℝ) : ℂ) := by
    push_cast at h ⊢
    exact h
  exact_mod_cast h2

theorem cas_comm {M : Type} [AddCommGroup M] [Module ℂ M] {ρ : Ix r s → Ix r s → Module.End ℂ M}
    (hρ : GlK ρ) {a b : Ix r s} (hab : sameBlock a b) : casK ρ * ρ a b = ρ a b * casK ρ := by
  have key : ∀ c d : Ix r s,
      ρ a b * (if sameBlock c d then ρ c d * ρ d c else 0) - (if sameBlock c d then ρ c d * ρ d c else 0) * ρ a b =
      ((if b = c then (if sameBlock a d then ρ a d * ρ d b else 0) else 0) -
        (if a = d then (if sameBlock c a then ρ c b * ρ a c else 0) else 0)) +
      ((if b = d then (if sameBlock c a then ρ c b * ρ a c else 0) else 0) -
        (if a = c then (if sameBlock a d then ρ a d * ρ d b else 0) else 0)) := by
    intro c d
    by_cases hcd : sameBlock c d
    · have e : ρ a b * (ρ c d * ρ d c) - (ρ c d * ρ d c) * ρ a b =
          (ρ a b * ρ c d - ρ c d * ρ a b) * ρ d c + ρ c d * (ρ a b * ρ d c - ρ d c * ρ a b) := by
        noncomm_ring
      rw [if_pos hcd, e, hρ a b c d hab hcd, hρ a b d c hab (sb_symm hcd), sub_mul, mul_sub]
      congr 2
      · by_cases h : b = c
        · subst h; simp [sb_trans hab hcd]
        · simp [h]
      · by_cases h : a = d
        · subst h; simp [hcd]
        · simp [h, Ne.symm h]
      · by_cases h : b = d
        · subst h; simp [sb_trans hcd (sb_symm hab)]
        · simp [h]
      · by_cases h : a = c
        · subst h; simp [hcd]
        · simp [h, Ne.symm h]
    · have t1 : (if b = c then (if sameBlock a d then ρ a d * ρ d b else 0) else 0) = 0 := by
        split_ifs with h1 h2
        · subst h1; exact absurd (sb_trans (sb_symm hab) h2) hcd
        all_goals rfl
      have t2 : (if a = d then (if sameBlock c a then ρ c b * ρ a c else 0) else 0) = 0 := by
        split_ifs with h1 h2
        · subst h1; exact absurd h2 hcd
        all_goals rfl
      have t3 : (if b = d then (if sameBlock c a then ρ c b * ρ a c else 0) else 0) = 0 := by
        split_ifs with h1 h2
        · subst h1; exact absurd (sb_trans h2 hab) hcd
        all_goals rfl
      have t4 : (if a = c then (if sameBlock a d then ρ a d * ρ d b else 0) else 0) = 0 := by
        split_ifs with h1 h2
        · subst h1; exact absurd h2 hcd
        all_goals rfl
      rw [t1, t2, t3, t4, if_neg hcd]
      simp
  have h0 : ρ a b * casK ρ - casK ρ * ρ a b = 0 := by
    unfold casK
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, key]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_comm (f := fun c d => if b = c then (if sameBlock a d then ρ a d * ρ d b else 0) else 0),
      Finset.sum_comm (f := fun c d => if a = c then (if sameBlock a d then ρ a d * ρ d b else 0) else 0)]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    abel
  exact (sub_eq_zero.1 h0).symm

theorem cas_hw {M : Type} [AddCommGroup M] [Module ℂ M] {ρ : Ix r s → Ix r s → Module.End ℂ M}
    (hρ : GlK ρ) {μ : Ix r s → ℚ} {f : M} (hf : HwK ρ μ f) : casK ρ f = ((casW μ : ℚ) : ℂ) • f := by
  have key : ∀ a b : Ix r s, (if sameBlock a b then ρ a b * ρ b a else 0) f =
      (((if a = b then μ a ^ 2 else 0) + (if posC a b then μ a - μ b else 0) : ℚ) : ℂ) • f := by
    intro a b
    by_cases hab : sameBlock a b
    · rw [if_pos hab]
      rcases sb_tri hab with h | h | h
      · subst h
        rw [if_pos rfl, if_neg (pos_irrefl a), Module.End.mul_apply, hf.1 a, map_smul, hf.1 a, smul_smul]
        congr 1
        push_cast
        ring
      · rw [if_neg (fun e : a = b => pos_irrefl b (by subst e; exact h)), if_pos h, Module.End.mul_apply, hw_comm hρ hf h, zero_add]
      · rw [if_neg (fun e : a = b => pos_irrefl b (by subst e; exact h)), if_neg (pos_asymm h), Module.End.mul_apply, hf.2 b a h]
        simp
    · rw [if_neg hab, if_neg (fun e : a = b => hab (by subst e; exact sb_refl a)), if_neg (fun h => hab (sb_of_pos h))]
      simp
  unfold casK casW
  simp only [LinearMap.sum_apply, key, ← Finset.sum_smul]
  congr 1
  simp only [← Rat.cast_sum, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem self_mem_cycK {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Ix r s → Ix r s → Module.End ℂ M) (f : M) :
    f ∈ cycK ρ f := by
  exact Submodule.mem_sInf.2 fun N hN => hN.1

theorem kSt_cycK {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Ix r s → Ix r s → Module.End ℂ M) (f : M) :
    KSt ρ (cycK ρ f) := by
  intro a b hab x hx
  exact Submodule.mem_sInf.2 fun N hN => hN.2 a b hab x (Submodule.mem_sInf.1 hx N hN)

theorem cas_cyc {M : Type} [AddCommGroup M] [Module ℂ M] {ρ : Ix r s → Ix r s → Module.End ℂ M}
    (hρ : GlK ρ) {μ : Ix r s → ℚ} {f : M} (hf : HwK ρ μ f) :
    ∀ x ∈ cycK ρ f, casK ρ x = ((casW μ : ℚ) : ℂ) • x := by
  intro x hx
  have hle : cycK ρ f ≤ LinearMap.ker (casK ρ - ((casW μ : ℚ) : ℂ) • 1) := by
    refine sInf_le ⟨?_, ?_⟩
    · simp [LinearMap.mem_ker, cas_hw hρ hf]
    · intro a b hab y hy
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        sub_eq_zero] at hy ⊢
      rw [← Module.End.mul_apply, cas_comm hρ hab, Module.End.mul_apply, hy, map_smul]
  have h := hle hx
  simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero] using h

theorem dom_of_hw {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] {ρ : Ix r s → Ix r s → Module.End ℂ A}
    (hadj : AdjK ρ) (hρ : GlK ρ) {μ : Ix r s → ℚ} {f : A} (hf : HwK ρ μ f) (h0 : f ≠ 0) : Dom μ := by
  intro a b hab
  have h := norm_low hadj hρ hf hab
  have hp : 0 < ‖f‖ ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ ((μ a - μ b : ℚ) : ℝ) * ‖f‖ ^ 2 := h ▸ sq_nonneg _
  have h3 : (0 : ℝ) ≤ ((μ a - μ b : ℚ) : ℝ) := nonneg_of_mul_nonneg_left h2 hp
  have h4 : (0 : ℚ) ≤ μ a - μ b := by exact_mod_cast h3
  linarith

theorem low_kill {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] {ρ : Ix r s → Ix r s → Module.End ℂ A}
    (hadj : AdjK ρ) (hρ : GlK ρ) {μ : Ix r s → ℚ} {f : A} (hf : HwK ρ μ f) {a b : Ix r s} (hab : posC a b)
    (hμ : μ a = μ b) : ρ b a f = 0 := by
  have h := norm_low hadj hρ hf hab
  rw [hμ] at h
  simpa using h

theorem cyc_irred {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A] {ρ : Ix r s → Ix r s → Module.End ℂ A}
    (hadj : AdjK ρ) (hρ : GlK ρ) {μ : Ix r s → ℚ} {f : A} (hf : HwK ρ μ f)
    (N : Submodule ℂ A) (hN : N ≤ cycK ρ f) (hK : KSt ρ N) : N = ⊥ ∨ N = cycK ρ f := by
  let S : Submodule ℂ (Module.End ℂ A) := Submodule.span ℂ {E | ∃ a b, sameBlock a b ∧ E = ρ a b}
  let L : Set (Module.End ℂ A) := {E | ∃ a b, posC a b ∧ E = ρ b a}
  have hmem : ∀ a b, sameBlock a b → ρ a b ∈ S := fun a b h => Submodule.subset_span ⟨a, b, h, rfl⟩
  have hS : ∀ E ∈ S, ∀ F ∈ S, E * F - F * E ∈ S := by
    intro E hE F hF
    induction hE using Submodule.span_induction with
    | mem E hE =>
      obtain ⟨a, b, hab, rfl⟩ := hE
      induction hF using Submodule.span_induction with
      | mem F hF =>
        obtain ⟨c, d, hcd, rfl⟩ := hF
        rw [hρ a b c d hab hcd]
        refine S.sub_mem ?_ ?_
        · split_ifs with h
          · subst h; exact hmem _ _ (sb_trans hab hcd)
          · exact S.zero_mem
        · split_ifs with h
          · subst h; exact hmem _ _ (sb_trans hcd hab)
          · exact S.zero_mem
      | zero => simp
      | add F G _ _ h1 h2 =>
        have := S.add_mem h1 h2
        convert this using 1
        noncomm_ring
      | smul c F _ h1 =>
        have := S.smul_mem c h1
        convert this using 1
        simp [smul_sub]
    | zero => simp
    | add E G _ _ h1 h2 =>
      have := S.add_mem h1 h2
      convert this using 1
      noncomm_ring
    | smul c E _ h1 =>
      have := S.smul_mem c h1
      convert this using 1
      simp [smul_sub]
  have hL : L ⊆ S := by
    rintro _ ⟨a, b, hab, rfl⟩
    exact hmem _ _ (sb_symm (sb_of_pos hab))
  have hz : ∀ E ∈ S, ∃ F ∈ Submodule.span ℂ L, ∃ c : ℂ, E f = F f + c • f := by
    intro E hE
    induction hE using Submodule.span_induction with
    | mem E hE =>
      obtain ⟨a, b, hab, rfl⟩ := hE
      rcases sb_tri hab with h | h | h
      · subst h
        exact ⟨0, Submodule.zero_mem _, ((μ a : ℚ) : ℂ), by rw [hf.1 a]; simp⟩
      · exact ⟨0, Submodule.zero_mem _, 0, by rw [hf.2 a b h]; simp⟩
      · exact ⟨ρ a b, Submodule.subset_span ⟨b, a, h, rfl⟩, 0, by simp⟩
    | zero => exact ⟨0, Submodule.zero_mem _, 0, by simp⟩
    | add E G _ _ h1 h2 =>
      obtain ⟨F1, hF1, c1, e1⟩ := h1
      obtain ⟨F2, hF2, c2, e2⟩ := h2
      refine ⟨F1 + F2, Submodule.add_mem _ hF1 hF2, c1 + c2, ?_⟩
      simp only [LinearMap.add_apply, e1, e2, add_smul]
      abel
    | smul c E _ h1 =>
      obtain ⟨F1, hF1, c1, e1⟩ := h1
      refine ⟨c • F1, Submodule.smul_mem _ _ hF1, c * c1, ?_⟩
      simp only [LinearMap.smul_apply, e1, smul_add, smul_smul]
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℂ A, W = sInf {N | f ∈ N ∧ ∀ F ∈ L, ∀ x ∈ N, F x ∈ N} := ⟨_, rfl⟩
  obtain ⟨hfW, hSW, hWeq⟩ := words S hS L hL f hz W hW
  have hcW : cycK ρ f ≤ W := sInf_le ⟨hfW, fun a b hab x hx => hSW _ (hmem a b hab) x hx⟩
  have hKo : KSt ρ Nᗮ := by
    intro a b hab x hx
    rw [Submodule.mem_orthogonal'] at hx ⊢
    intro u hu
    rw [hadj a b hab]
    exact hx _ (hK b a (sb_symm hab) u hu)
  obtain ⟨y, hy, z, hz', hyz⟩ := Submodule.mem_sup.1
    (show f ∈ N ⊔ Nᗮ by rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]; exact Submodule.mem_top)
  have hyk : ∀ a b, posC a b → ρ a b y = 0 := by
    intro a b hab
    have h1 : ρ a b y ∈ N := hK a b (sb_of_pos hab) y hy
    have h2 : ρ a b y ∈ Nᗮ := by
      have e : ρ a b y = - ρ a b z := by
        have := hf.2 a b hab
        rw [← hyz, map_add] at this
        exact eq_neg_of_add_eq_zero_left this
      rw [e]
      exact Nᗮ.neg_mem (hKo a b (sb_of_pos hab) z hz')
    exact inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal h1 h2)
  have hw0 : ⟪f, f⟫_ℂ • y - ⟪f, y⟫_ℂ • f = 0 := by
    set w := ⟪f, f⟫_ℂ • y - ⟪f, y⟫_ℂ • f with hw
    have hwW : w ∈ W := W.sub_mem (W.smul_mem _ (hcW (hN hy))) (W.smul_mem _ hfW)
    have hle : W ≤ (Submodule.span ℂ {w})ᗮ := by
      rw [hWeq]
      refine sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 ?_) (iSup₂_le ?_)
      · rw [Submodule.mem_orthogonal_singleton_iff_inner_left, hw, inner_sub_right, inner_smul_right,
          inner_smul_right]
        ring
      · rintro _ ⟨a, b, hab, rfl⟩ _ ⟨x, _, rfl⟩
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left, hadj b a (sb_symm (sb_of_pos hab)), hw,
          map_sub, map_smul, map_smul, hyk a b hab, hf.2 a b hab]
        simp
    have := hle hwW
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at this
    exact inner_self_eq_zero.1 this
  by_cases hfy : ⟪f, y⟫_ℂ = 0
  · left
    have hy0 : y = 0 := by
      rw [← hyz, inner_add_left, Submodule.inner_left_of_mem_orthogonal hy hz', add_zero] at hfy
      exact inner_self_eq_zero.1 hfy
    have hfo : f ∈ Nᗮ := by rw [← hyz, hy0, zero_add]; exact hz'
    have hle : cycK ρ f ≤ Nᗮ := sInf_le ⟨hfo, hKo⟩
    rw [eq_bot_iff]
    intro u hu
    exact (Submodule.mem_bot ℂ).2
      (inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hu (hle (hN hu))))
  · right
    have hfN : f ∈ N := by
      have h1 : ⟪f, y⟫_ℂ • f ∈ N := by
        rw [← sub_eq_zero.1 hw0]
        exact N.smul_mem _ hy
      exact (N.smul_mem_iff hfy).1 h1
    exact le_antisymm hN (sInf_le ⟨hfN, hK⟩)

theorem glK_units {M : Type} [AddCommGroup M] [Module ℂ M] {act : Mat r s →ₗ[ℂ] Module.End ℂ M}
    (h : IsLie act) (a b c d : Ix r s) :
    units act a b * units act c d - units act c d * units act a b =
      (if b = c then units act a d else 0) - (if d = a then units act c b else 0) := by
  unfold units
  rw [h, eab_mul, eab_mul, map_sub]
  congr 1 <;> split_ifs <;> simp

theorem glK_of_lie {M : Type} [AddCommGroup M] [Module ℂ M] {act : Mat r s →ₗ[ℂ] Module.End ℂ M}
    (h : IsLie act) : GlK (units act) :=
  fun a b c d _ _ => glK_units h a b c d

theorem act_eq_sum {M : Type} [AddCommGroup M] [Module ℂ M] (act : Mat r s →ₗ[ℂ] Module.End ℂ M) (W : Mat r s) :
    act W = ∑ a, ∑ b, W a b • act (Eab a b) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single W]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← map_smul, Eab, Matrix.smul_single, smul_eq_mul, mul_one]

theorem adjK_of_adjG {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] {act : Mat r s →ₗ[ℂ] Module.End ℂ A} (h : AdjG act) : AdjK (units act) := by
  intro a b hab u v
  have := h a b u v
  rw [epsB, if_pos hab, one_mul] at this
  exact this

end PositivityTheory.KReal

end
