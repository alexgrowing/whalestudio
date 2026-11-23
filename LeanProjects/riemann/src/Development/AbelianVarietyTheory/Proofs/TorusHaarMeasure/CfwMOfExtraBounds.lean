import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.LowSpanCombinations
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicThreshold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.MemSSgtOfZeroOnDom
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.CoordDifferentiableAt

namespace GlobalTheory.FlatCompare

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

private theorem lact_one_torus_haar_measure (X : Data E r) (x : Frame X.Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem levi_eq (X : Data E r) (x0 : Frame X.Ψ r) (φ : Frame X.Ψ r → ℝ) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : levi X x0 φ z ξ = leviM X φ x0 z ξ := rfl

theorem hf_pos (X : Data E r) {ξ : Fin r → E} (hξ : ξ ≠ 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    0 < hf X ξ x τ := by
  unfold hf
  refine mul_pos (IsotropicThreshold.c_pos X τ) (X.maj_pos hx τ ?_)
  intro h0
  apply hξ
  funext a
  have h1 := congrFun h0 a
  simpa [Data.emb] using h1

theorem guard_iff (X : Data E r) {ξ : Fin r → E} (hξ : ξ ≠ 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    hf X ξ x τ ≤ 1 ↔ 1 ≤ X.tt ξ x τ := by
  rw [tt_eq X ξ x τ, one_le_div (hf_pos X hξ hx τ)]

theorem logTerm_nonneg (X : Data E r) (x : Frame X.Ψ r) : 0 ≤ Real.log (1 + 1 / X.la1 x) := by
  apply Real.log_nonneg
  have h1 : 0 ≤ 1 / X.la1 x := div_nonneg zero_le_one (Real.sqrt_nonneg _)
  linarith

theorem exists_short (X : Data E r) : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ X.dom, 0 < X.firstMinimumSq x → X.firstMinimumSq x < ε →
    ∃ v, X.IsIso v ∧ (∀ τ, 1 ≤ X.tt v x τ) ∧ ∀ τ, 1 / (2 * X.firstMinimumSq x) ≤ X.tt v x τ := by
  obtain ⟨δ0, hδ0, hiso⟩ := IsotropicThreshold.iso_threshold X
  refine ⟨min (δ0 / 2) (1 / 2), lt_min (by linarith) (by norm_num), fun x hx hpos hsmall => ?_⟩
  have hmin1 := min_le_left (δ0 / 2) (1 / 2)
  have hmin2 := min_le_right (δ0 / 2) (1 / 2)
  have hne : {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 : X.firstMinimumSq x = 0 := by rw [Data.firstMinimumSq, hemp, Real.sInf_empty]
    linarith
  obtain ⟨t, ⟨v, hvΛ, hv0, rfl⟩, hlt⟩ :=
    exists_lt_of_csInf_lt hne (show X.firstMinimumSq x < 2 * X.firstMinimumSq x by linarith)
  have hsum_lt : ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) < δ0 := by linarith
  have hherm := hiso x hx v hvΛ hsum_lt
  have hterm : ∀ τ, hf X v x τ ≤ ∑ τ', X.c τ' * X.maj x τ' (Data.emb τ'.1 v) := fun τ =>
    Finset.single_le_sum (f := fun τ' => X.c τ' * X.maj x τ' (Data.emb τ'.1 v))
      (fun τ' _ => (hf_pos X hv0 hx τ').le) (Finset.mem_univ τ)
  refine ⟨v, ⟨hvΛ, hherm, hv0⟩, fun τ => ?_, fun τ => ?_⟩
  · rw [← guard_iff X hv0 hx τ]
    linarith [hterm τ]
  · rw [tt_eq X v x τ]
    exact one_div_le_one_div_of_le (hf_pos X hv0 hx τ) (by linarith [hterm τ])

theorem bdd_add_log (X : Data E r) {ps : Frame X.Ψ r → ℝ} {a : ℝ} (h : cfwM X ps a) (ha : 0 < a)
    (K : ℝ) : ∃ B : ℝ, ∀ x ∈ X.dom, ps x + K * Real.log (1 + 1 / X.la1 x) ≤ B := by
  obtain ⟨⟨C1, A1, h1⟩, h2⟩ := h
  obtain ⟨C2, A2, h2'⟩ := h2 (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨ε, hε, hshort⟩ := exists_short X
  have hM : 0 ≤ |A1| + |K| + |A2| := by positivity
  have hpa : 0 < 8 * Real.pi * a := by positivity
  refine ⟨max (C1 + (|A1| + |K| + |A2|) / Real.sqrt ε)
    (C2 + (|A1| + |K| + |A2|) ^ 2 / (8 * Real.pi * a)), fun x hx => ?_⟩
  have hL0 := logTerm_nonneg X x
  have hy0 : 0 ≤ 1 / X.la1 x := div_nonneg zero_le_one (Real.sqrt_nonneg _)
  have hLy : Real.log (1 + 1 / X.la1 x) ≤ 1 / X.la1 x := by
    have h3 := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / X.la1 x by linarith)
    linarith
  have hK := mul_le_mul_of_nonneg_right (le_abs_self K) hL0
  have hA1 := mul_le_mul_of_nonneg_right (le_abs_self A1) hL0
  have hA2 := mul_le_mul_of_nonneg_right (le_abs_self A2) hL0
  have hA1' := mul_nonneg (abs_nonneg A1) hL0
  have hA2' := mul_nonneg (abs_nonneg A2) hL0
  by_cases hs : 0 < X.firstMinimumSq x ∧ X.firstMinimumSq x < ε
  · obtain ⟨v, hv, hv1, hv2⟩ := hshort x hx hs.1 hs.2
    have hb := h2' x hx v hv hv1
    have := nonempty_cmType X
    have hinf : 1 / (2 * X.firstMinimumSq x) ≤ ⨅ τ, X.tt v x τ := le_ciInf hv2
    have hla : X.la1 x ^ 2 = X.firstMinimumSq x := Real.sq_sqrt hs.1.le
    have hyy : 1 / (2 * X.firstMinimumSq x) = (1 / X.la1 x) ^ 2 / 2 := by
      rw [div_pow, one_pow, hla]; ring
    rw [hyy] at hinf
    have hcoef : (0 : ℝ) ≤ 8 * Real.pi * (1 - 2 * (1 / 4)) * a := by nlinarith [Real.pi_pos]
    have hI := mul_le_mul_of_nonneg_left hinf hcoef
    have hMy := mul_le_mul_of_nonneg_left hLy hM
    have hq : (|A1| + |K| + |A2|) * (1 / X.la1 x) - 2 * Real.pi * a * (1 / X.la1 x) ^ 2 ≤
        (|A1| + |K| + |A2|) ^ 2 / (8 * Real.pi * a) := by
      rw [le_div_iff₀ hpa]
      nlinarith [sq_nonneg (4 * Real.pi * a * (1 / X.la1 x) - (|A1| + |K| + |A2|))]
    refine le_trans ?_ (le_max_right _ _)
    linarith
  · have hLe : Real.log (1 + 1 / X.la1 x) ≤ 1 / Real.sqrt ε := by
      rcases le_or_gt (X.firstMinimumSq x) 0 with h0 | h0
      · have hz : X.la1 x = 0 := Real.sqrt_eq_zero'.2 h0
        rw [hz, div_zero, add_zero, Real.log_one]
        positivity
      · have hge : ε ≤ X.firstMinimumSq x := by
          by_contra hlt
          exact hs ⟨h0, not_le.1 hlt⟩
        exact hLy.trans (one_div_le_one_div_of_le (Real.sqrt_pos.2 hε) (Real.sqrt_le_sqrt hge))
    have hb := h1 x hx
    have hMe := mul_le_mul_of_nonneg_left hLe hM
    have he : (|A1| + |K| + |A2|) * (1 / Real.sqrt ε) = (|A1| + |K| + |A2|) / Real.sqrt ε := by ring
    refine le_trans ?_ (le_max_left _ _)
    linarith

theorem cfwM_of_extraBounds (X : Data E r) {ps : Frame X.Ψ r → ℝ} {a : ℝ} (h : ExtraBounds X ps a) :
    cfwM X ps a := by
  obtain ⟨A, h1, C, h2⟩ := h
  refine ⟨⟨C, A, h2⟩, fun η hη _ => ?_⟩
  obtain ⟨C', hC'⟩ := h1 η hη
  exact ⟨C', A, fun x hx ξ hξ htt => hC' x hx ξ hξ fun τ => (guard_iff X hξ.2.2 hx τ).2 (htt τ)⟩

theorem extraBounds_of_cfwM (X : Data E r) {ps : Frame X.Ψ r → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h : cfwM X ps a) : ExtraBounds X ps a := by
  rcases ha.eq_or_lt with ha0 | hapos
  · subst ha0
    obtain ⟨⟨C, A, hC⟩, -⟩ := h
    refine ⟨A, fun η _ => ⟨C, fun x hx ξ _ _ => ?_⟩, C, hC⟩
    have h1 := hC x hx
    simp only [mul_zero, zero_mul, sub_zero]
    exact h1
  · obtain ⟨B0, hB0⟩ := bdd_add_log X h hapos 0
    have := nonempty_cmType X
    refine ⟨0, fun η hη => ?_, B0, fun x hx => by linarith [hB0 x hx]⟩
    rcases lt_or_ge η (1 / 2) with hη2 | hη2
    · obtain ⟨C', A', hC'⟩ := h.2 (η / 2) (by linarith) (by linarith)
      obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (1 - 2 * η) / (1 - η) := ⟨_, rfl⟩
      have h1η : 0 < 1 - η := by linarith
      have hθ0 : 0 < θ := by rw [hθ]; exact div_pos (by linarith) h1η
      have hθ1 : θ < 1 := by rw [hθ, div_lt_one h1η]; linarith
      have hθη : θ * (1 - η) = 1 - 2 * η := by rw [hθ]; field_simp
      obtain ⟨K, hK⟩ : ∃ K : ℝ, (1 - θ) * K = θ * |A'| :=
        ⟨θ * |A'| / (1 - θ), by field_simp [(sub_pos.2 hθ1).ne']⟩
      obtain ⟨BK, hBK⟩ := bdd_add_log X h hapos K
      refine ⟨θ * C' + (1 - θ) * BK, fun x hx ξ hξ hg => ?_⟩
      have htt : ∀ τ, 1 ≤ X.tt ξ x τ := fun τ => (guard_iff X hξ.2.2 hx τ).1 (hg τ)
      have hL0 := logTerm_nonneg X x
      have e1 := mul_le_mul_of_nonneg_left (hC' x hx ξ hξ htt) hθ0.le
      have e2 := mul_le_mul_of_nonneg_left (hBK x hx) (sub_pos.2 hθ1).le
      have hKL : (1 - θ) * K * Real.log (1 + 1 / X.la1 x) =
          θ * |A'| * Real.log (1 + 1 / X.la1 x) := by rw [hK]
      have hA : θ * A' * Real.log (1 + 1 / X.la1 x) ≤ θ * |A'| * Real.log (1 + 1 / X.la1 x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self A') hθ0.le) hL0
      have h3 : θ * (8 * Real.pi * (1 - 2 * (η / 2)) * a * ⨅ τ, X.tt ξ x τ) =
          8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ x τ := by
        rw [← hθη]; ring
      linarith
    · refine ⟨B0, fun x hx ξ hξ hg => ?_⟩
      have htt : ∀ τ, 1 ≤ X.tt ξ x τ := fun τ => (guard_iff X hξ.2.2 hx τ).1 (hg τ)
      have hI : 1 ≤ ⨅ τ, X.tt ξ x τ := le_ciInf htt
      have h2 := hB0 x hx
      have hpI : 0 ≤ 8 * Real.pi * a * ⨅ τ, X.tt ξ x τ :=
        mul_nonneg (by positivity) (by linarith)
      nlinarith

theorem extraBounds_iff (X : Data E r) (ps : Frame X.Ψ r → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    ExtraBounds X ps a ↔ cfwM X ps a := ⟨fun h => cfwM_of_extraBounds X h, extraBounds_of_cfwM X ha⟩

private theorem lact_lact_eq_lact_mul (X : Data E r) (γ γ' : GL (Fin r) E) (x : Frame X.Ψ r) :
    lact (γ * γ') x = lact γ (lact γ' x) := by
  funext τ
  show ((γ * γ' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
    (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((γ' : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

private theorem rmul_lact_comm' (X : Data E r) (γ : GL (Fin r) E) (x b : Frame X.Ψ r) :
    rmul (lact γ x) b = lact γ (rmul x b) := by
  funext τ
  show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) * mat b τ =
    (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ)
  rw [Matrix.mul_assoc]

theorem samePt_symm (X : Data E r) {x y : Frame X.Ψ r} (h : SamePt X x y) : SamePt X y x := by
  obtain ⟨γ, hγ, b, hb, rfl⟩ := h
  refine ⟨γ⁻¹, inv_mem hγ, ExtFPf.invF X b, ExtFPf.invF_mem X hb, ?_⟩
  rw [rmul_lact_comm', ← lact_lact_eq_lact_mul, inv_mul_cancel, lact_one_torus_haar_measure, ExtFPf.rmul_assoc,
    ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]

theorem samePt_trans (X : Data E r) {x y z : Frame X.Ψ r} (h : SamePt X x y) (h' : SamePt X y z) :
    SamePt X x z := by
  obtain ⟨γ, hγ, b, hb, rfl⟩ := h
  obtain ⟨γ', hγ', b', hb', rfl⟩ := h'
  refine ⟨γ' * γ, mul_mem hγ' hγ, rmul b b', ExtFPf.mul_mem X hb hb', ?_⟩
  rw [rmul_lact_comm', ExtFPf.rmul_assoc, lact_lact_eq_lact_mul]

theorem continuous_act (X : Data E r) (γ : GL (Fin r) E) (b : Frame X.Ψ r) :
    Continuous fun x : Frame X.Ψ r => lact γ (rmul x b) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun x : Frame X.Ψ r =>
    ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) : Matrix (Fin r) (Fin r) ℂ)
  exact continuous_const.matrix_mul ((continuous_apply τ).matrix_mul continuous_const)

theorem offNbhd_iff (X : Data E r) {ι : Type} {P : ι → Frame X.Ψ r} (hP : ∀ k, P k ∈ X.dom)
    (Φ : ℝ → Frame X.Ψ r → Prop) :
    (∀ U : Set (Frame X.Ψ r), IsOpen U → (∀ k, P k ∈ U) → ∃ C : ℝ, ∀ x ∈ X.dom,
      (∀ u ∈ U, u ∈ X.dom → ¬ SamePt X u x) → Φ C x) ↔
    ∀ U : Set (Frame X.Ψ r), IsOpen U → (∀ k, P k ∈ U) →
      (∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U) →
      ∃ K : ℝ, ∀ x ∈ X.dom, x ∉ U → Φ K x := by
  constructor
  · intro H U hU hPU hsat
    obtain ⟨C, hC⟩ := H U hU hPU
    refine ⟨C, fun x hx hxU => hC x hx fun u hu _ hux => hxU ?_⟩
    obtain ⟨γ, hγ, b, hb, rfl⟩ := hux
    exact hsat u hu γ hγ b hb
  · intro H U hU hPU
    have hopen : IsOpen {y | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul y b) ∈ U} := by
      have e : {y | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul y b) ∈ U} =
          ⋃ γ ∈ X.Γ, ⋃ b ∈ Bor X.Ψ r, (fun y => lact γ (rmul y b)) ⁻¹' U := by
        ext y
        simp
      rw [e]
      exact isOpen_biUnion fun γ _ => isOpen_biUnion fun b _ => hU.preimage (continuous_act X γ b)
    have hmem : ∀ k, P k ∈ {y | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul y b) ∈ U} := fun k =>
      ⟨1, one_mem _, ExtFPf.oneF X, ExtFPf.oneF_mem X, by
        rw [ExtFPf.rmul_oneF, lact_one_torus_haar_measure]; exact hPU k⟩
    have hsat : ∀ x ∈ {y | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul y b) ∈ U}, ∀ γ ∈ X.Γ,
        ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ {y | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul y b) ∈ U} := by
      rintro y ⟨γ0, hγ0, b0, hb0, hy⟩ γ hγ b hb
      have hs1 : SamePt X y (lact γ (rmul y b)) := ⟨γ, hγ, b, hb, rfl⟩
      have hs2 : SamePt X y (lact γ0 (rmul y b0)) := ⟨γ0, hγ0, b0, hb0, rfl⟩
      obtain ⟨γ', hγ', b', hb', e⟩ := samePt_trans X (samePt_symm X hs1) hs2
      exact ⟨γ', hγ', b', hb', by rw [← e]; exact hy⟩
    obtain ⟨K, hK⟩ := H _ hopen hmem hsat
    refine ⟨K, fun x hx hxU => hK x hx ?_⟩
    rintro ⟨γ, hγ, b, hb, hu⟩
    have hs : SamePt X x (lact γ (rmul x b)) := ⟨γ, hγ, b, hb, rfl⟩
    exact hxU _ hu (OntoS.dom_lact X hγ (OntoS.dom_rmul X hx hb)) (samePt_symm X hs)

theorem sqrt_le_iff {α : Type} (D : Set α) (p : α → Prop) {f g : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hg : ∀ x, 0 ≤ g x) :
    (∃ C : ℝ, ∀ x ∈ D, p x → √(f x) ≤ C * √(g x)) ↔ ∃ K : ℝ, ∀ x ∈ D, p x → f x ≤ K * g x := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C ^ 2, fun x hx hpx => ?_⟩
    calc f x = √(f x) ^ 2 := (Real.sq_sqrt (hf x)).symm
      _ ≤ (C * √(g x)) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hC x hx hpx) 2
      _ = C ^ 2 * g x := by rw [mul_pow, Real.sq_sqrt (hg x)]
  · rintro ⟨K, hK⟩
    refine ⟨√(max K 0), fun x hx hpx => ?_⟩
    rw [← Real.sqrt_mul (le_max_right K 0)]
    exact Real.sqrt_le_sqrt ((hK x hx hpx).trans (mul_le_mul_of_nonneg_right (le_max_left K 0) (hg x)))

theorem sumSq_nonneg (X : Data E r) (L : Wt X.Ψ r) {ι : Type} [Fintype ι] (g : ι → Frame X.Ψ r → ℂ)
    (x : Frame X.Ψ r) : 0 ≤ ∑ j, X.pnorm L (g j) x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem wLeS_iff (X : Data E r) (L : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ)
    (s : Fin (nd X) → Frame X.Ψ r → ℂ) {δ : ℕ} {P : Fin δ → Frame X.Ψ r} (hP : ∀ k, P k ∈ X.dom) :
    (∀ U : Set (Frame X.Ψ r), IsOpen U → (∀ k, P k ∈ U) → ∃ C : ℝ, ∀ x ∈ X.dom,
      (∀ u ∈ U, u ∈ X.dom → ¬ SamePt X u x) → famNorm X L w x ≤ C * famNorm X L s x) ↔
    ∀ U : Set (Frame X.Ψ r), IsOpen U → (∀ k, P k ∈ U) →
      (∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U) →
      ∃ K : ℝ, ∀ x ∈ X.dom, x ∉ U → ∑ k, X.pnorm L (w k) x ^ 2 ≤ K * ∑ k, X.pnorm L (s k) x ^ 2 := by
  refine (offNbhd_iff X hP (fun C x => famNorm X L w x ≤ C * famNorm X L s x)).trans ?_
  refine forall_congr' fun U => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => ?_
  exact sqrt_le_iff X.dom (fun x => x ∉ U) (fun x => sumSq_nonneg X L w x) (fun x => sumSq_nonneg X L s x)

theorem wLe_iff (X : Data E r) (L : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ)
    (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) :
    (∃ C : ℝ, ∀ x ∈ X.dom,
      famNorm X L w x ≤ C * famNorm X L (fun o : Option (Fin (nd X)) => o.elim w0 s) x) ↔
    ∃ K : ℝ, ∀ x ∈ X.dom, ∑ k, X.pnorm L (w k) x ^ 2 ≤
      K * (X.pnorm L w0 x ^ 2 + ∑ k, X.pnorm L (s k) x ^ 2) := by
  have e : ∀ x, famNorm X L (fun o : Option (Fin (nd X)) => o.elim w0 s) x =
      √(X.pnorm L w0 x ^ 2 + ∑ k, X.pnorm L (s k) x ^ 2) := fun x => by
    simp [famNorm, Fintype.sum_option]
  have h := sqrt_le_iff X.dom (fun _ => True) (f := fun x => ∑ k, X.pnorm L (w k) x ^ 2)
    (g := fun x => X.pnorm L w0 x ^ 2 + ∑ k, X.pnorm L (s k) x ^ 2)
    (fun x => sumSq_nonneg X L w x) (fun x => add_nonneg (sq_nonneg _) (sumSq_nonneg X L s x))
  simp only [true_implies] at h
  simp only [e]
  exact h

theorem coord_iff {n : ℕ} (f : V n → V n) :
    (∃ T : V n ≃L[ℂ] V n, HasFDerivAt f (T : V n →L[ℂ] V n) 0) ↔ (fderiv ℂ f 0).det ≠ 0 := by
  constructor
  · rintro ⟨T, hT⟩
    rw [hT.fderiv]
    exact (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero
  · intro h
    have hd : DifferentiableAt ℂ f 0 := by
      by_contra hnd
      rw [fderiv_zero_of_not_differentiableAt hnd] at h
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        have hc : f = fun _ => f 0 := funext fun v => congrArg f (PiLp.ext fun i => Fin.elim0 i)
        rw [hc] at hnd
        exact hnd (differentiableAt_const _)
      · apply h
        change LinearMap.det ((0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) = 0
        rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero, finrank_euclideanSpace_fin,
          zero_pow hn.ne']
    refine ⟨(fderiv ℂ f 0).toContinuousLinearEquivOfDetNeZero h, ?_⟩
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact hd.hasFDerivAt

theorem comb_le (X : Data E r) (L : Wt X.Ψ r) {N : ℕ} {w : Fin N → Frame X.Ψ r → ℂ}
    {f : Frame X.Ψ r → ℂ} (h : IsComb X w f) :
    ∃ K : ℝ, ∀ x ∈ X.dom, X.pnorm L f x ^ 2 ≤ K * ∑ k, X.pnorm L (w k) x ^ 2 := by
  obtain ⟨c, hc⟩ := h
  refine ⟨∑ j, ‖c j‖ ^ 2, fun x hx => ?_⟩
  have key : X.pnorm L f x ≤ ∑ j, ‖c j‖ * X.pnorm L (w j) x := by
    rw [BoundedSectionAlgebra.pnorm_eq, hc x hx]
    calc ‖∑ j, c j * w j x‖ * X.nfac L x ≤ (∑ j, ‖c j‖ * ‖w j x‖) * X.nfac L x :=
          mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul])))
            (BoundedSectionAlgebra.nfac_nonneg X L x)
      _ = ∑ j, ‖c j‖ * X.pnorm L (w j) x := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [BoundedSectionAlgebra.pnorm_eq]
          ring
  calc X.pnorm L f x ^ 2 ≤ (∑ j, ‖c j‖ * X.pnorm L (w j) x) ^ 2 :=
        pow_le_pow_left₀ (BoundedSectionAlgebra.pnorm_nonneg X L f x) key 2
    _ ≤ (∑ j, ‖c j‖ ^ 2) * ∑ j, X.pnorm L (w j) x ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem mem_SSgt_congr (X : Data E r) {L : Wt X.Ψ r} {a : ℝ} {f g : Frame X.Ψ r → ℂ}
    (h : ∀ x ∈ X.dom, f x = g x) (hg : g ∈ X.SSgt L a) : f ∈ X.SSgt L a := by
  obtain ⟨⟨⟨⟨hd, hb, hγ⟩, C, hC⟩, h0⟩, h1⟩ := hg
  have hsec : X.IsSec L f :=
    ⟨hd.congr h, fun x hx b hb' => by
      rw [h _ (OntoS.dom_rmul X hx hb'), h x hx, hb x hx b hb'], fun γ hγ' x hx => by
      rw [h _ (OntoS.dom_lact X hγ' hx), h x hx, hγ γ hγ' x hx]⟩
  refine ⟨⟨⟨hsec, C, fun x hx => ?_⟩, fun ξ hξ x hx => ?_⟩, fun ξ hξ ν hν x hx => ?_⟩
  · rw [BoundedSectionAlgebra.pnorm_eq, h x hx, ← BoundedSectionAlgebra.pnorm_eq]
    exact hC x hx
  · rw [GlobalTheory.FJCheck.fj_congr X L hξ 0 h hx]
    exact h0 ξ hξ x hx
  · rw [GlobalTheory.FJCheck.fj_congr X L hξ ν h hx]
    exact h1 ξ hξ ν hν x hx

private theorem zero_mem_SSgt (X : Data E r) (L : Wt X.Ψ r) (a : ℝ) :
    (0 : Frame X.Ψ r → ℂ) ∈ X.SSgt L a :=
  ⟨⟨BoundedSectionAlgebra.bdd_zero X L, fun ξ _ x _ => BoundedSectionAlgebra.fj_zero X L ξ x 0⟩,
    fun ξ _ ν _ x _ => BoundedSectionAlgebra.fj_zero X L ξ x ν⟩

private theorem add_mem_SSgt (X : Data E r) {L : Wt X.Ψ r} {a : ℝ} {P Q : Frame X.Ψ r → ℂ}
    (hP : P ∈ X.SSgt L a) (hQ : Q ∈ X.SSgt L a) : P + Q ∈ X.SSgt L a :=
  ⟨⟨BoundedSectionAlgebra.bdd_add X hP.1.1 hQ.1.1, fun ξ hξ x hx => by
      rw [BoundedSectionAlgebra.fj_add X hP.1.1 hQ.1.1 hξ hx, hP.1.2 ξ hξ x hx, hQ.1.2 ξ hξ x hx, add_zero]⟩,
    fun ξ hξ ν hν x hx => by
      rw [BoundedSectionAlgebra.fj_add X hP.1.1 hQ.1.1 hξ hx, hP.2 ξ hξ ν hν x hx, hQ.2 ξ hξ ν hν x hx, add_zero]⟩

private theorem smul_mem_SSgt (X : Data E r) {L : Wt X.Ψ r} {a : ℝ} (z : ℂ) {P : Frame X.Ψ r → ℂ}
    (hP : P ∈ X.SSgt L a) : z • P ∈ X.SSgt L a :=
  ⟨⟨BoundedSectionAlgebra.bdd_smul X z hP.1.1, fun ξ hξ x hx => by
      rw [BoundedSectionAlgebra.fj_smul, hP.1.2 ξ hξ x hx, mul_zero]⟩,
    fun ξ hξ ν hν x hx => by rw [BoundedSectionAlgebra.fj_smul, hP.2 ξ hξ ν hν x hx, mul_zero]⟩

theorem comb_mem_SSgt (X : Data E r) {L : Wt X.Ψ r} {a : ℝ} {N : ℕ} {w : Fin N → Frame X.Ψ r → ℂ}
    (hw : ∀ k, w k ∈ X.SSgt L a) {f : Frame X.Ψ r → ℂ} (h : IsComb X w f) : f ∈ X.SSgt L a := by
  obtain ⟨c, hc⟩ := h
  have hsum : (∑ j, c j • w j) ∈ X.SSgt L a :=
    Finset.sum_induction _ (· ∈ X.SSgt L a) (fun P Q hP hQ => add_mem_SSgt X hP hQ)
      (zero_mem_SSgt X L a) fun j _ => smul_mem_SSgt X (c j) (hw j)
  refine mem_SSgt_congr X (fun x hx => ?_) hsum
  rw [hc x hx]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

def toFlatM {X : Data E r} (Xa : ArchInM X) {w0 : Frame X.Ψ r → ℂ} {s : Fin (nd X) → Frame X.Ψ r → ℂ}
    {del : ℕ} {P : Fin del → Frame X.Ψ r} (h : IsFlat X Xa.L Xa.w w0 s P) : FlatM X Xa where
  w0 := w0
  s := s
  weightForm_vanishes := comb_mem_SSgt X Xa.w_van h.base_weight_isComb
  s_van k := comb_mem_SSgt X Xa.w_van (h.s_comb k)
  δ := del
  xs := P
  xs_mem := h.rep_mem
  S_eq := h.zero_iff
  xs_inj j j' γ hγ b hb e := h.rep_inj j j' ⟨γ, hγ, b, hb, e⟩
  w0_ne := h.w0_ne
  coord j := (coord_iff (zMap X w0 s (P j))).1 (h.coord j)
  w_le := (wLe_iff X Xa.L Xa.w w0 s).1 h.weight_le_base_weight
  denom_le_family := comb_le X Xa.L h.base_weight_isComb
  s_le_w := by
    choose K hK using fun k => comb_le X Xa.L (h.s_comb k)
    exact ⟨∑ k, K k, fun x hx => by
      rw [Finset.sum_mul]; exact Finset.sum_le_sum fun k _ => hK k x hx⟩
  family_le_coords := (wLeS_iff X Xa.L Xa.w s h.rep_mem).1 h.family_le_coords

end

end GlobalTheory.FlatCompare
