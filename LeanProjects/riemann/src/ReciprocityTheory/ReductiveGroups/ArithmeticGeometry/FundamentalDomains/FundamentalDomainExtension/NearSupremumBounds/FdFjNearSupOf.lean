import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting

namespace PI.FdFjNearSup.W

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def FjHolo : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ),
    P ∈ X.SS la → X.IsIso ξ → DifferentiableOn ℂ (X.fj la ξ ν P) X.dom

def FjRealFlow : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ),
    P ∈ X.SS la → X.IsIso ξ → ∀ x ∈ X.dom, ∀ s : X.Ψ → ℝ,
      X.fj la ξ ν P (X.flowV (X.embV ξ) (fun τ => (s τ : ℂ)) x) =
        cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * (s τ : ℂ)) * X.fj la ξ ν P x

theorem isIsoV_embV {r : ℕ} (X : Data E r) {ξ : Fin r → E} (h : X.IsIso ξ) :
    X.IsIsoV (X.embV ξ) := by
  intro τ
  obtain ⟨-, hh, hne⟩ := h
  have key : hermC τ.1 X.Gm (X.embV ξ τ) (X.embV ξ τ) = τ.1 (herm X.Gm ξ ξ) := by
    simp only [hermC, herm, Data.embV, Data.emb, map_sum, map_mul, cc,
      IsCMField.complexEmbedding_complexConj]
  refine ⟨by rw [key, hh, map_zero], fun h0 => hne ?_⟩
  funext a
  have h1 := congrFun h0 a
  simp only [Data.embV, Data.emb, Pi.zero_apply, map_eq_zero] at h1
  simpa using h1

theorem dmin_ne {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ)
    (j : Fin (r + 1)) : dmin X.Gm x τ j ≠ 0 := by
  intro h0
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hx
  have h1 := (hx τ).2 j
  rw [h0, Complex.zero_re, mul_zero] at h1
  exact lt_irrefl _ h1

theorem nfac_pos {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < X.nfac la x := by
  unfold Data.nfac
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
  exact norm_pos_iff.2 (div_ne_zero (dmin_ne X hx τ _) (dmin_ne X hx τ _))

theorem pnorm_eq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la Q x = ‖Q x‖ * X.nfac la x := rfl

theorem pnorm_nonneg {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : 0 ≤ X.pnorm la Q x := by
  rw [pnorm_eq]
  exact mul_nonneg (norm_nonneg _) (nfac_pos X la hx).le

theorem spread_nonneg {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (τ : X.Ψ) : 0 ≤ X.spread la τ := by
  unfold Data.spread
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp
  · have hb := Set.finite_range (fun i : Fin r => (la τ i : ℝ))
    exact sub_nonneg.2 ((ciInf_le hb.bddBelow (⟨0, hr⟩ : Fin r)).trans
      (le_ciSup hb.bddAbove (⟨0, hr⟩ : Fin r)))

theorem flow_eq {r : ℕ} (X : Data E r) (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    X.flow ξ s x = X.flowV (X.embV ξ) s x := rfl

theorem realFlow {r : ℕ} (X : Data E r) (h1 : FlowDomainCriterion (E := E))
    (h2 : FlowNormRatio (E := E)) {ξ : Fin r → E} (hξ : X.IsIso ξ) (la : Wt X.Ψ r)
    (x : Frame X.Ψ r) (hx : x ∈ X.dom) (s : X.Ψ → ℝ) :
    X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom ∧
      X.nfac la (X.flow ξ (fun τ => (s τ : ℂ)) x) = X.nfac la x := by
  rw [flow_eq]
  have he := isIsoV_embV X hξ
  have hd : X.flowV (X.embV ξ) (fun τ => (s τ : ℂ)) x ∈ X.dom :=
    (h1 r X _ he x hx _).1.2 fun τ => by simp
  refine ⟨hd, ?_⟩
  obtain ⟨hlo, hhi⟩ := h2 r X _ he la x hx _ hd
  simp only [Complex.ofReal_im, zero_div, add_zero, inv_one, min_self, max_self,
    Real.one_rpow, Finset.prod_const_one] at hlo hhi
  have hn := nfac_pos X la hd
  have heq := le_antisymm hhi hlo
  rw [div_eq_one_iff_eq hn.ne'] at heq
  exact heq.symm

theorem fj_pnorm_le {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E)
    (ν : X.Ψ → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hflow : ∀ x ∈ X.dom, ∀ s : X.Ψ → ℝ, X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom ∧
      X.nfac la (X.flow ξ (fun τ => (s τ : ℂ)) x) = X.nfac la x)
    (hP : ∀ x ∈ X.dom, X.pnorm la P x ≤ C) :
    ∀ x ∈ X.dom, X.pnorm la (X.fj la ξ ν P) x ≤ C := by
  intro x hx
  have hn := nfac_pos X la hx

  have hexp : ∀ s : X.Ψ → ℝ, ‖cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ))‖ = 1 := by
    intro s
    have e : -(4 * (Real.pi : ℂ) * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ) =
        ((-(4 * Real.pi * ∑ τ, ν τ * s τ) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [e, Complex.norm_exp_ofReal_mul_I]
  have hbound : ∀ s : X.Ψ → ℝ, ‖P (X.flow ξ (fun τ => (s τ : ℂ)) x) *
      cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ))‖ ≤ C / X.nfac la x := by
    intro s
    obtain ⟨hd, hnf⟩ := hflow x hx s
    have h1 := hP _ hd
    rw [pnorm_eq, hnf] at h1
    rw [norm_mul, hexp s, mul_one, le_div_iff₀ hn]
    exact h1
  rw [pnorm_eq]
  unfold Data.fj
  split_ifs with h₁ h₂
  · obtain ⟨-, -, hpos, hfin⟩ := h₂.choose_spec
    have hV : 0 < (volume h₂.choose).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
    have hint := norm_setIntegral_le_of_norm_le_const hfin (fun s _ => hbound s)
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV]
    have hreal : volume.real h₂.choose = (volume h₂.choose).toReal := rfl
    rw [hreal] at hint
    calc (volume h₂.choose).toReal⁻¹ * ‖∫ s in h₂.choose, P (X.flow ξ (fun τ => (s τ : ℂ)) x) *
          cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ))‖ * X.nfac la x
        ≤ (volume h₂.choose).toReal⁻¹ * (C / X.nfac la x * (volume h₂.choose).toReal) *
          X.nfac la x := by gcongr
      _ = C := by field_simp
  · simpa using hC0
  · simpa using hC0

theorem rho_facts {c1 w : ℝ} (hc1 : 0 < c1) (hw : 1 ≤ w) :
    0 < d6rh c1 w ∧ d6rh c1 w ≤ 1 / 36 ∧ 12 * Real.pi * (c1 + w) * d6rh c1 w = 1 := by
  have hp := Real.pi_gt_three
  have hA : 0 < 12 * Real.pi * (c1 + w) := by positivity
  have h36 : 36 ≤ 12 * Real.pi * (c1 + w) := by
    nlinarith [mul_le_mul_of_nonneg_right hp.le (by linarith : (0 : ℝ) ≤ c1 + w)]
  unfold d6rh
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_div_iff₀ hA (by norm_num)]
    linarith
  · field_simp

theorem ab_facts {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1 / 36) :
    0 < (1 - ρ) / (1 + ρ) ∧ ((1 - ρ) / (1 + ρ))⁻¹ = (1 + ρ) / (1 - ρ) ∧
      1 - 2 * ρ ≤ (1 - ρ) / (1 + ρ) ∧ (1 + ρ) / (1 - ρ) ≤ 1 + 3 * ρ ∧ 1 ≤ (1 + ρ) / (1 - ρ) := by
  have h1ρ : 0 < 1 - ρ := by linarith
  have h2ρ : 0 < 1 + ρ := by linarith
  refine ⟨div_pos h1ρ h2ρ, inv_div _ _, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ h2ρ]
    nlinarith
  · rw [div_le_iff₀ h1ρ]
    nlinarith
  · rw [le_div_iff₀ h1ρ]
    linarith

theorem fd_fj_near_sup_of (h1 : FlowDomainCriterion (E := E)) (h2 : FjHolo (E := E))
    (h3 : FjRealFlow (E := E)) (h4 : OrthonormalFlagTranslate (E := E)) :
    HolomorphicPeriodicityExtension (E := E) → FlowNormRatio (E := E) → ModerateCoefficientPositivity (E := E) →
      NearSupremumTransference (E := E) := by
  intro h5 h6 h7 r X la P ξ ν c1 w z0 hD x' hx' htt
  obtain ⟨-, hSS, hiso, hc1, hνc, ⟨x0, hx0, hfj0⟩, hw, hspw, -, -, -⟩ := hD
  obtain ⟨hρ0, hρ1, hρeq⟩ := rho_facts hc1 hw
  obtain ⟨ha0, hainv, halo, hahi, -⟩ := ab_facts hρ0 hρ1
  have hSS' := hSS
  obtain ⟨⟨hsec, C, hC⟩, -⟩ := hSS'
  have hiso' := isIsoV_embV X.toData hiso

  have hflow := fun x hx s => realFlow X.toData h1 h6 hiso la x hx s
  have hfjb : ∀ x ∈ X.dom, X.pnorm la (X.fj la ξ ν P) x ≤ max C 0 :=
    fj_pnorm_le X.toData la P ξ ν (max C 0) (le_max_right _ _) hflow
      (fun x hx => (hC x hx).trans (le_max_left _ _))
  have hν : ∀ τ, 0 ≤ ν τ := (h7 r X.toData la P C 0 hsec (fun x hx => by
    rw [neg_zero, Real.rpow_zero, mul_one]; exact hC x hx)).1 ξ hiso ν x0 hx0 hfj0
  have hN0 : ∀ y, 0 ≤ X.hatN la (X.fj la ξ ν P) y := fun y =>
    Real.sSup_nonneg fun t ⟨x'', hx'', _, ht⟩ => ht ▸ pnorm_nonneg X.toData la _ hx''
  have hNC : ∀ y, X.hatN la (X.fj la ξ ν P) y ≤ max C 0 := fun y =>
    Real.sSup_le (fun t ⟨x'', hx'', _, ht⟩ => ht ▸ hfjb x'' hx'') (le_max_right _ _)
  have hpN : ∀ y ∈ X.dom, X.pnorm la (X.fj la ξ ν P) y ≤ X.hatN la (X.fj la ξ ν P) y :=
    fun y hy => le_csSup ⟨max C 0, fun t ⟨x'', hx'', _, ht⟩ => ht ▸ hfjb x'' hx''⟩
      ⟨y, hy, fun τ => rfl, rfl⟩
  have hNS : ∀ y ∈ X.FramesOverBasis ξ, X.hatN la (X.fj la ξ ν P) y ≤
      sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y} :=
    fun y hy => le_csSup ⟨max C 0, fun t ⟨y, _, ht⟩ => ht ▸ hNC y⟩ ⟨y, hy, rfl⟩
  have hS0 : 0 ≤ sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y} :=
    Real.sSup_nonneg fun t ⟨y, _, ht⟩ => ht ▸ hN0 y
  refine Real.sSup_le ?_ (mul_nonneg (Real.exp_pos 2).le hS0)
  rintro _ ⟨x'', hx'', hsf, rfl⟩

  have hmaj := ((h4 r X.toData).2.2 x' hx' x'' hx'' hsf).2
  have htx : ∀ τ, (1 - d6rh c1 w) / (1 + d6rh c1 w) ≤ X.tt ξ x'' τ ∧
      X.tt ξ x'' τ ≤ (1 + d6rh c1 w) / (1 - d6rh c1 w) := by
    intro τ
    have e : X.tt ξ x'' τ = X.tt ξ x' τ := by simp only [Data.tt, hmaj]
    rw [e]
    exact htt τ
  have ttpos : ∀ τ, 0 < X.tt ξ x'' τ := fun τ => lt_of_lt_of_le ha0 (htx τ).1

  obtain ⟨s, hs⟩ : ∃ s : X.Ψ → ℂ, s = fun τ => I * ((1 - X.tt ξ x'' τ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hsim : ∀ τ, (s τ).im = 1 - X.tt ξ x'' τ := fun τ => by simp [hs]
  have hq : ∀ τ, 1 + (s τ).im / X.ttV (X.embV ξ) x'' τ = (X.tt ξ x'' τ)⁻¹ := by
    intro τ
    have ht0 := (ttpos τ).ne'
    show 1 + (s τ).im / X.tt ξ x'' τ = (X.tt ξ x'' τ)⁻¹
    rw [hsim, inv_eq_one_div, eq_div_iff ht0, add_mul, div_mul_cancel₀ _ ht0]
    ring
  have hM := h1 r X.toData _ hiso' x'' hx'' s
  have hy : X.flowV (X.embV ξ) s x'' ∈ X.dom :=
    hM.1.2 fun τ => by rw [hq τ]; exact inv_pos.2 (ttpos τ)
  have hyD : X.flowV (X.embV ξ) s x'' ∈ X.FramesOverBasis ξ := by
    refine ⟨hy, fun τ => ?_⟩
    have h11 : X.ttV (X.embV ξ) (X.flowV (X.embV ξ) s x'') τ = 1 := by
      rw [hM.2 hy τ, hsim]
      show X.tt ξ x'' τ + (1 - X.tt ξ x'' τ) = 1
      ring
    unfold Data.ttV at h11
    rw [one_div, inv_eq_one] at h11
    exact h11

  have hfj := h5 r X.toData _ hiso' (X.fj la ξ ν P) (h2 r X.toData la P ξ ν hSS hiso)
    (fun τ => (ν τ : ℂ)) x'' hx'' (h3 r X.toData la P ξ ν hSS hiso x'' hx'') s hy
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = ∑ τ, ν τ * (1 - X.tt ξ x'' τ) := ⟨_, rfl⟩
  have hsum : 4 * (Real.pi : ℂ) * I * ∑ τ, (fun τ => (ν τ : ℂ)) τ * s τ =
      ((-(4 * Real.pi * Λ) : ℝ) : ℂ) := by
    rw [hΛdef]
    simp only [hs]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    linear_combination (4 * (Real.pi : ℂ) * (ν τ : ℂ) * (1 - (X.tt ξ x'' τ : ℂ))) * Complex.I_sq
  rw [hsum, ← Complex.ofReal_exp] at hfj
  have hnorm := congrArg norm hfj
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at hnorm
  have hGx : ‖X.fj la ξ ν P x''‖ = Real.exp (4 * Real.pi * Λ) *
      ‖X.fj la ξ ν P (X.flowV (X.embV ξ) s x'')‖ := by
    rw [hnorm, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have hΛ : Λ ≤ c1 * (2 * d6rh c1 w) := by
    rw [hΛdef]
    calc ∑ τ, ν τ * (1 - X.tt ξ x'' τ) ≤ ∑ τ, ν τ * (2 * d6rh c1 w) :=
          Finset.sum_le_sum fun τ _ =>
            mul_le_mul_of_nonneg_left (by linarith [(htx τ).1, halo]) (hν τ)
      _ = (∑ τ, ν τ) * (2 * d6rh c1 w) := (Finset.sum_mul _ _ _).symm
      _ ≤ c1 * (2 * d6rh c1 w) := mul_le_mul_of_nonneg_right hνc (by linarith)
  have hpr := mul_pos Real.pi_pos hρ0
  have hexpΛ : Real.exp (4 * Real.pi * Λ) ≤ Real.exp 1 := by
    refine Real.exp_le_exp.2 ?_
    have h4 := mul_le_mul_of_nonneg_left hΛ (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
    nlinarith [mul_nonneg hpr.le hc1.le, mul_nonneg hpr.le (by linarith : (0 : ℝ) ≤ w)]

  obtain ⟨-, hhi⟩ := h6 r X.toData _ hiso' la x'' hx'' s hy
  have hny := nfac_pos X.toData la hy
  have hnx : X.nfac la x'' ≤ Real.exp 1 * X.nfac la (X.flowV (X.embV ξ) s x'') := by
    rw [← div_le_iff₀ hny]
    refine hhi.trans ?_
    have h3ρ : 0 ≤ 1 + 3 * d6rh c1 w := by linarith
    calc _ ≤ ∏ τ : X.Ψ, (1 + 3 * d6rh c1 w) ^ (X.spread la τ / 2) := by
          refine Finset.prod_le_prod (fun τ _ => ?_) (fun τ _ => ?_)
          · dsimp only
            rw [hq τ, inv_inv]
            exact Real.rpow_nonneg (le_max_of_le_right (ttpos τ).le) _
          · dsimp only
            rw [hq τ, inv_inv]
            refine Real.rpow_le_rpow (le_max_of_le_right (ttpos τ).le) (max_le ?_ ?_)
              (by linarith [spread_nonneg X.toData la τ])
            · exact ((inv_anti₀ ha0 (htx τ).1).trans (le_of_eq hainv)).trans hahi
            · exact (htx τ).2.trans hahi
      _ = (1 + 3 * d6rh c1 w) ^ (∑ τ, X.spread la τ / 2) :=
          (Real.rpow_sum_of_pos (by linarith) _ _).symm
      _ ≤ (1 + 3 * d6rh c1 w) ^ (w / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [← Finset.sum_div]; linarith)
      _ ≤ (Real.exp (3 * d6rh c1 w)) ^ (w / 2) :=
          Real.rpow_le_rpow h3ρ (by linarith [Real.add_one_le_exp (3 * d6rh c1 w)])
            (by linarith)
      _ = Real.exp (3 * d6rh c1 w * (w / 2)) := (Real.exp_mul _ _).symm
      _ ≤ Real.exp 1 := by
          refine Real.exp_le_exp.2 ?_
          nlinarith [mul_nonneg hpr.le hc1.le,
            mul_le_mul_of_nonneg_right Real.pi_gt_three.le
              (mul_nonneg hρ0.le (by linarith : (0 : ℝ) ≤ w))]

  have hN := (hpN _ hy).trans (hNS _ hyD)
  rw [pnorm_eq] at hN ⊢
  have hGx' : ‖X.fj la ξ ν P x''‖ ≤ Real.exp 1 * ‖X.fj la ξ ν P (X.flowV (X.embV ξ) s x'')‖ := by
    rw [hGx]
    exact mul_le_mul_of_nonneg_right hexpΛ (norm_nonneg _)
  calc ‖X.fj la ξ ν P x''‖ * X.nfac la x''
      ≤ (Real.exp 1 * ‖X.fj la ξ ν P (X.flowV (X.embV ξ) s x'')‖) *
        (Real.exp 1 * X.nfac la (X.flowV (X.embV ξ) s x'')) :=
        mul_le_mul hGx' hnx (nfac_pos X.toData la hx'').le (by positivity)
    _ = Real.exp 2 * (‖X.fj la ξ ν P (X.flowV (X.embV ξ) s x'')‖ *
        X.nfac la (X.flowV (X.embV ξ) s x'')) := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hN (Real.exp_pos 2).le

end

end PI.FdFjNearSup.W
