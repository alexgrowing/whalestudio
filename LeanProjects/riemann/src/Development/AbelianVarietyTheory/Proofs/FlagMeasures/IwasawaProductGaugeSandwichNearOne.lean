import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutOutSubgroupTangentSecondOrderHilbertSchmidtStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwSand

theorem exists_le_mul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] (f g : V → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hfs : ∀ s : ℝ, 0 ≤ s → ∀ v, f (s • v) = s * f v)
    (hgs : ∀ s : ℝ, 0 ≤ s → ∀ v, g (s • v) = s * g v) (hg0 : ∀ v, 0 ≤ g v) (hd : ∀ v, g v = 0 → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v, f v ≤ C * g v := by
  have hf0 : f 0 = 0 := by simpa using hfs 0 le_rfl 0
  have hg0' : g 0 = 0 := by simpa using hgs 0 le_rfl 0
  rcases (Metric.sphere (0 : V) 1).eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun v => ?_⟩
    have hv : v = 0 := by
      by_contra hv
      have hmem : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
        simp [norm_smul, hv]
      rw [hS] at hmem
      exact hmem
    subst hv
    simp [hf0, hg0']
  · have hK := isCompact_sphere (0 : V) 1
    obtain ⟨u0, hu0, hmin⟩ := hK.exists_isMinOn hS hg.continuousOn
    obtain ⟨u1, -, hmax⟩ := hK.exists_isMaxOn hS hf.continuousOn
    have hm : 0 < g u0 := by
      rcases (hg0 u0).lt_or_eq with h | h
      · exact h
      · exfalso
        have h0 := hd u0 h.symm
        subst h0
        simp at hu0
    refine ⟨max (f u1) 0 / g u0 + 1, by positivity, fun v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp [hf0, hg0']
    have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hw : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
      simp [norm_smul, hr.ne']
    have hvw : v = ‖v‖ • (‖v‖⁻¹ • v) := by
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hfv : f v = ‖v‖ * f (‖v‖⁻¹ • v) := by
      conv_lhs => rw [hvw]
      exact hfs _ hr.le _
    have hgv : g v = ‖v‖ * g (‖v‖⁻¹ • v) := by
      conv_lhs => rw [hvw]
      exact hgs _ hr.le _
    have h1 : f (‖v‖⁻¹ • v) ≤ f u1 := isMaxOn_iff.mp hmax _ hw
    have h2 : g u0 ≤ g (‖v‖⁻¹ • v) := isMinOn_iff.mp hmin _ hw
    have hgw : 0 ≤ g (‖v‖⁻¹ • v) := hg0 _
    rw [hfv, hgv]
    calc ‖v‖ * f (‖v‖⁻¹ • v) ≤ ‖v‖ * max (f u1) 0 :=
          mul_le_mul_of_nonneg_left (h1.trans (le_max_left _ _)) hr.le
      _ = max (f u1) 0 / g u0 * (‖v‖ * g u0) := by field_simp
      _ ≤ max (f u1) 0 / g u0 * (‖v‖ * g (‖v‖⁻¹ • v)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hr.le) (by positivity)
      _ ≤ (max (f u1) 0 / g u0 + 1) * (‖v‖ * g (‖v‖⁻¹ • v)) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hr.le hgw)

variable {n : ℕ}

theorem nrm_le_add_sub (X Y : Matrix (Fin n) (Fin n) ℂ) : nrm X ≤ nrm Y + nrm (X - Y) := by
  have h := nrm_add_le Y (X - Y)
  rwa [add_sub_cancel] at h

theorem abs_nrm_sub_le (X Y : Matrix (Fin n) (Fin n) ℂ) : |nrm X - nrm Y| ≤ nrm (X - Y) := by
  have h1 := nrm_le_add_sub X Y
  have h2 := nrm_le_add_sub Y X
  have h3 : nrm (Y - X) = nrm (X - Y) := by rw [← neg_sub, nrm_neg]
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem abs_len_sub_le {d : ℕ} (x y : Fin d → ℝ) : |len x - len y| ≤ len (x - y) := by
  have h1 : len x ≤ len y + len (x - y) := by
    have h := len_add_le y (x - y)
    rwa [add_sub_cancel] at h
  have h2 : len y ≤ len x + len (y - x) := by
    have h := len_add_le x (y - x)
    rwa [add_sub_cancel] at h
  have h3 : len (y - x) = len (x - y) := by rw [← neg_sub, len_neg]
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem nrm_prod_sub_le (a b c X Y Z : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (hs1 : s ≤ 1) (ha : nrm (a - 1) ≤ s)
    (hb : nrm (b - 1) ≤ s) (hc : nrm (c - 1) ≤ s) (hX : nrm (a - 1 - X) ≤ s ^ 2) (hY : nrm (b - 1 - Y) ≤ s ^ 2)
    (hZ : nrm (c - 1 - Z) ≤ s ^ 2) : nrm (a * b * c - 1 - (X + Y + Z)) ≤ 7 * s ^ 2 := by
  have hs0 : 0 ≤ s := (nrm_nonneg _).trans ha
  have key : a * b * c - 1 - (X + Y + Z) =
      ((a - 1 - X) + (b - 1 - Y) + (c - 1 - Z)) +
        ((a - 1) * (b - 1) + (a - 1) * (c - 1) + (b - 1) * (c - 1)) + (a - 1) * (b - 1) * (c - 1) := by
    noncomm_ring
  have pr2 : ∀ P Q : Matrix (Fin n) (Fin n) ℂ, nrm P ≤ s → nrm Q ≤ s → nrm (P * Q) ≤ s ^ 2 := by
    intro P Q hP hQ
    calc nrm (P * Q) ≤ nrm P * nrm Q := nrm_mul_le _ _
      _ ≤ s * s := mul_le_mul hP hQ (nrm_nonneg _) hs0
      _ = s ^ 2 := (sq s).symm
  have e1 : nrm ((a - 1 - X) + (b - 1 - Y) + (c - 1 - Z)) ≤ 3 * s ^ 2 := by
    have := nrm_add_le ((a - 1 - X) + (b - 1 - Y)) (c - 1 - Z)
    have := nrm_add_le (a - 1 - X) (b - 1 - Y)
    linarith
  have e2 : nrm ((a - 1) * (b - 1) + (a - 1) * (c - 1) + (b - 1) * (c - 1)) ≤ 3 * s ^ 2 := by
    have := nrm_add_le ((a - 1) * (b - 1) + (a - 1) * (c - 1)) ((b - 1) * (c - 1))
    have := nrm_add_le ((a - 1) * (b - 1)) ((a - 1) * (c - 1))
    have := pr2 _ _ ha hb
    have := pr2 _ _ ha hc
    have := pr2 _ _ hb hc
    linarith
  have e3 : nrm ((a - 1) * (b - 1) * (c - 1)) ≤ s ^ 2 := by
    calc nrm ((a - 1) * (b - 1) * (c - 1)) ≤ nrm ((a - 1) * (b - 1)) * nrm (c - 1) := nrm_mul_le _ _
      _ ≤ s ^ 2 * s := mul_le_mul (pr2 _ _ ha hb) hc (nrm_nonneg _) (sq_nonneg _)
      _ ≤ s ^ 2 * 1 := mul_le_mul_of_nonneg_left hs1 (sq_nonneg _)
      _ = s ^ 2 := mul_one _
  rw [key]
  have := nrm_add_le (((a - 1 - X) + (b - 1 - Y) + (c - 1 - Z)) +
        ((a - 1) * (b - 1) + (a - 1) * (c - 1) + (b - 1) * (c - 1))) ((a - 1) * (b - 1) * (c - 1))
  have := nrm_add_le ((a - 1 - X) + (b - 1 - Y) + (c - 1 - Z))
        ((a - 1) * (b - 1) + (a - 1) * (c - 1) + (b - 1) * (c - 1))
  linarith

theorem real_sandwich {C η s σ γ : ℝ} (hC : 0 < C) (hη : 0 < η) (hγ : 0 ≤ γ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2)
    (hs' : s ≤ η / (1 + η) / (14 * C)) (h1 : s ≤ C * γ + s ^ 2) (h2 : |σ - γ| ≤ 7 * s ^ 2) :
    γ ≤ (1 + η) * σ ∧ σ ≤ (1 + η) * γ ∧ s ≤ 2 * C * γ := by
  have hδη : η / (1 + η) ≤ η := div_le_self hη.le (by linarith)
  have hδ : η / (1 + η) * (1 + η) = η := div_mul_cancel₀ η (by positivity)
  have h3 : s ≤ 2 * C * γ := by nlinarith [mul_nonneg hs0 (sub_nonneg.2 hs)]
  have h4 : s * (14 * C) ≤ η / (1 + η) := by
    rwa [le_div_iff₀ (by positivity)] at hs'
  have h5 : 7 * s ^ 2 ≤ η / (1 + η) * γ := by
    nlinarith [mul_le_mul_of_nonneg_left h3 hs0, mul_le_mul_of_nonneg_right h4 hγ]
  obtain ⟨hl, hr⟩ := abs_le.mp h2
  refine ⟨?_, ?_, h3⟩
  · have hpos : 0 ≤ (1 + η) * (σ - γ + η / (1 + η) * γ) :=
      mul_nonneg (by linarith) (by linarith)
    have hδγ : η / (1 + η) * (1 + η) * γ = η * γ := by rw [hδ]
    nlinarith
  · nlinarith [mul_le_mul_of_nonneg_right hδη hγ]

theorem gau_sandwich : ∀ (n : ℕ) (ε : Fin n → Bool) (SN SM MainNotions : Set (Formalism.REAL.UJ ε)), ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε SN EN → IsCut ε SM EM → IsCut ε MainNotions EK → IsON EL → (∀ v, gau EN EM EK EL v = 0 → v = 0) → ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ ∀ u ∈ SN, ∀ m ∈ SM, ∀ k ∈ MainNotions, nrm (uMat u - 1) < t → nrm (uMat m - 1) < t → nrm (uMat k - 1) < t → ∀ σ γ : ℝ, σ = max (nrm (uMat (u * m * k) - 1)) (len (crd EL (uMat k - 1))) → γ = gau EN EM EK EL (crd EN (uMat u - 1), crd EM (uMat m - 1), crd EK (uMat k - 1)) → γ ≤ (1 + η) * σ ∧ σ ≤ (1 + η) * γ ∧ nrm (uMat u - 1) ≤ C * γ ∧ nrm (uMat m - 1) ≤ C * γ ∧ nrm (uMat k - 1) ≤ C * γ := by
  intro n ε SN SM MainNotions dN dM dK dL EN EM EK EL hN hM hK hL hdef
  obtain ⟨C0, hC0, hC0le⟩ := exists_le_mul
    (fun v : (Fin dN → ℝ) × (Fin dM → ℝ) × (Fin dK → ℝ) => max (len v.1) (max (len v.2.1) (len v.2.2)))
    (gau EN EM EK EL)
    ((continuous_len.comp continuous_fst).max ((continuous_len.comp (continuous_fst.comp continuous_snd)).max
      (continuous_len.comp (continuous_snd.comp continuous_snd))))
    (continuous_gau EN EM EK EL)
    (by
      intro s hs v
      simp only [Prod.smul_fst, Prod.smul_snd, len_smul, abs_of_nonneg hs]
      rw [mul_max_of_nonneg _ _ hs, mul_max_of_nonneg _ _ hs])
    (fun s hs v => gau_smul EN EM EK EL s hs v) (gau_nonneg EN EM EK EL) hdef
  refine ⟨2 * C0, by positivity, fun η hη => ?_⟩
  refine ⟨min (1 / 2) (η / (1 + η) / (14 * C0)), lt_min (by norm_num) (by positivity), ?_⟩
  intro u hu m hm k hk hut hmt hkt σ γ hσ hγ
  set s := max (nrm (uMat u - 1)) (max (nrm (uMat m - 1)) (nrm (uMat k - 1))) with hs_def
  have hst : s < min (1 / 2) (η / (1 + η) / (14 * C0)) := max_lt hut (max_lt hmt hkt)
  have hs12 : s ≤ 1 / 2 := (hst.trans_le (min_le_left _ _)).le
  have hsη : s ≤ η / (1 + η) / (14 * C0) := (hst.trans_le (min_le_right _ _)).le
  have hsu : nrm (uMat u - 1) ≤ s := le_max_left _ _
  have hsm : nrm (uMat m - 1) ≤ s := (le_max_left _ _).trans (le_max_right _ _)
  have hsk : nrm (uMat k - 1) ≤ s := (le_max_right _ _).trans (le_max_right _ _)
  have hs0 : 0 ≤ s := (nrm_nonneg _).trans hsu
  have hs2 : ∀ x : ℝ, 0 ≤ x → x ≤ s → x ^ 2 ≤ s ^ 2 := fun x hx hxs => pow_le_pow_left₀ hx hxs 2

  have aN := GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt n ε SN dN EN hN u hu
  have aM := GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt n ε SM dM EM hM m hm
  have aK := GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt n ε MainNotions dK EK hK k hk
  set X := cmb EN (crd EN (uMat u - 1))
  set Y := cmb EM (crd EM (uMat m - 1))
  set Z := cmb EK (crd EK (uMat k - 1))
  have aN' : nrm (uMat u - 1 - X) ≤ s ^ 2 := aN.trans (hs2 _ (nrm_nonneg _) hsu)
  have aM' : nrm (uMat m - 1 - Y) ≤ s ^ 2 := aM.trans (hs2 _ (nrm_nonneg _) hsm)
  have aK' : nrm (uMat k - 1 - Z) ≤ s ^ 2 := aK.trans (hs2 _ (nrm_nonneg _) hsk)
  have hmul : uMat (u * m * k) = uMat u * uMat m * uMat k := by
    simp [uMat]
  have hprod : nrm (uMat (u * m * k) - 1 - (X + Y + Z)) ≤ 7 * s ^ 2 := by
    rw [hmul]
    exact nrm_prod_sub_le _ _ _ X Y Z s (by linarith) hsu hsm hsk aN' aM' aK'
  have hγ' : γ = max (nrm (X + Y + Z)) (len (crd EL Z)) := by
    rw [hγ]; rfl
  have d1 : |nrm (uMat (u * m * k) - 1) - nrm (X + Y + Z)| ≤ 7 * s ^ 2 :=
    (abs_nrm_sub_le _ _).trans hprod
  have d2 : |len (crd EL (uMat k - 1)) - len (crd EL Z)| ≤ 7 * s ^ 2 := by
    refine (abs_len_sub_le _ _).trans ?_
    rw [← crd_sub]
    refine (len_crd_le hL _).trans ?_
    nlinarith [sq_nonneg s]
  have hσγ : |σ - γ| ≤ 7 * s ^ 2 := by
    rw [hσ, hγ']
    exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le d1 d2)

  have hγ0 : 0 ≤ γ := by rw [hγ]; exact gau_nonneg _ _ _ _ _
  have hbound := hC0le (crd EN (uMat u - 1), crd EM (uMat m - 1), crd EK (uMat k - 1))
  rw [← hγ] at hbound
  have lN : len (crd EN (uMat u - 1)) ≤ C0 * γ := (le_max_left _ _).trans hbound
  have lM : len (crd EM (uMat m - 1)) ≤ C0 * γ := ((le_max_left _ _).trans (le_max_right _ _)).trans hbound
  have lK : len (crd EK (uMat k - 1)) ≤ C0 * γ := ((le_max_right _ _).trans (le_max_right _ _)).trans hbound
  have near : ∀ {d : ℕ} (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin n) ℂ), IsON E →
      len (crd E W) ≤ C0 * γ → nrm (W - cmb E (crd E W)) ≤ s ^ 2 → nrm W ≤ C0 * γ + s ^ 2 := by
    intro d E W hE h1 h2
    have h3 := nrm_le_add_sub W (cmb E (crd E W))
    rw [nrm_cmb hE] at h3
    linarith
  have bN := near EN _ hN.isON lN aN'
  have bM := near EM _ hM.isON lM aM'
  have bK := near EK _ hK.isON lK aK'
  have h1 : s ≤ C0 * γ + s ^ 2 := max_le bN (max_le bM bK)
  obtain ⟨r1, r2, r3⟩ := real_sandwich hC0 hη hγ0 hs0 hs12 hsη h1 hσγ
  refine ⟨r1, r2, ?_, ?_, ?_⟩ <;> linarith

end GlobalTheory.IwSand
