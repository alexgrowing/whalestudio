import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnMeasurableSetReg

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem cn_wt_nonneg {a : ℕ} (j : Fin a → ℕ) (f : ℕ) {t : Fin a → ℝ} (ht : t ∈ cn_Reg a) : 0 ≤ cn_wt j f t :=
  Finset.prod_nonneg fun x _ => by have := (ht.2 x).1; positivity

theorem cn_cnt_nonneg {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) {de : ℝ} (hde : 0 ≤ de) {t : Fin a → ℝ} (ht : t ∈ cn_Reg a) :
    0 ≤ cn_cnt j n0 f de t :=
  Finset.prod_nonneg fun r _ => by have := (cn_la_mem ht r).1; positivity

def cn_hT (f n0 j : ℕ) : ℝ → ℝ :=
  (Set.Ioo (0 : ℝ) (1 / 2)).indicator fun s : ℝ => s ^ (2 * j * n0 * f) * (2 * (f : ℝ) * j / s)

theorem cn_hT_nonneg (f n0 j : ℕ) (s : ℝ) : 0 ≤ cn_hT f n0 j s :=
  Set.indicator_nonneg (fun s hs => by have := hs.1; positivity) s

theorem cn_hT_of_mem (f n0 j : ℕ) {s : ℝ} (h0 : 0 < s) (h1 : s < 1 / 2) :
    cn_hT f n0 j s = s ^ (2 * j * n0 * f) * (2 * (f : ℝ) * j / s) :=
  Set.indicator_of_mem (show s ∈ Set.Ioo (0 : ℝ) (1 / 2) from ⟨h0, h1⟩) _

def cn_hL (f j : ℕ) (ts : ℝ) : ℝ → ℝ := (Set.Ico ts (1 / 2)).indicator fun s : ℝ => 2 * (f : ℝ) * j / s

theorem cn_hL_nonneg (f j : ℕ) {ts : ℝ} (h0 : 0 < ts) (s : ℝ) : 0 ≤ cn_hL f j ts s :=
  Set.indicator_nonneg (fun s hs => by have := lt_of_lt_of_le h0 hs.1; positivity) s

theorem cn_hL_of_mem (f j : ℕ) {ts s : ℝ} (h0 : ts ≤ s) (h1 : s < 1 / 2) : cn_hL f j ts s = 2 * (f : ℝ) * j / s :=
  Set.indicator_of_mem (show s ∈ Set.Ico ts (1 / 2) from ⟨h0, h1⟩) _

theorem cn_hL_measurable (f j : ℕ) (ts : ℝ) : Measurable (cn_hL f j ts) :=
  (measurable_const.div measurable_id).indicator measurableSet_Ico

theorem cn_dens_wt_le {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) {t : Fin a → ℝ} (ht : t ∈ cn_Reg a) :
    cn_dens j n0 f t * cn_wt j f t ≤ ∏ x, cn_hT f n0 (j x) (t x) := by
  have e1 : ∏ x, cn_hT f n0 (j x) (t x) = (∏ x, t x ^ (2 * j x * n0 * f)) * cn_wt j f t := by
    unfold cn_wt
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun x _ => cn_hT_of_mem f n0 (j x) (ht.2 x).1 (ht.2 x).2
  rw [e1]
  exact mul_le_mul_of_nonneg_right (cn_dens_le j n0 f ht) (cn_wt_nonneg j f ht)

theorem cn_int_hT_le (f n0 j : ℕ) (hf : 1 ≤ f) (hj : 1 ≤ j) (hn : 1 ≤ n0) : ∫ s, cn_hT f n0 j s ≤ 1 := by
  have h := (cn_int_tau f j n0 hf hj hn).2
  unfold cn_hT
  rw [h]
  have h1 : ((1 : ℝ) / 2) ^ (2 * j * n0 * f) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : (1 : ℝ) ≤ n0 := by exact_mod_cast hn
  rw [div_le_one (by linarith)]
  linarith

theorem cn_int_dens_le {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) (hf : 1 ≤ f) (hj : ∀ x, 1 ≤ j x) (hn : 1 ≤ n0) :
    ∫⁻ t in cn_Reg a, ENNReal.ofReal (cn_dens j n0 f t * cn_wt j f t) ≤ 1 := by
  have s1 : ∫⁻ t in cn_Reg a, ENNReal.ofReal (cn_dens j n0 f t * cn_wt j f t) ≤
      ∫⁻ t in cn_Reg a, ENNReal.ofReal (∏ x, cn_hT f n0 (j x) (t x)) :=
    setLIntegral_mono' (cn_measurableSet_Reg a) fun t ht => ENNReal.ofReal_le_ofReal (cn_dens_wt_le j n0 f ht)
  have s2 : ∫⁻ t in cn_Reg a, ENNReal.ofReal (∏ x, cn_hT f n0 (j x) (t x)) ≤
      ∫⁻ t : Fin a → ℝ, ENNReal.ofReal (∏ x, cn_hT f n0 (j x) (t x)) := setLIntegral_le_lintegral _ _
  have s3 := cn_lint_prod (fun x => cn_hT f n0 (j x)) (fun x => (cn_int_tau f (j x) n0 hf (hj x) hn).1)
    (fun x s => cn_hT_nonneg f n0 (j x) s)
  have s4 : ENNReal.ofReal (∏ x, ∫ s, cn_hT f n0 (j x) s) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Finset.prod_le_one (fun x _ => integral_nonneg (cn_hT_nonneg f n0 (j x)))
      fun x _ => cn_int_hT_le f n0 (j x) hf (hj x) hn)
  exact s1.trans (s2.trans (s3.le.trans s4))

def cn_Psi {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) (de ts : ℝ) : (Fin a → ℝ) → ℝ≥0∞ := fun t =>
  ENNReal.ofReal (cn_cnt j n0 f de t) * ({t : Fin a → ℝ | ∀ x, ts ≤ t x}.indicator 1 t)

theorem cn_measurable_Psi {a : ℕ} (j : Fin a → ℕ) (n0 f : ℕ) (de ts : ℝ) : Measurable (cn_Psi j n0 f de ts) := by
  have hs : MeasurableSet {t : Fin a → ℝ | ∀ x, ts ≤ t x} := by
    have : {t : Fin a → ℝ | ∀ x, ts ≤ t x} = ⋂ x, {t : Fin a → ℝ | ts ≤ t x} := by
      ext t; simp
    rw [this]
    exact MeasurableSet.iInter fun x => measurableSet_le measurable_const (measurable_pi_apply x)
  exact (ENNReal.measurable_ofReal.comp (cn_measurable_cnt j n0 f de)).mul (measurable_one.indicator hs)

theorem cn_Psi_dens_le {a : ℕ} (j : Fin a → ℕ) (n0 f n q : ℕ) (de ts : ℝ) (hn : n0 + 2 * ∑ x, j x = n)
    (hq : ∑ x, j x ≤ q) (hde : 0 ≤ de) (hsm : de * q * n * f ≤ 1 / 100) {t : Fin a → ℝ} (ht : t ∈ cn_Reg a) :
    cn_Psi j n0 f de ts t * ENNReal.ofReal (cn_dens j n0 f t * cn_wt j f t) ≤
      2 * ENNReal.ofReal (∏ x, cn_hL f (j x) ts (t x)) := by
  unfold cn_Psi
  by_cases h2 : ∀ x, ts ≤ t x
  · rw [Set.indicator_of_mem (show t ∈ {t : Fin a → ℝ | ∀ x, ts ≤ t x} from h2), Pi.one_apply, mul_one,
      ← ENNReal.ofReal_mul (cn_cnt_nonneg j n0 f hde ht)]
    have e1 : ∏ x, cn_hL f (j x) ts (t x) = cn_wt j f t :=
      Finset.prod_congr rfl fun x _ => cn_hL_of_mem f (j x) (h2 x) (ht.2 x).2
    rw [e1, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (cn_cnt_dens_le j n0 f n q de hn hq hde hsm ht) (cn_wt_nonneg j f ht)
  · rw [Set.indicator_of_notMem (show t ∉ {t : Fin a → ℝ | ∀ x, ts ≤ t x} from h2)]
    simp

theorem cn_int_near_le {a : ℕ} (j : Fin a → ℕ) (n0 f n q : ℕ) (de ts : ℝ) (hn : n0 + 2 * ∑ x, j x = n)
    (hq : ∑ x, j x ≤ q) (hde : 0 ≤ de) (hsm : de * q * n * f ≤ 1 / 100) (h0 : 0 < ts) (h1 : ts ≤ 1 / 2) :
    ∫⁻ t in cn_Reg a, cn_Psi j n0 f de ts t * ENNReal.ofReal (cn_dens j n0 f t * cn_wt j f t) ≤
      2 * ENNReal.ofReal (∏ x, (2 * (f : ℝ) * j x * Real.log (1 / (2 * ts)))) := by
  have s1 : ∫⁻ t in cn_Reg a, cn_Psi j n0 f de ts t * ENNReal.ofReal (cn_dens j n0 f t * cn_wt j f t) ≤
      ∫⁻ t in cn_Reg a, 2 * ENNReal.ofReal (∏ x, cn_hL f (j x) ts (t x)) :=
    setLIntegral_mono' (cn_measurableSet_Reg a) fun t ht => cn_Psi_dens_le j n0 f n q de ts hn hq hde hsm ht
  have s2 : ∫⁻ t in cn_Reg a, 2 * ENNReal.ofReal (∏ x, cn_hL f (j x) ts (t x)) ≤
      ∫⁻ t : Fin a → ℝ, 2 * ENNReal.ofReal (∏ x, cn_hL f (j x) ts (t x)) := setLIntegral_le_lintegral _ _
  have hm : Measurable fun t : Fin a → ℝ => ENNReal.ofReal (∏ x, cn_hL f (j x) ts (t x)) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun x _ =>
      (cn_hL_measurable f (j x) ts).comp (measurable_pi_apply x))
  have s3 : ∫⁻ t : Fin a → ℝ, 2 * ENNReal.ofReal (∏ x, cn_hL f (j x) ts (t x)) =
      2 * ∫⁻ t : Fin a → ℝ, ENNReal.ofReal (∏ x, cn_hL f (j x) ts (t x)) := lintegral_const_mul _ hm
  have s4 := cn_lint_prod (fun x => cn_hL f (j x) ts) (fun x => (cn_int_log f (j x) ts h0 h1).1)
    (fun x s => cn_hL_nonneg f (j x) h0 s)
  have s5 : ∏ x, ∫ s, cn_hL f (j x) ts s = ∏ x, (2 * (f : ℝ) * j x * Real.log (1 / (2 * ts))) :=
    Finset.prod_congr rfl fun x _ => (cn_int_log f (j x) ts h0 h1).2
  rw [s5] at s4
  rw [s4] at s3
  exact s1.trans (s2.trans s3.le)

theorem cn_sum_types_le (q : ℕ) (T : ∀ J : ℕ, Composition J → ℝ≥0∞) (B : ℝ≥0∞)
    (h : ∀ J ∈ Finset.Icc 1 q, ∀ c, T J c ≤ B) : ∑ J ∈ Finset.Icc 1 q, ∑ c, T J c ≤ 2 ^ q * B := by
  calc ∑ J ∈ Finset.Icc 1 q, ∑ c, T J c ≤ ∑ J ∈ Finset.Icc 1 q, (Fintype.card (Composition J) : ℝ≥0∞) * B := by
        refine Finset.sum_le_sum fun J hJ => ?_
        refine le_trans (Finset.sum_le_sum fun c _ => h J hJ c) ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        rfl
    _ = ((∑ J ∈ Finset.Icc 1 q, Fintype.card (Composition J) : ℕ) : ℝ≥0∞) * B := by
        rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ 2 ^ q * B := by
        refine mul_le_mul_left ?_ _
        have := Formalism.HermitianLatticeCounting.Final.S7.typeCount q
        exact_mod_cast this

namespace CSize

variable {X : CData} (S : CSize X)

theorem type_mass (hD : S.Density) {J : ℕ} (c : Composition J) (hJ1 : 1 ≤ J) (hJq : J ≤ X.qq) (hn0 : 1 ≤ X.I.n - 2 * J) :
    X.μ (S.str J c) ≤ ENNReal.ofReal (X.I.vol X.μf X.fund * S.kap J c) := by
  have h := hD J c hJ1 hJq (fun _ => 1) measurable_const
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ] at h
  refine h.trans (mul_le_of_le_one_right' ?_)
  exact cn_int_dens_le c.blocksFun _ _ (one_le_autInst_f X.I) c.one_le_blocksFun hn0

theorem compl_Mod_subset (hS : S.Strata) {C₁ : ℝ} (hts : cn_tauS X C₁ ≤ 1 / 2) :
    (S.Mod C₁)ᶜ ⊆ ⋃ J ∈ Finset.Icc 1 X.qq, ⋃ c ∈ (Finset.univ : Finset (Composition J)), S.str J c := by
  intro x hx
  have hx' : S.tau1 x < cn_tauS X C₁ := not_le.1 hx
  rcases hS.2.2.2.1 x with h0 | ⟨J, h1, h2, c, hc⟩
  · have := hS.2.2.2.2.1 x h0
    linarith
  · simp only [Set.mem_iUnion]
    exact ⟨J, Finset.mem_Icc.2 ⟨h1, h2⟩, c, Finset.mem_univ _, hc⟩

theorem compl_Mod_le (hS : S.Strata) (hD : S.Density) {C₁ : ℝ} (hts : cn_tauS X C₁ ≤ 1 / 2) (hn : 2 * X.qq + 1 ≤ X.I.n) :
    X.μ (S.Mod C₁)ᶜ ≤ ∑ J ∈ Finset.Icc 1 X.qq, ∑ c : Composition J, ENNReal.ofReal (X.I.vol X.μf X.fund * S.kap J c) := by
  refine le_trans (measure_mono (S.compl_Mod_subset hS hts)) ?_
  refine le_trans (measure_biUnion_finset_le _ _) (Finset.sum_le_sum fun J hJ => ?_)
  refine le_trans (measure_biUnion_finset_le _ _) (Finset.sum_le_sum fun c _ => ?_)
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hJ
  exact S.type_mass hD c h1 h2 (by omega)

theorem near_le (hS : S.Strata) (hD : S.Density) {εN δ : ℝ} (hN : S.NearCount εN δ) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    {C₁ : ℝ} (h0 : 0 < cn_tauS X C₁) (hts : cn_tauS X C₁ ≤ 1 / 2) (hn : 2 * X.qq + 1 ≤ X.I.n) (hδ : 0 ≤ δ)
    (hsm : δ * X.qq * X.I.n * X.I.f ≤ 1 / 100) :
    ∫⁻ x in S.Mod C₁, X.nearS εN x ∂X.μ ≤
      ∑ J ∈ Finset.Icc 1 X.qq, ∑ c : Composition J,
        ENNReal.ofReal (fdegAll X.I X.σ X.w * (X.e 1).re) * (ENNReal.ofReal (X.I.vol X.μf X.fund * S.kap J c) *
          (2 * ENNReal.ofReal (∏ a, (2 * (X.I.f : ℝ) * c.blocksFun a * Real.log (1 / (2 * cn_tauS X C₁)))))) := by
  set M : ℝ≥0∞ := ENNReal.ofReal (fdegAll X.I X.σ X.w * (X.e 1).re) with hM
  set G : ∀ J : ℕ, Composition J → X.I.GA → ℝ≥0∞ := fun J c =>
    (S.str J c).indicator fun x => M * cn_Psi c.blocksFun (X.I.n - 2 * J) X.I.f δ (cn_tauS X C₁) (S.tau J c x) with hG
  have hGm : ∀ J c, Measurable (G J c) := fun J c =>
    (((cn_measurable_Psi _ _ _ _ _).comp (hS.2.2.1 J c)).const_mul M).indicator (hS.2.1 J c)
  have hpt : ∀ x ∈ S.Mod C₁, X.nearS εN x ≤ ∑ J ∈ Finset.Icc 1 X.qq, ∑ c : Composition J, G J c x := by
    intro x hx
    rcases hS.2.2.2.1 x with hx0 | ⟨J, h1, h2, c, hc⟩
    · have := cn_nearS_le X hX εN x 0 fun T hT => by
        have : T = ∅ := Finset.eq_empty_of_forall_notMem fun γ hγ =>
          (hT γ hγ).2 (hN.1 x hx0 γ (hT γ hγ).1.1 (hT γ hγ).1.2)
        simp [this]
      simp only [ENNReal.ofReal_zero, mul_zero] at this
      exact le_trans this zero_le
    · have h3 := cn_nearS_le X hX εN x _ (hN.2 J c x hc)
      have h4 : G J c x = M * ENNReal.ofReal (cn_cnt c.blocksFun (X.I.n - 2 * J) X.I.f δ (S.tau J c x)) := by
        simp only [hG]
        rw [Set.indicator_of_mem hc]
        unfold cn_Psi
        rw [Set.indicator_of_mem (show S.tau J c x ∈ {t : Fin c.length → ℝ | ∀ a, cn_tauS X C₁ ≤ t a} from
          fun a => le_trans hx (hS.2.2.2.2.2.2 J c x hc a)), Pi.one_apply, mul_one]
      rw [← h4] at h3
      refine le_trans h3 ?_
      refine le_trans ?_ (Finset.single_le_sum (f := fun J => ∑ c : Composition J, G J c x) (fun _ _ => zero_le)
        (Finset.mem_Icc.2 ⟨h1, h2⟩))
      exact Finset.single_le_sum (f := fun c => G J c x) (fun _ _ => zero_le) (Finset.mem_univ c)
  calc ∫⁻ x in S.Mod C₁, X.nearS εN x ∂X.μ
      ≤ ∫⁻ x in S.Mod C₁, ∑ J ∈ Finset.Icc 1 X.qq, ∑ c : Composition J, G J c x ∂X.μ :=
        setLIntegral_mono' (S.measurableSet_Mod hS C₁) hpt
    _ ≤ ∫⁻ x, ∑ J ∈ Finset.Icc 1 X.qq, ∑ c : Composition J, G J c x ∂X.μ := setLIntegral_le_lintegral _ _
    _ = ∑ J ∈ Finset.Icc 1 X.qq, ∑ c : Composition J, ∫⁻ x, G J c x ∂X.μ := by
        rw [lintegral_finsetSum _ fun J _ => Finset.measurable_sum _ fun c _ => hGm J c]
        exact Finset.sum_congr rfl fun J _ => lintegral_finsetSum _ fun c _ => hGm J c
    _ ≤ _ := by
        refine Finset.sum_le_sum fun J hJ => Finset.sum_le_sum fun c _ => ?_
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hJ
        simp only [hG]
        rw [lintegral_indicator (hS.2.1 J c),
          lintegral_const_mul M (show Measurable fun x => cn_Psi c.blocksFun (X.I.n - 2 * J) X.I.f δ (cn_tauS X C₁)
            (S.tau J c x) from (cn_measurable_Psi _ _ _ _ _).comp (hS.2.2.1 J c))]
        refine mul_le_mul_right ?_ _
        refine le_trans (hD J c h1 h2 _ (cn_measurable_Psi _ _ _ _ _)) (mul_le_mul_right ?_ _)
        exact cn_int_near_le c.blocksFun _ _ X.I.n X.qq δ _ (by rw [c.sum_blocksFun]; omega)
          (by rw [c.sum_blocksFun]; exact h2) hδ hsm h0 hts

end CSize

end Formalism.MainNotions.LeviCoordinates

end
