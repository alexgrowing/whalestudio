import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOneSimpleZeroFormAtPoint
import Development.AbelianVarietyTheory.Definitions.Foundations.EtaSixProductDifferentiable

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

open UpperHalfPlane Filter in
open ModularForm (E₄ E₆) in
open scoped MatrixGroups ModularForm Manifold Topology in
private lemma sum_range_zpow_primitiveRoot_pow {ζ : ℂ} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (t : ℤ) :
    ∑ m ∈ Finset.range n, (ζ ^ t) ^ m = if (n : ℤ) ∣ t then (n : ℂ) else 0 := by
  split_ifs with hdvd
  · rw [(hζ.zpow_eq_one_iff_dvd t).2 hdvd]
    simp
  · have hne : ζ ^ t ≠ 1 := fun h1 => hdvd ((hζ.zpow_eq_one_iff_dvd t).1 h1)
    rw [geom_sum_eq hne]
    have : (ζ ^ t) ^ n = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
    rw [this, sub_self, zero_div]

open UpperHalfPlane Filter in
open ModularForm (E₄ E₆) in
open scoped MatrixGroups ModularForm Manifold Topology in
private lemma eventually_ne_zero_nhdsNE_of_simple_zero {E : ℍ → ℂ} (hE : MDiff E) {z : ℂ}
    (hz : 0 < z.im) (he : (E ∘ ofComplex) z = 0) (hd : deriv (E ∘ ofComplex) z ≠ 0) :
    ∀ᶠ w in 𝓝[≠] z, (E ∘ ofComplex) w ≠ 0 := by
  have hU : {w : ℂ | 0 < w.im} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz
  have hdiff : DifferentiableAt ℂ (E ∘ ofComplex) z :=
    (UpperHalfPlane.mdifferentiable_iff.1 hE).differentiableAt hU
  have hc : ContinuousAt (dslope (E ∘ ofComplex) z) z := continuousAt_dslope_same.2 hdiff
  have h1 : ∀ᶠ w in 𝓝 z, dslope (E ∘ ofComplex) z w ≠ 0 :=
    hc.eventually_ne (by rwa [dslope_same])
  filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with w hw hwz
  have hs := sub_smul_dslope (E ∘ ofComplex) z w
  rw [he, sub_zero, smul_eq_mul] at hs
  rw [← hs]
  exact mul_ne_zero (sub_ne_zero.2 hwz) hw

open UpperHalfPlane Filter in
open ModularForm (E₄ E₆) in
open scoped MatrixGroups ModularForm Manifold Topology in
private lemma eq_of_eq_off_simple_zeros' {E A B : ℍ → ℂ} (hE : MDiff E)
    (hzero : ∀ τ : ℍ, E τ = 0 → deriv (E ∘ ofComplex) τ ≠ 0) (hA : MDiff A) (hB : MDiff B)
    (h : ∀ τ, E τ ≠ 0 → A τ = B τ) : A = B := by
  funext τ
  by_cases hτ : E τ = 0
  swap
  · exact h τ hτ
  have hU : {w : ℂ | 0 < w.im} ∈ 𝓝 (τ : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos
  have hAc : ContinuousAt (A ∘ ofComplex) τ :=
    ((UpperHalfPlane.mdifferentiable_iff.1 hA).differentiableAt hU).continuousAt
  have hBc : ContinuousAt (B ∘ ofComplex) τ :=
    ((UpperHalfPlane.mdifferentiable_iff.1 hB).differentiableAt hU).continuousAt
  have hev := eventually_ne_zero_nhdsNE_of_simple_zero hE τ.im_pos (by simpa using hτ) (hzero τ hτ)
  have heq : A ∘ ofComplex =ᶠ[𝓝[≠] (τ : ℂ)] B ∘ ofComplex := by
    filter_upwards [hev] with w hw
    exact h _ hw
  have := tendsto_nhds_unique ((hAc.tendsto.mono_left nhdsWithin_le_nhds).congr' heq)
    (hBc.tendsto.mono_left nhdsWithin_le_nhds)
  simpa using this

open UpperHalfPlane Filter in
open ModularForm (E₄ E₆) in
open scoped MatrixGroups ModularForm Manifold Topology in
private lemma exists_isMF_mul_eq_of_vanishes_on_orbit {Γ : Subgroup SL(2, ℤ)} {N b : ℤ}
    {E H : ℍ → ℂ} {τ₀ : ℍ} (hE : _root_.GlobalTheory.OddFrame.IsMF ⊤ b E)
    (hzero : ∀ τ : ℍ, E τ = 0 → deriv (E ∘ ofComplex) τ ≠ 0 ∧ ∃ γ : SL(2, ℤ), τ = γ • τ₀)
    (hlim : ∃ c, c ≠ 0 ∧ Tendsto E atImInfty (𝓝 c)) (hH : _root_.GlobalTheory.OddFrame.IsMF Γ N H)
    (hHz : ∀ γ : SL(2, ℤ), H (γ • τ₀) = 0) :
    ∃ G, _root_.GlobalTheory.OddFrame.IsMF Γ (N - b) G ∧ ∀ τ, E τ * G τ = H τ := by
  set e := E ∘ ofComplex with he_def
  set h := H ∘ ofComplex with hh_def
  let g : ℂ → ℂ := fun w => if e w = 0 then deriv h w / deriv e w else h w / e w
  have hEe : ∀ τ : ℍ, e τ = E τ := fun τ => by simp [he_def]
  have hHh : ∀ τ : ℍ, h τ = H τ := fun τ => by simp [hh_def]
  have hprod : ∀ τ : ℍ, E τ * g τ = H τ := by
    intro τ
    by_cases h0 : E τ = 0
    · obtain ⟨γ, hγ⟩ := (hzero τ h0).2
      rw [h0, zero_mul, hγ, hHz γ]
    · have h0' : e τ ≠ 0 := by rwa [hEe]
      show E τ * (if e τ = 0 then _ else _) = H τ
      rw [if_neg h0', hEe, hHh, mul_div_cancel₀ _ h0]
  set G : ℍ → ℂ := fun τ => g τ with hG_def
  have hGdiv : ∀ τ, E τ ≠ 0 → G τ = H τ / E τ := fun τ hτ =>
    eq_div_of_mul_eq hτ (by rw [mul_comm]; exact hprod τ)
  have hU' : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hed : DifferentiableOn ℂ e {w : ℂ | 0 < w.im} :=
    UpperHalfPlane.mdifferentiable_iff.1 hE.2.1
  have hhd : DifferentiableOn ℂ h {w : ℂ | 0 < w.im} :=
    UpperHalfPlane.mdifferentiable_iff.1 hH.2.1
  have hgd : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ g z := by
    intro z hz
    have hU := hU'.mem_nhds hz
    have hcoe : ((ofComplex z : ℍ) : ℂ) = z := by rw [ofComplex_apply_of_im_pos hz]
    by_cases hez : e z = 0
    · have hz' : E (ofComplex z) = 0 := hez
      have hdz : deriv e z ≠ 0 := by have := (hzero _ hz').1; rwa [hcoe] at this
      obtain ⟨γ, hγ⟩ := (hzero _ hz').2
      have hhz : h z = 0 := by show H (ofComplex z) = 0; rw [hγ]; exact hHz γ
      have hds : DifferentiableAt ℂ (fun w => dslope h z w / dslope e z w) z :=
        (((Complex.differentiableOn_dslope hU).2 hhd).differentiableAt hU).div
          (((Complex.differentiableOn_dslope hU).2 hed).differentiableAt hU) (by rwa [dslope_same])
      apply hds.congr_of_eventuallyEq
      have hc : ContinuousAt (dslope e z) z := continuousAt_dslope_same.2 (hed.differentiableAt hU)
      filter_upwards [hc.eventually_ne (by rwa [dslope_same] : dslope e z z ≠ 0)] with w hw
      by_cases hwz : w = z
      · rw [hwz]
        show (if e z = 0 then _ else _) = _
        rw [if_pos hez, dslope_same, dslope_same]
      · have he' : e w = (w - z) * dslope e z w := by
          have := sub_smul_dslope e z w
          rw [hez, sub_zero, smul_eq_mul] at this
          exact this.symm
        have hh' : h w = (w - z) * dslope h z w := by
          have := sub_smul_dslope h z w
          rw [hhz, sub_zero, smul_eq_mul] at this
          exact this.symm
        have hew : e w ≠ 0 := by rw [he']; exact mul_ne_zero (sub_ne_zero.2 hwz) hw
        show (if e w = 0 then _ else _) = _
        rw [if_neg hew, he', hh', mul_div_mul_left _ _ (sub_ne_zero.2 hwz)]
    · have hq : DifferentiableAt ℂ (fun w => h w / e w) z :=
        (hhd.differentiableAt hU).div (hed.differentiableAt hU) hez
      apply hq.congr_of_eventuallyEq
      filter_upwards [(hed.differentiableAt hU).continuousAt.eventually_ne hez] with w hw
      show (if e w = 0 then _ else _) = _
      rw [if_neg hw]
  have hGm : MDiff G := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    intro z hz
    have hU := hU'.mem_nhds hz
    have heq : G ∘ ofComplex =ᶠ[𝓝 z] g := by
      filter_upwards [hU] with w hw
      simp only [Function.comp_apply, hG_def]
      rw [ofComplex_apply_of_im_pos hw]
    exact ((hgd z hz).congr_of_eventuallyEq heq).differentiableWithinAt
  have hkey : ∀ (x : SL(2, ℤ)) (τ : ℍ), E τ ≠ 0 →
      (G ∣[N - b] x) τ = (H ∣[N] x) τ / E τ := by
    intro x τ hτ
    have hEx := congrFun (hE.slash_top x) τ
    rw [ModularForm.SL_slash_apply] at hEx
    rw [ModularForm.SL_slash_apply, ModularForm.SL_slash_apply]
    set D := denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) x)) (τ : ℂ) with hD
    have hD0 : D ≠ 0 := denom_ne_zero _ _
    have hEx' : E (x • τ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hEx
      exact hτ hEx.symm
    rw [hGdiv _ hEx', ← hEx, show -(N - b) = -N - -b by ring, zpow_sub₀ hD0]
    have hb0 : D ^ (-b) ≠ 0 := zpow_ne_zero _ hD0
    field_simp
  refine ⟨G, ⟨fun γ hγ => ?_, hGm, fun x => ?_⟩, hprod⟩
  · apply eq_of_eq_off_simple_zeros' hE.2.1 (fun τ hτ => (hzero τ hτ).1)
      (_root_.GlobalTheory.OddFrame.mdiff_slash hGm _ _) hGm
    intro τ hτ
    rw [hkey γ τ hτ, hH.1 γ hγ, hGdiv τ hτ]
  · obtain ⟨c, hc, hEc⟩ := hlim
    have hinv : BoundedAtFilter atImInfty (fun τ => (E τ)⁻¹) := by
      unfold BoundedAtFilter
      exact (hEc.inv₀ hc).isBigO_one ℝ
    have hbd := (hH.2.2 x).mul hinv
    unfold IsBoundedAtImInfty BoundedAtFilter at hbd ⊢
    refine hbd.congr' ?_ EventuallyEq.rfl
    filter_upwards [hEc.eventually_ne hc] with τ hτ
    rw [Pi.mul_apply, hkey x τ hτ, div_eq_mul_inv]

open UpperHalfPlane Filter in
open ModularForm (E₄ E₆) in
open scoped MatrixGroups ModularForm Manifold Topology in

theorem _root_.GlobalTheory.OddFrame.reduces_of_det_evM_eq_zero : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (τ₀ : ℍ), _root_.GlobalTheory.OddFrame.IsReps Γ s → (∀ j, Odd (w j) ∧ _root_.GlobalTheory.OddFrame.IsMF Γ (w j) (F j)) →
    (_root_.GlobalTheory.OddFrame.evM s w F τ₀).det = 0 → _root_.GlobalTheory.OddFrame.Reduces Γ w F := by
  intro Γ r s w F τ₀ hs hF hdet
  classical
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hrow : ∀ i, ∑ j, v j * (F j ∣[w j] s i) τ₀ = 0 := by
    intro i
    have := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, _root_.GlobalTheory.OddFrame.evM, Matrix.of_apply,
      Pi.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hrel : ∀ x : SL(2, ℤ), ∑ j, v j * (F j ∣[w j] x) τ₀ = 0 :=
    fun x => hs.sum_eq_zero hF v τ₀ hrow x
  obtain ⟨n, a, b, E, u, hu, hn, hζ, hab, hba, hE, hzero, hlim, hforms⟩ :=
    _root_.GlobalTheory.LevelOneLocal.exists_local_data τ₀
  set ζ := denom (Matrix.SpecialLinearGroup.toGL
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) u)) (τ₀ : ℂ) with hζdef
  have hζ0 : ζ ≠ 0 := denom_ne_zero _ _
  have hpow : ∀ (m : ℕ) (x : SL(2, ℤ)) (j : Fin r),
      (F j ∣[w j] (x * u ^ m)) τ₀ = (F j ∣[w j] x) τ₀ * ζ ^ (-((m : ℤ) * w j)) := by
    intro m
    induction m with
    | zero => intro x j; simp
    | succ m ih =>
      intro x j
      rw [pow_succ, ← mul_assoc, _root_.GlobalTheory.OddFrame.slash_mul_apply, hu, ih, mul_assoc,
        ← zpow_add₀ hζ0]
      congr 2
      push_cast
      ring
  have hrelm : ∀ (m : ℕ) (x : SL(2, ℤ)),
      ∑ j, v j * (F j ∣[w j] x) τ₀ * ζ ^ (-((m : ℤ) * w j)) = 0 := by
    intro m x
    rw [← hrel (x * u ^ m)]
    exact Finset.sum_congr rfl fun j _ => by rw [hpow, mul_assoc]
  obtain ⟨j₁, hj₁⟩ : ∃ j, v j ≠ 0 := by simpa using Function.ne_iff.1 hv0
  have hclass : ∀ x : SL(2, ℤ),
      ∑ j, (if (n : ℤ) ∣ w j - w j₁ then v j else 0) * (F j ∣[w j] x) τ₀ = 0 := by
    intro x
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hsum : ∑ m ∈ Finset.range n, ζ ^ ((m : ℤ) * w j₁) *
        ∑ j, v j * (F j ∣[w j] x) τ₀ * ζ ^ (-((m : ℤ) * w j)) = 0 :=
      Finset.sum_eq_zero fun m _ => by rw [hrelm, mul_zero]
    have hswap : ∑ m ∈ Finset.range n, ζ ^ ((m : ℤ) * w j₁) *
        ∑ j, v j * (F j ∣[w j] x) τ₀ * ζ ^ (-((m : ℤ) * w j)) =
        ∑ j, v j * (F j ∣[w j] x) τ₀ * ∑ m ∈ Finset.range n, (ζ ^ (w j₁ - w j)) ^ m := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
      rw [← zpow_natCast, ← zpow_mul,
        show (w j₁ - w j) * (m : ℤ) = (m : ℤ) * w j₁ + -((m : ℤ) * w j) by ring, zpow_add₀ hζ0]
      ring
    rw [hswap] at hsum
    simp_rw [sum_range_zpow_primitiveRoot_pow hζ] at hsum
    have hmul : (n : ℂ) * ∑ j, (if (n : ℤ) ∣ w j - w j₁ then v j else 0) *
        (F j ∣[w j] x) τ₀ = 0 := by
      refine Eq.trans ?_ hsum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hd : (n : ℤ) ∣ w j - w j₁
      · rw [if_pos hd, if_pos (dvd_sub_comm.1 hd)]
        ring
      · have hd' : ¬ (n : ℤ) ∣ w j₁ - w j := fun h' => hd (dvd_sub_comm.1 h')
        simp [hd, hd']
    exact (mul_eq_zero.1 hmul).resolve_left hn0
  set P : Fin r → Prop := fun j => v j ≠ 0 ∧ (n : ℤ) ∣ w j - w j₁ with hP
  have hne : (Finset.univ.filter P).Nonempty :=
    ⟨j₁, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj₁, by simp⟩⟩
  obtain ⟨j₀, hj₀S, hj₀max⟩ := (Finset.univ.filter P).exists_max_image w hne
  have hj₀ : P j₀ := (Finset.mem_filter.1 hj₀S).2
  have hforms' : ∀ j, ∃ f : ℍ → ℂ,
      _root_.GlobalTheory.OddFrame.IsMF ⊤ (w j₀ - w j + a) f ∧ (P j → f τ₀ ≠ 0) := by
    intro j
    by_cases hj : P j
    · obtain ⟨f, hf, hf0⟩ := hforms (w j₀ - w j)
        (sub_nonneg.2 (hj₀max j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)))
        (by have := dvd_sub hj₀.2 hj.2; rwa [sub_sub_sub_cancel_right] at this)
      exact ⟨f, hf, fun _ => hf0⟩
    · exact ⟨0, _root_.GlobalTheory.OddFrame.IsMF.zero _ _, fun h' => absurd h' hj⟩
  choose f hfmf hfne using hforms'
  set e : Fin r → ℍ → ℂ := fun j => (if P j then v j / f j τ₀ else 0) • f j with he_def
  have he_mf : ∀ j, _root_.GlobalTheory.OddFrame.IsMF ⊤ (w j₀ - w j + a) (e j) :=
    fun j => (hfmf j).smul _
  have he0 : ∀ j, e j τ₀ = if (n : ℤ) ∣ w j - w j₁ then v j else 0 := by
    intro j
    simp only [he_def, Pi.smul_apply, smul_eq_mul]
    by_cases hj : P j
    · rw [if_pos hj, if_pos hj.2, div_mul_cancel₀ _ (hfne j hj)]
    · rw [if_neg hj, zero_mul]
      by_cases hd : (n : ℤ) ∣ w j - w j₁
      · rw [if_pos hd]
        exact (not_not.1 fun hv' => hj ⟨hv', hd⟩).symm
      · rw [if_neg hd]
  set H : ℍ → ℂ := ∑ j, e j * F j with hH_def
  have hHmf : _root_.GlobalTheory.OddFrame.IsMF Γ (w j₀ + a) H :=
    _root_.GlobalTheory.OddFrame.IsMF.sum _ fun j _ =>
      ((he_mf j).mono le_top).mul (hF j).2 (by ring)
  have hHslash : ∀ (x : SL(2, ℤ)) (τ : ℍ),
      (H ∣[w j₀ + a] x) τ = ∑ j, e j τ * (F j ∣[w j] x) τ := by
    intro x τ
    rw [ModularForm.SL_slash_apply, hH_def, Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hex := congrFun ((he_mf j).slash_top x) τ
    rw [ModularForm.SL_slash_apply] at hex
    rw [ModularForm.SL_slash_apply, ← hex, Pi.mul_apply, mul_mul_mul_comm,
      ← zpow_add₀ (denom_ne_zero _ _)]
    congr 2
    ring
  have hHz : ∀ γ : SL(2, ℤ), H (γ • τ₀) = 0 := by
    intro γ
    have h1 : (H ∣[w j₀ + a] γ) τ₀ = 0 := by
      rw [hHslash]
      simp_rw [he0]
      exact hclass γ
    rw [ModularForm.SL_slash_apply] at h1
    exact (mul_eq_zero.1 h1).resolve_right (zpow_ne_zero _ (denom_ne_zero _ _))
  obtain ⟨G, hG, hEG⟩ := exists_isMF_mul_eq_of_vanishes_on_orbit hE hzero hlim hHmf hHz
  refine ⟨j₀, w j₀ + a - b, G, E, e, by linarith, ?_, hG, fun j => (he_mf j).2.1, ?_, ?_⟩
  · rw [show w j₀ + a - b = w j₀ - (b - a) by ring]
    exact (hF j₀).1.sub_even hba
  · intro h0
    have := congrFun h0 τ₀
    rw [he0, if_pos hj₀.2, Pi.zero_apply] at this
    exact hj₀.1 this
  · intro x τ
    rw [← hHslash]
    have hEGf : H = E * G := funext fun τ => (hEG τ).symm
    have hm := ModularForm.mul_slash_SL2 b (w j₀ + a - b) x E G
    rw [show b + (w j₀ + a - b) = w j₀ + a by ring, hE.slash_top] at hm
    rw [hEGf, hm]
    rfl

end GlobalTheory.OddFrame
