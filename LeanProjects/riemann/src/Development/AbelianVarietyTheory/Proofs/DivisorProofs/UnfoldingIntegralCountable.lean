import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIndicatorTsumOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainUnfoldSubgroupStatement

open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.UnfoldSemidirect

theorem sFinite_of_fd {X : Type} [Group X] [MeasurableSpace X] (μ : Measure X) (H : Subgroup X)
    (𝓕 : Set X) (hH : Countable H) (hL : ∀ g : X, Measurable (g * ·)) (hμ : μ.IsMulLeftInvariant)
    (h𝓕 : IsFundamentalDomain H 𝓕 μ) (hfin : μ 𝓕 ≠ ⊤) : SFinite μ := by
  haveI := hH; haveI := hμ
  haveI : MeasurableConstSMul H X := ⟨fun g => hL g.1⟩
  haveI : SMulInvariantMeasure H X μ := ⟨fun g s hs => by
    show μ ((fun x => (g : X) * x) ⁻¹' s) = μ s
    rw [← Measure.map_apply (hL g.1) hs, map_mul_left_eq_self]⟩
  haveI : ∀ g : H, IsFiniteMeasure (μ.restrict (g • 𝓕)) := fun g =>
    ⟨by rw [Measure.restrict_apply_univ, measure_smul]; exact hfin.lt_top⟩
  rw [← h𝓕.sum_restrict]
  infer_instance

theorem ae_zero_of_iter {N G₁ L Kt : Type} [MeasurableSpace N] [MeasurableSpace G₁]
    [MeasurableSpace L] [MeasurableSpace Kt] (μN : Measure N) (ν : Measure G₁) (μL : Measure L)
    (μK : Measure Kt) (h1 : SFinite μN) (h2 : SFinite ν) (h3 : SFinite μL)
    (Φ : N × G₁ × L × Kt → ENNReal) (hΦ : Measurable Φ)
    (h0 : ∫⁻ k, ∫⁻ l, ∫⁻ g₀, ∫⁻ n, Φ (n, g₀, l, k) ∂μN ∂ν ∂μL ∂μK = 0) :
    ∀ᵐ k ∂μK, ∀ᵐ l ∂μL, ∀ᵐ g₀ ∂ν, ∫⁻ n, Φ (n, g₀, l, k) ∂μN = 0 := by
  haveI := h1; haveI := h2; haveI := h3
  have m1 : Measurable (fun q : G₁ × L × Kt => ∫⁻ n, Φ (n, q) ∂μN) := hΦ.lintegral_prod_left'
  have m2 : Measurable (fun q : L × Kt => ∫⁻ g₀, ∫⁻ n, Φ (n, g₀, q) ∂μN ∂ν) :=
    m1.lintegral_prod_left'
  have m3 : Measurable (fun k : Kt => ∫⁻ l, ∫⁻ g₀, ∫⁻ n, Φ (n, g₀, l, k) ∂μN ∂ν ∂μL) :=
    m2.lintegral_prod_left'
  have hk := (lintegral_eq_zero_iff m3).1 h0
  filter_upwards [hk] with k hk
  have m2k : Measurable (fun l : L => ∫⁻ g₀, ∫⁻ n, Φ (n, g₀, l, k) ∂μN ∂ν) :=
    m2.comp (measurable_id.prodMk measurable_const)
  have hl := (lintegral_eq_zero_iff m2k).1 hk
  filter_upwards [hl] with l hl
  have m1kl : Measurable (fun g₀ : G₁ => ∫⁻ n, Φ (n, g₀, l, k) ∂μN) :=
    m1.comp (measurable_id.prodMk measurable_const)
  exact (lintegral_eq_zero_iff m1kl).1 hl

theorem setLIntegral_count_mul {G : Type} [Group G] [MeasurableSpace G] (N Q : Subgroup G)
    (μN : Measure N) (𝓕 : Set N) (D B : Set G) (h : G) (a : ENNReal)
    (hh : Measurable (fun n : N => n.1 * h)) (hB : MeasurableSet B)
    (hχ : ∀ y ∉ B, ∑' q : Q, D.indicator (1 : G → ENNReal) (q.1 * y) = 1)
    (h0 : (∫⁻ n, B.indicator (1 : G → ENNReal) (n.1 * h) ∂μN) * a = 0) :
    (∫⁻ n in 𝓕, ∑' q : Q, D.indicator (1 : G → ENNReal) (q.1 * (n.1 * h)) ∂μN) * a = μN 𝓕 * a := by
  classical
  rcases mul_eq_zero.1 h0 with h1 | h1
  · have hfun : (fun n : N => B.indicator (1 : G → ENNReal) (n.1 * h))
        = ((fun n : N => n.1 * h) ⁻¹' B).indicator 1 := by
      funext n; simp [Set.indicator_apply]
    have hpre : μN ((fun n : N => n.1 * h) ⁻¹' B) = 0 := by
      rw [← lintegral_indicator_one (hh hB), ← hfun]; exact h1
    have hae : ∀ᵐ n ∂μN, ∑' q : Q, D.indicator (1 : G → ENNReal) (q.1 * (n.1 * h)) = 1 := by
      rw [ae_iff]
      refine measure_mono_null ?_ hpre
      intro n hn
      by_contra hnB
      exact hn (hχ _ hnB)
    rw [lintegral_congr_ae (ae_restrict_of_ae hae)]
    simp
  · simp [h1]

theorem lintegral_fundamentalDomain_eq : ∀ {G G₁ L Kt : Type} [Group G] [MeasurableSpace G] [Group G₁] [MeasurableSpace G₁] [MeasurableSpace L] [MeasurableSpace Kt]
    (μG : Measure G) (ν : Measure G₁) (μL : Measure L) (μK : Measure Kt) (N Q : Subgroup G) (Γ : Subgroup G₁) (μN : Measure N)
    (kk : Kt → G) (m : L → G₁ → G) (ι : G₁ → G) (w : L → ENNReal) (c : ENNReal) (dom : Set G₁) (𝓕 : Set N),
    Countable Q → Countable Γ → SFinite ν → SFinite μL →
    (∀ g : G, Measurable (g * ·)) → (∀ g : G₁, Measurable (g * ·)) → (∀ g : G, Measurable (· * g)) →
    Measurable (fun p : N × G₁ × L × Kt => p.1.1 * m p.2.2.1 p.2.1 * kk p.2.2.2) →
    Measurable w → (∀ l, w l ≠ 0) → (∀ l, w l ≠ ⊤) → μG.IsMulLeftInvariant →
    (∀ φ : G → ENNReal, Measurable φ →
      ∫⁻ g, φ g ∂μG = c * ∫⁻ k, ∫⁻ l, ∫⁻ g₀, ∫⁻ n, φ (n.1 * m l g₀ * kk k) * w l ∂μN ∂ν ∂μL ∂μK) →
    c ≠ 0 → c ≠ ⊤ →
    (∀ l g₀, ∀ γ ∈ Γ, m l (γ * g₀) = ι γ * m l g₀) → (∀ γ ∈ Γ, ι γ ∈ Q) → (∀ q ∈ Q, ∃! γ : Γ, (ι γ)⁻¹ * q ∈ N) →
    (∀ γ ∈ Γ, ∀ f : G → ENNReal, Measurable f → ∫⁻ n, f (n.1 * ι γ) ∂μN = ∫⁻ n, f (ι γ * n.1) ∂μN) →
    μN.IsMulLeftInvariant → IsFundamentalDomain (Q.subgroupOf N) 𝓕 μN → μN 𝓕 ≠ 0 → μN 𝓕 ≠ ⊤ →
    IsFundamentalDomain Γ dom ν → ν.IsMulLeftInvariant →
    ∀ 𝓓 : Set G, IsFundamentalDomain Q 𝓓 μG →
    ∀ φ : G → ENNReal, Measurable φ → (∀ q ∈ Q, ∀ g, φ (q * g) = φ g) → (∀ n ∈ N, ∀ g, φ (n * g) = φ g) →
      ∫⁻ g in 𝓓, φ g ∂μG = c * μN 𝓕 * ∫⁻ k, ∫⁻ l, ∫⁻ g₀ in dom, φ (m l g₀ * kk k) * w l ∂ν ∂μL ∂μK := by
  intro G G₁ L Kt _ _ _ _ _ _ μG ν μL μK N Q Γ μN kk m ι w c dom 𝓕 hQc hΓc hνsf hLsf hLG hLG₁ hRG
    hjoint hw hw0 hwtop hμG hformula hc0 hctop hmι hιQ huniq hconj hμN h𝓕 h𝓕0 h𝓕top hdom hν
    𝓓 h𝓓 φ hφ hφQ hφN
  classical
  haveI := hQc; haveI := hΓc; haveI := hνsf; haveI := hLsf; haveI := hμN; haveI := hν; haveI := hμG
  have hLN : ∀ g : N, Measurable (g * ·) := fun g =>
    ((hLG g.1).comp measurable_subtype_coe).subtype_mk
  haveI hQNc : Countable (Q.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Q.subgroupOf N => (⟨x.1.1, x.2⟩ : Q)) ?_
    intro x y hxy
    have h2 := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h2)
  haveI hNsf : SFinite μN := sFinite_of_fd μN (Q.subgroupOf N) 𝓕 hQNc hLN hμN h𝓕 h𝓕top
  haveI : MeasurableConstSMul Γ G₁ := ⟨fun γ => hLG₁ γ.1⟩
  haveI : SMulInvariantMeasure Γ G₁ ν := ⟨fun γ s hs => by
    show ν ((fun x => (γ : G₁) * x) ⁻¹' s) = ν s
    rw [← Measure.map_apply (hLG₁ γ.1) hs, map_mul_left_eq_self]⟩
  obtain ⟨𝓓₀, hsub, h₀, hae⟩ := h𝓓.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hnull : μG (𝓓 \ 𝓓₀) = 0 := (ae_eq_set.1 hae).2
  let χ : G → ENNReal := fun y => ∑' q : Q, 𝓓₀.indicator (1 : G → ENNReal) ((q : G) * y)
  have hχae : ∀ᵐ y ∂μG, χ y = 1 := GlobalTheory.T.fundamental_domain_indicator_tsum_one μG Q 𝓓 𝓓₀ hQc hLG hμG h𝓓 h₀ hsub hnull
  have hχm : Measurable χ :=
    Measurable.ennreal_tsum fun q => (measurable_one.indicator h₀).comp (hLG q.1)
  let B : Set G := χ ⁻¹' {1}ᶜ
  have hBm : MeasurableSet B := hχm (measurableSet_singleton 1).compl
  have hB0 : μG B = 0 := ae_iff.1 hχae
  have hχB : ∀ y ∉ B, ∑' q : Q, 𝓓₀.indicator (1 : G → ENNReal) (q.1 * y) = 1 := by
    intro y hy
    by_contra hne
    exact hy hne
  have hBint : ∫⁻ k, ∫⁻ l, ∫⁻ g₀, ∫⁻ n, B.indicator φ (n.1 * m l g₀ * kk k) * w l ∂μN ∂ν ∂μL ∂μK
      = 0 := by
    have h1 := hformula (B.indicator φ) (hφ.indicator hBm)
    rw [lintegral_indicator hBm, setLIntegral_measure_zero _ _ hB0] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left hc0
  have hΦm : Measurable (fun p : N × G₁ × L × Kt =>
      B.indicator φ (p.1.1 * m p.2.2.1 p.2.1 * kk p.2.2.2) * w p.2.2.1) :=
    ((hφ.indicator hBm).comp hjoint).mul (hw.comp measurable_snd.snd.fst)
  have hae4 := ae_zero_of_iter μN ν μL μK hNsf hνsf hLsf (fun p : N × G₁ × L × Kt =>
      B.indicator φ (p.1.1 * m p.2.2.1 p.2.1 * kk p.2.2.2) * w p.2.2.1) hΦm hBint
  have key : ∀ k l g₀, ∑' γ : Γ, (∫⁻ n, 𝓓₀.indicator φ (n.1 * m l ((γ : G₁) * g₀) * kk k) * w l ∂μN)
      = (∫⁻ n in 𝓕, χ (n.1 * (m l g₀ * kk k)) ∂μN) * (φ (m l g₀ * kk k) * w l) := by
    intro k l g₀
    have hmeas : Measurable (fun n : N => n.1 * (m l g₀ * kk k)) :=
      (hRG _).comp measurable_subtype_coe
    have e1 : ∀ γ : Γ, (∫⁻ n, 𝓓₀.indicator φ (n.1 * m l ((γ : G₁) * g₀) * kk k) * w l ∂μN)
        = (∫⁻ n, 𝓓₀.indicator (1 : G → ENNReal) (n.1 * ι γ * (m l g₀ * kk k)) ∂μN)
          * (φ (m l g₀ * kk k) * w l) := by
      intro γ
      have hm1 : Measurable (fun n : N =>
          𝓓₀.indicator (1 : G → ENNReal) (n.1 * ι γ * (m l g₀ * kk k))) :=
        ((measurable_one.indicator h₀).comp (hRG _)).comp ((hRG (ι γ)).comp measurable_subtype_coe)
      rw [← lintegral_mul_const _ hm1]
      refine lintegral_congr fun n => ?_
      have hx : n.1 * m l ((γ : G₁) * g₀) * kk k = n.1 * ι γ * (m l g₀ * kk k) := by
        rw [hmι l g₀ γ γ.2]; simp only [mul_assoc]
      have hφx : φ (n.1 * ι γ * (m l g₀ * kk k)) = φ (m l g₀ * kk k) := by
        rw [mul_assoc n.1 (ι γ), hφN n.1 n.2, hφQ (ι γ) (hιQ γ γ.2)]
      rw [hx]
      by_cases hd : n.1 * ι γ * (m l g₀ * kk k) ∈ 𝓓₀
      · simp [Set.indicator_apply, hd, hφx]
      · simp [Set.indicator_apply, hd]
    rw [tsum_congr e1, ENNReal.tsum_mul_right]
    congr 1
    exact GlobalTheory.T.fundamental_domain_unfold_subgroup N Q Γ μN ι 𝓕 𝓓₀ (m l g₀ * kk k) hQc hΓc hLG hmeas h₀ hιQ huniq
      (fun γ hγ => hconj γ hγ (fun x => 𝓓₀.indicator (1 : G → ENNReal) (x * (m l g₀ * kk k)))
        ((measurable_one.indicator h₀).comp (hRG _))) hμN h𝓕
  have unfoldG₁ : ∀ k l, ∫⁻ g₀, ∫⁻ n, 𝓓₀.indicator φ (n.1 * m l g₀ * kk k) * w l ∂μN ∂ν
      = ∫⁻ g₀ in dom, (∫⁻ n in 𝓕, χ (n.1 * (m l g₀ * kk k)) ∂μN)
          * (φ (m l g₀ * kk k) * w l) ∂ν := by
    intro k l
    have hP0 : Measurable (fun p : N × G₁ => 𝓓₀.indicator φ (p.1.1 * m l p.2 * kk k)) :=
      (hφ.indicator h₀).comp
        (hjoint.comp (measurable_fst.prodMk (measurable_snd.prodMk (measurable_const (a := (l, k))))))
    have hP : Measurable (fun p : N × G₁ => 𝓓₀.indicator φ (p.1.1 * m l p.2 * kk k) * w l) :=
      hP0.mul_const (w l)
    have hHm : Measurable (fun g₀ : G₁ => ∫⁻ n, 𝓓₀.indicator φ (n.1 * m l g₀ * kk k) * w l ∂μN) :=
      hP.lintegral_prod_left'
    calc ∫⁻ g₀, ∫⁻ n, 𝓓₀.indicator φ (n.1 * m l g₀ * kk k) * w l ∂μN ∂ν
        = ∑' γ : Γ, ∫⁻ g₀ in dom,
            ∫⁻ n, 𝓓₀.indicator φ (n.1 * m l ((γ : G₁) * g₀) * kk k) * w l ∂μN ∂ν :=
          hdom.lintegral_eq_tsum'' _
      _ = ∫⁻ g₀ in dom, ∑' γ : Γ,
            ∫⁻ n, 𝓓₀.indicator φ (n.1 * m l ((γ : G₁) * g₀) * kk k) * w l ∂μN ∂ν :=
          (lintegral_tsum fun γ : Γ => (hHm.comp (hLG₁ (γ : G₁))).aemeasurable).symm
      _ = _ := lintegral_congr fun g₀ => key k l g₀
  have hLHS : ∫⁻ g in 𝓓, φ g ∂μG
      = c * ∫⁻ k, ∫⁻ l, ∫⁻ g₀, ∫⁻ n, 𝓓₀.indicator φ (n.1 * m l g₀ * kk k) * w l ∂μN ∂ν ∂μL ∂μK := by
    rw [setLIntegral_congr hae.symm, ← lintegral_indicator h₀]
    exact hformula _ (hφ.indicator h₀)
  rw [hLHS, mul_assoc]
  congr 1
  rw [← lintegral_const_mul' _ _ h𝓕top]
  refine lintegral_congr_ae (hae4.mono fun k hk => ?_)
  dsimp only
  rw [← lintegral_const_mul' _ _ h𝓕top]
  refine lintegral_congr_ae (hk.mono fun l hl => ?_)
  dsimp only
  rw [unfoldG₁ k l, ← lintegral_const_mul' _ _ h𝓕top]
  refine lintegral_congr_ae (ae_restrict_of_ae (hl.mono fun g₀ hg => ?_))
  dsimp only
  have hg' : ∫⁻ n, B.indicator φ (n.1 * m l g₀ * kk k) * w l ∂μN = 0 := hg
  have hmB : Measurable (fun n : N => B.indicator (1 : G → ENNReal) (n.1 * (m l g₀ * kk k))) :=
    (measurable_one.indicator hBm).comp ((hRG _).comp measurable_subtype_coe)
  refine setLIntegral_count_mul N Q μN 𝓕 𝓓₀ B (m l g₀ * kk k) (φ (m l g₀ * kk k) * w l)
    ((hRG _).comp measurable_subtype_coe) hBm hχB ?_
  rw [← lintegral_mul_const _ hmB, ← hg']
  refine lintegral_congr fun n => ?_
  have hφx : φ (n.1 * m l g₀ * kk k) = φ (m l g₀ * kk k) := by
    rw [mul_assoc, hφN n.1 n.2]
  rw [← mul_assoc n.1]
  by_cases hb : n.1 * m l g₀ * kk k ∈ B
  · simp [Set.indicator_apply, hb, hφx]
  · simp [Set.indicator_apply, hb]

end GlobalTheory.UnfoldSemidirect
