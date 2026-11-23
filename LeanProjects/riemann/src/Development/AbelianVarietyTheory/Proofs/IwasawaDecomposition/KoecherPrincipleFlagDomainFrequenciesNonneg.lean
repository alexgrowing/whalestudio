import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bNormHolds

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom Filter Topology

namespace GlobalTheory.Koecher

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

open MajorantConjugateTransfer TwoSidedBoostBounds MinimumGrowthBounds FractionalSliceDomains in

theorem fj_le_slice (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) (ξ : Fin r → E) (hξ : X.IsIso ξ)
    (ν : X.Ψ → ℝ) (x : Frame X.Ψ r) (hx : x ∈ X.dom) (y : X.Ψ → ℝ) (M : ℝ)
    (hy : ∀ τ, 0 < X.tt ξ x τ + y τ)
    (hM : ∀ u : X.Ψ → ℝ, ‖P (X.flow ξ (fun τ => (u τ : ℂ) + (y τ : ℂ) * Complex.I) x)‖ ≤ M) :
    ‖X.fj la ξ ν P x‖ * Real.exp (-4 * Real.pi * ∑ τ, ν τ * y τ) ≤ M := by
  classical
  obtain ⟨bs, hω⟩ := FlowMeanContinuity.exists_basis X la
  have hωp : ∀ j, bs j ∈ X.periods la := by
    intro j
    have : bs j ∈ Submodule.span ℤ (Set.range bs) := Submodule.subset_span ⟨j, rfl⟩
    rw [hω] at this
    exact this
  have hrepr : ∀ (v : X.Ψ → ℝ) τ, ∑ j, bs.repr v j * bs j τ = v τ := by
    intro v τ
    conv_rhs => rw [← bs.sum_repr v]
    simp [Finset.sum_apply, mul_comm]
  by_cases hf : ∀ j, ∃ k : ℤ, 2 * ∑ τ, ν τ * bs j τ = k
  swap
  · have h0 : X.fj la ξ ν P x = 0 := by
      unfold Data.fj
      rw [if_neg]
      intro hall
      exact hf fun j => hall _ (hωp j)
    rw [h0, norm_zero, zero_mul]
    exact (norm_nonneg _).trans (hM 0)
  choose k hk using hf
  rw [FlowMeanContinuity.fj_eq_fourCoeff X la P hP hξ hx bs hω ν k hk]
  change ‖ReciprocityTheory.L2DbarEstimates.Y.fourCoeff (hfun X P ξ x bs) 0 k‖ * _ ≤ _
  have hm : ∀ τ, 0 < X.maj x τ (Data.emb τ.1 ξ) :=
    fun τ => X.maj_pos hx τ (emb_ne_zero τ.1 hξ.2.2)
  have hc := c_pos X
  set b' : Fin (Fintype.card X.Ψ) → ℝ := fun j => bs.repr y j with hb'
  have hb'ω : ∀ τ, ∑ j, b' j * bs j τ = y τ := hrepr y
  have hb'Ω : b' ∈ FractionalSliceDomains.Om X ξ x bs := by
    show (fun τ => ∑ j, b' j * bs j τ) ∈ AdmissibleHermitianColumns.admissibleImaginary X ξ x
    rw [mem_admissibleImaginary_iff X hx hξ]
    intro τ
    rw [hb'ω]
    have h1 := mul_pos (hc τ) (hm τ)
    have h2 := mul_pos (hy τ) h1
    have e : (X.tt ξ x τ + y τ) * (X.c τ * X.maj x τ (Data.emb τ.1 ξ)) =
        1 + X.c τ * y τ * X.maj x τ (Data.emb τ.1 ξ) := by
      rw [Data.tt, add_mul, one_div_mul_cancel h1.ne']
      ring
    rwa [e] at h2
  have hind := ReciprocityTheory.L2DbarEstimates.Y.four_indep (Fintype.card X.Ψ) (FractionalSliceDomains.Om X ξ x bs) (hfun X P ξ x bs)
    (Om_open_conn X bs hx).1 (Om_open_conn X bs hx).2 (hfun_diff X bs P la hP hx hξ)
    (hfun_periodic X bs P la hP hx hξ hω) 0 (zero_mem_Om X bs hx hξ) b' hb'Ω k
  rw [hind]
  have hslice : ∀ t : Fin (Fintype.card X.Ψ) → ℝ,
      ‖hfun X P ξ x bs (fun k => (t k : ℂ) + (b' k : ℂ) * Complex.I)‖ ≤ M := by
    intro t
    have h := hM (fun τ => ∑ j, t j * bs j τ)
    unfold hfun
    convert h using 4
    funext τ
    rw [← hb'ω τ]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hbd := ReciprocityTheory.L2DbarEstimates.Y.four_bound (Fintype.card X.Ψ) (hfun X P ξ x bs) b' k _ hslice
  have hsum : ∑ j, (k j : ℝ) * b' j = 2 * ∑ τ, ν τ * ∑ j, b' j * bs j τ := by
    simp only [← hk, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum] at hbd
  simp only [hb'ω] at hbd
  convert hbd using 3
  ring

theorem exists_ne (h : 1 < Module.finrank ℚ E / 2) (τ₀ : X.Ψ) : ∃ τ₁ : X.Ψ, τ₁ ≠ τ₀ := by
  classical
  by_contra hne
  push Not at hne
  have hsub : (Finset.univ : Finset (E →+* ℂ)) ⊆ {τ₀.1, ComplexEmbedding.conjugate τ₀.1} := by
    intro τ _
    by_cases hτ : τ ∈ X.Ψ
    · have := congrArg Subtype.val (hne ⟨τ, hτ⟩)
      simp only at this
      simp [this]
    · have h2 : ComplexEmbedding.conjugate τ ∈ X.Ψ := by
        by_contra h3
        exact hτ ((X.cmType τ).mpr h3)
      have := congrArg Subtype.val (hne ⟨_, h2⟩)
      simp only at this
      have h4 : τ = ComplexEmbedding.conjugate τ₀.1 := by
        rw [← this]
        exact (star_star τ).symm
      simp [h4]
  have h1 := (Finset.card_le_card hsub).trans Finset.card_le_two
  rw [Finset.card_univ, NumberField.Embeddings.card] at h1
  omega

theorem eq_zero_of_exp_le {a b c K A : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (h : ∀ L : ℝ, 1 ≤ L → a * Real.exp (b * L - c) ≤ K * L ^ A) : a = 0 := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero A b hb).const_mul (K * Real.exp c)
  rw [mul_zero] at ht
  refine le_antisymm (ge_of_tendsto ht ?_) ha
  filter_upwards [eventually_ge_atTop 1] with L hL
  have h1 := mul_le_mul_of_nonneg_right (h L hL) (Real.exp_pos (c - b * L)).le
  rw [mul_assoc, ← Real.exp_add] at h1
  simp only [sub_add_sub_cancel', sub_self, Real.exp_zero, mul_one] at h1
  refine h1.trans (le_of_eq ?_)
  rw [sub_eq_add_neg, Real.exp_add, neg_mul]
  ring

end GlobalTheory.Koecher

namespace GlobalTheory

open Koecher FjCauchy in

theorem freqNonneg_of_thickBdd : OrbitThickSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), 1 < Module.finrank ℚ E / 2 → X.IsSec la P →
    ThickBdd X (X.pnorm la P) → FreqNonneg X la P := by
  intro hO E _ _ _ r X la P hE hP hT ξ hξ ν x hx hne τ₀
  classical
  by_contra hneg
  push Not at hneg
  obtain ⟨τ₁, h10⟩ := exists_ne X hE τ₀
  obtain ⟨ε, hε, hth⟩ := hO E r X ξ hξ x hx
  obtain ⟨S, hS⟩ := hT ε hε
  have ht := tt_pos X hξ hx
  have hn := FlowCoefficientBounds.nfac_pos X hx la
  apply hne
  rw [← norm_eq_zero]
  refine eq_zero_of_exp_le (b := 4 * Real.pi * (-ν τ₀ * X.tt ξ x τ₀))
    (c := 4 * Real.pi * (-ν τ₀ * X.tt ξ x τ₀ + |ν τ₁| * X.tt ξ x τ₁)) (K := |S| / X.nfac la x)
    (A := ∑ τ, |X.spread la τ / 2|) (norm_nonneg _)
    (mul_pos (by positivity) (mul_pos (by linarith) (ht _))) fun L hL => ?_
  have hL0 : 0 < L := by linarith
  have hLi : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
  let q : X.Ψ → ℝ := fun τ => (if τ = τ₀ then L else 1) * (if τ = τ₁ then L⁻¹ else 1)
  have hq0 : ∀ τ, 0 < q τ := fun τ => by
    simp only [q]
    split_ifs <;> positivity
  have hqm : ∀ τ, max (q τ) (q τ)⁻¹ ≤ L := fun τ => by
    simp only [q]
    split_ifs with h1 h2 h2
    · exact absurd (h2.symm.trans h1) h10
    · simp [hLi.trans hL]
    · simp [hLi.trans hL]
    · simp [hL]
  have hq1 : ∀ τ, 1 ≤ max (q τ) (q τ)⁻¹ := fun τ => by
    rcases le_total 1 (q τ) with h | h
    · exact le_max_of_le_left h
    · exact le_max_of_le_right ((one_le_inv₀ (hq0 τ)).mpr h)
  have hqp : ∏ τ, q τ = 1 := by
    simp only [q, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    exact mul_inv_cancel₀ hL0.ne'
  let y : X.Ψ → ℝ := fun τ => (q τ - 1) * X.tt ξ x τ
  have hty : ∀ τ, X.tt ξ x τ + y τ = q τ * X.tt ξ x τ := fun τ => by simp only [y]; ring
  have hy : ∀ τ, 0 < X.tt ξ x τ + y τ := fun τ => by rw [hty]; exact mul_pos (hq0 τ) (ht τ)
  refine le_trans ?_ (fj_le_slice X la P hP ξ hξ ν x hx y _ hy fun u => ?_)
  · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have e : ∑ τ, ν τ * y τ = ν τ₀ * ((L - 1) * X.tt ξ x τ₀) + ν τ₁ * ((L⁻¹ - 1) * X.tt ξ x τ₁) := by
      rw [Fintype.sum_eq_add τ₀ τ₁ h10.symm]
      · simp [y, q, h10, h10.symm]
      · rintro τ ⟨h1, h2⟩
        simp [y, q, h1, h2]
    rw [e]
    have h1 : ν τ₁ * ((L⁻¹ - 1) * X.tt ξ x τ₁) ≤ |ν τ₁| * X.tt ξ x τ₁ := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos (ht τ₁)]
      refine mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (ht τ₁).le ?_) (abs_nonneg _)
      have := inv_pos.mpr hL0
      rw [abs_le]
      constructor <;> linarith
    nlinarith [Real.pi_pos]
  · set s : X.Ψ → ℂ := fun τ => (u τ : ℂ) + (y τ : ℂ) * I with hs
    have him : ∀ τ, (s τ).im = y τ := fun τ => by simp [hs]
    have hd : X.flow ξ s x ∈ X.dom := flow_mem_dom X hξ hx s fun τ => by rw [him]; exact hy τ
    have hprod : ∏ τ, X.tt ξ (X.flow ξ s x) τ = ∏ τ, X.tt ξ x τ := by
      simp only [tt_flow X hξ hx s hd, him, hty]
      rw [Finset.prod_mul_distrib, hqp, one_mul]
    have hb : ‖P (X.flow ξ s x)‖ * X.nfac la (X.flow ξ s x) ≤ S := hS _ hd (hth s hd hprod)
    have hn' := FlowCoefficientBounds.nfac_pos X hd la
    have hN : X.nfac la x / X.nfac la (X.flow ξ s x) ≤
        ∏ τ, max (1 + (s τ).im / X.tt ξ x τ) (1 + (s τ).im / X.tt ξ x τ)⁻¹ ^ (X.spread la τ / 2) :=
      (m3bNorm_holds r X _ (isIsoV_embV X hξ) la x hx s hd).2
    have hqe : ∀ τ, 1 + (s τ).im / X.tt ξ x τ = q τ := fun τ => by
      rw [him]
      simp only [y]
      rw [mul_div_cancel_right₀ _ (ht τ).ne']
      ring
    simp only [hqe] at hN
    have hN2 : ∏ τ, max (q τ) (q τ)⁻¹ ^ (X.spread la τ / 2) ≤ L ^ ∑ τ, |X.spread la τ / 2| := by
      rw [Real.rpow_sum_of_pos hL0]
      refine Finset.prod_le_prod (fun τ _ => Real.rpow_nonneg (zero_le_one.trans (hq1 τ)) _) fun τ _ => ?_
      exact (Real.rpow_le_rpow_of_exponent_le (hq1 τ) (le_abs_self _)).trans
        (Real.rpow_le_rpow (zero_le_one.trans (hq1 τ)) (hqm τ) (abs_nonneg _))
    calc ‖P (X.flow ξ s x)‖ ≤ |S| / X.nfac la (X.flow ξ s x) := by
          rw [le_div_iff₀ hn']
          exact hb.trans (le_abs_self S)
      _ = |S| / X.nfac la x * (X.nfac la x / X.nfac la (X.flow ξ s x)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hN.trans hN2) (by positivity)

end GlobalTheory
