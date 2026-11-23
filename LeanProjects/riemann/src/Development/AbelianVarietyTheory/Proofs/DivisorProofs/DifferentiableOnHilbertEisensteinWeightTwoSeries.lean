import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardHilbertEisensteinFourierFiberLeNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormLeAbsNormMulDivAbsNormOfEisensteinIndexPaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableExpNegTraceTotallyPositiveFractionalIdeaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqMulExpNegTraceLeStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.QHolo

variable {F : Type} [Field F] [NumberField F]

theorem isOpen_upperHalf : IsOpen (upperHalf F) := by
  have : upperHalf F = ⋂ τ : Emb F, (fun z : Emb F → ℂ => (z τ).im) ⁻¹' Set.Ioi 0 := by
    ext z; simp [upperHalf]
  rw [this]
  exact isOpen_iInter_of_finite fun τ => isOpen_Ioi.preimage (by fun_prop)

theorem qClass_two (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) : qClass 𝔞 𝔟 2 z c =
    ((|(Algebra.norm ℚ c.out.1.1 : ℝ)| / nrm 𝔞 : ℝ) : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * I * ∑ τ, (τ (c.out.1.1 * c.out.1.2) : ℂ) * z τ) := by
  simp [qClass, qTerm, qPow]

theorem differentiable_qClass (𝔞 𝔟 : Frac F) (c : Quotient (qRel 𝔞 𝔟)) :
    Differentiable ℂ (fun z => qClass 𝔞 𝔟 2 z c) := by
  simp only [qClass_two]
  fun_prop

theorem norm_qClass (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) : ‖qClass 𝔞 𝔟 2 z c‖ =
    |(Algebra.norm ℚ c.out.1.1 : ℝ)| / nrm 𝔞 *
      Real.exp (-(2 * Real.pi) * ∑ τ, τ (c.out.1.1 * c.out.1.2) * (z τ).im) := by
  rw [qClass_two, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (abs_nonneg _) (by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _))]
  congr 2
  simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum, Finset.mul_sum]

theorem summable_of_fiber {α β : Type} (g : α → β) (f : α → ℝ) (B : β → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hB : Summable B) (hfib : ∀ (b : β) (s : Finset α), (∀ a ∈ s, g a = b) → ∑ a ∈ s, f a ≤ B b) :
    Summable f := by
  classical
  have hB0 : ∀ b, 0 ≤ B b := fun b => by simpa using hfib b ∅ (by simp)
  refine summable_of_sum_le hf (c := ∑' b, B b) fun u => ?_
  rw [← Finset.sum_fiberwise_of_maps_to (s := u) (t := u.image g) (g := g)
    (fun x hx => Finset.mem_image_of_mem g hx)]
  calc ∑ b ∈ u.image g, ∑ a ∈ u with g a = b, f a ≤ ∑ b ∈ u.image g, B b :=
        Finset.sum_le_sum fun b _ => hfib b _ fun a ha => (Finset.mem_filter.1 ha).2
    _ ≤ ∑' b, B b := hB.sum_le_tsum _ fun b _ => hB0 b

theorem card_fiber_le [IsTotallyReal F] (𝔞 𝔟 : Frac F) (ξ : F) (s : Finset (Quotient (qRel 𝔞 𝔟)))
    (hs : ∀ c ∈ s, c.out.1.1 * c.out.1.2 = ξ) :
    (s.card : ℝ) ≤ |(Algebra.norm ℚ ξ : ℝ)| / (nrm 𝔞 * nrm 𝔟) := GlobalTheory.T.card_hilbertEisensteinFourierFiber_le_norm F 𝔞 𝔟 ξ s hs

theorem abs_norm_le [IsTotallyReal F] (𝔞 𝔟 : Frac F) (p : QPair 𝔞 𝔟) :
    |(Algebra.norm ℚ p.1.1 : ℝ)| ≤ |(Algebra.norm ℚ (p.1.1 * p.1.2) : ℝ)| / nrm 𝔟 := GlobalTheory.T.abs_norm_le_abs_norm_mul_div_absNorm_of_eisensteinIndexPair F 𝔞 𝔟 p

theorem summable_exp_trace [IsTotallyReal F] (L : FractionalIdeal (𝓞 F)⁰ F) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} => Real.exp (-δ * ∑ τ : Emb F, τ x.1)) :=
  GlobalTheory.T.summable_exp_neg_trace_totallyPositive_fractionalIdeal F L δ hδ

theorem norm_sq_exp_le [IsTotallyReal F] {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, ∀ x : F, (∀ τ : Emb F, 0 < τ x) →
    |(Algebra.norm ℚ x : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x) ≤ C * Real.exp (-(δ / 2) * ∑ τ : Emb F, τ x) :=
  GlobalTheory.T.norm_sq_mul_exp_neg_trace_le' F δ hδ

theorem summable_key [IsTotallyReal F] (𝔞 𝔟 : Frac F) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun c : Quotient (qRel 𝔞 𝔟) =>
      |(Algebra.norm ℚ c.out.1.1 : ℝ)| * Real.exp (-δ * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2))) := by
  have hna : 0 ≤ nrm 𝔞 := by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _
  have hnb : 0 ≤ nrm 𝔟 := by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _
  let β := {x : F // x ∈ ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟) ∧ ∀ τ : Emb F, 0 < τ x}
  let g : Quotient (qRel 𝔞 𝔟) → β := fun c =>
    ⟨c.out.1.1 * c.out.1.2, FractionalIdeal.mul_mem_mul c.out.2.1 c.out.2.2.1, c.out.2.2.2⟩
  let B : β → ℝ := fun x => |(Algebra.norm ℚ x.1 : ℝ)| / (nrm 𝔞 * nrm 𝔟) *
    (|(Algebra.norm ℚ x.1 : ℝ)| / nrm 𝔟 * Real.exp (-δ * ∑ τ : Emb F, τ x.1))
  obtain ⟨C, hC⟩ := norm_sq_exp_le (F := F) hδ
  have hB : Summable B := by
    refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_)
      ((summable_exp_trace (F := F) ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟) (half_pos hδ)).mul_left
        ((nrm 𝔞 * nrm 𝔟 * nrm 𝔟)⁻¹ * C))
    have h := hC x.1 x.2.2
    have : B x = (nrm 𝔞 * nrm 𝔟 * nrm 𝔟)⁻¹ *
        (|(Algebra.norm ℚ x.1 : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x.1)) := by
      simp only [B]; field_simp
    rw [this]
    have h2 := mul_le_mul_of_nonneg_left h (show 0 ≤ (nrm 𝔞 * nrm 𝔟 * nrm 𝔟)⁻¹ by positivity)
    linarith
  refine summable_of_fiber g _ B (fun c => by positivity) hB fun b s hs => ?_
  have hξ : ∀ c ∈ s, c.out.1.1 * c.out.1.2 = b.1 := fun c hc => by rw [← hs c hc]
  calc ∑ c ∈ s, |(Algebra.norm ℚ c.out.1.1 : ℝ)| * Real.exp (-δ * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2))
      ≤ ∑ c ∈ s, |(Algebra.norm ℚ b.1 : ℝ)| / nrm 𝔟 * Real.exp (-δ * ∑ τ : Emb F, τ b.1) := by
        refine Finset.sum_le_sum fun c hc => ?_
        rw [← hξ c hc]
        exact mul_le_mul_of_nonneg_right (abs_norm_le 𝔞 𝔟 c.out) (Real.exp_pos _).le
    _ = (s.card : ℝ) * (|(Algebra.norm ℚ b.1 : ℝ)| / nrm 𝔟 * Real.exp (-δ * ∑ τ : Emb F, τ b.1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ B b := mul_le_mul_of_nonneg_right (card_fiber_le 𝔞 𝔟 b.1 s hξ) (by positivity)

theorem exists_im_bound {y : Emb F → ℂ} (hy : y ∈ upperHalf F) :
    ∃ ε > 0, ∀ v ∈ Metric.ball y ε, ∀ τ, ε ≤ (v τ).im := by
  obtain ⟨ε, hε, hle⟩ : ∃ ε > 0, ∀ τ, 2 * ε ≤ (y τ).im := by
    rcases isEmpty_or_nonempty (Emb F) with h | h
    · exact ⟨1, one_pos, fun τ => isEmptyElim τ⟩
    · obtain ⟨τ₀, hτ₀⟩ := Finite.exists_min (fun τ => (y τ).im)
      exact ⟨(y τ₀).im / 2, half_pos (hy τ₀), fun τ => by linarith [hτ₀ τ]⟩
  refine ⟨ε, hε, fun v hv τ => ?_⟩
  have h1 : dist (v τ) (y τ) < ε := (dist_le_pi_dist v y τ).trans_lt (Metric.mem_ball.1 hv)
  have h2 : |(v τ).im - (y τ).im| < ε := by
    rw [Complex.dist_eq] at h1
    exact (by simpa using Complex.abs_im_le_norm (v τ - y τ) : |(v τ).im - (y τ).im| ≤ ‖v τ - y τ‖).trans_lt h1
  linarith [hle τ, (abs_lt.1 h2).1]

theorem qholo : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    DifferentiableOn ℂ (fun z => ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z c) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  intro F _ _ _ 𝔞 𝔟
  refine ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.differentiableOn_tsum_loc isOpen_upperHalf
    (fun c z => qClass 𝔞 𝔟 2 z c) (fun c => (differentiable_qClass 𝔞 𝔟 c).differentiableOn) ?_
  intro y hy
  obtain ⟨ε, hε, hv⟩ := exists_im_bound hy
  refine ⟨ε, hε, fun c => (nrm 𝔞)⁻¹ * (|(Algebra.norm ℚ c.out.1.1 : ℝ)| *
      Real.exp (-(2 * Real.pi * ε) * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2))),
    (summable_key 𝔞 𝔟 (by positivity)).mul_left _, fun c v hvb => ?_⟩
  rw [norm_qClass, div_eq_inv_mul, mul_assoc]
  have hn : 0 ≤ (nrm 𝔞)⁻¹ := inv_nonneg.2 (by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _)
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) hn
  refine Real.exp_le_exp.2 ?_
  have hpos := c.out.2.2.2
  have : ε * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2) ≤ ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2) * (v τ).im := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ _ => by nlinarith [hpos τ, hv v hvb τ]
  have hπ := Real.pi_pos
  nlinarith

end GlobalTheory.QHolo
