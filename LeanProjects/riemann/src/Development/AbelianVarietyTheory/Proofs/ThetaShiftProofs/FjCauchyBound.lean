import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HolomorphicPeriodicityExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMajorantFlags
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FjFlow

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.FjCauchy

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

open NumberField Complex Filter Topology in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in

theorem _root_.GlobalTheory.FjCauchy.isIsoV_embV {ξ : Fin r → E} (hξ : X.IsIso ξ) :
    X.IsIsoV (X.embV ξ) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsIsoV
  intro τ
  refine ⟨?_, _root_.ReciprocityTheory.ChartRestriction.G.FD.emb_ne_zero (τ : E →+* ℂ) hξ.2.2⟩
  show _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (τ : E →+* ℂ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ ξ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ ξ) = 0
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_emb, hξ.2.1, map_zero]

open NumberField Complex Filter Topology in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in

theorem _root_.GlobalTheory.FjCauchy.tt_pos {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) (τ : X.Ψ) :
    0 < X.tt ξ x τ := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.tt
  exact one_div_pos.2 (mul_pos (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ) (X.maj_pos hx τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.emb_ne_zero (τ : E →+* ℂ) hξ.2.2)))

open NumberField Complex Filter Topology in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
private theorem one_add_two_mul_pos_of_le {c y h hp : ℝ} (hc : 0 < c) (h0 : 0 ≤ h) (hle : h ≤ hp)
    (hpos : 0 < 1 + 2 * c * y * hp) : 0 < 1 + 2 * c * y * h := by
  rcases le_or_gt 0 y with hy | hy
  · have : 0 ≤ 2 * c * y * h := by positivity
    linarith
  · have h1 : 0 ≤ hp - h := sub_nonneg.2 hle
    have h2 : 0 < -y := by linarith
    have : 0 ≤ 2 * c * (-y) * (hp - h) := by positivity
    nlinarith

open NumberField Complex Filter Topology in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
private theorem one_add_two_mul_pos_of_inv_add_pos {c y hp : ℝ} (hc : 0 < c) (hp0 : 0 < hp)
    (hs : 0 < 1 / (c * (2 * hp)) + y) : 0 < 1 + 2 * c * y * hp := by
  have hk : 0 < c * (2 * hp) := by positivity
  have e : (1 / (c * (2 * hp)) + y) * (c * (2 * hp)) = 1 + 2 * c * y * hp := by
    rw [add_mul, one_div, inv_mul_cancel₀ hk.ne']
    ring
  rw [← e]
  exact mul_pos hs hk

open NumberField Complex Filter Topology in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in

theorem _root_.GlobalTheory.FjCauchy.flow_mem_dom {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hs : ∀ τ, 0 < X.tt ξ x τ + (s τ).im) :
    X.flow ξ s x ∈ X.dom := by
  have hiso := _root_.GlobalTheory.FjCauchy.isIsoV_embV X hξ
  rw [show X.flow ξ s x = X.flowV (X.embV ξ) s x from rfl]
  have hx' := hx
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG at hx' ⊢
  intro τ
  obtain ⟨hdet, hmin⟩ := hx' τ
  constructor
  · show (X.flowMatV (X.embV ξ τ) τ (s τ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0
    rw [Matrix.det_mul, _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.det_flowMat X _ τ _ (hiso τ).1, one_mul]
    exact hdet
  · intro i
    have hm0 := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.maj_eq X hx (X.embV ξ) τ (hiso τ).1
    have hmaj := X.maj_pos hx τ (hiso τ).2
    have hsτ := hs τ
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.tt at hsτ
    change 0 < 1 / (X.c τ * X.maj x τ (X.embV ξ τ)) + (s τ).im at hsτ
    have hb := _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN_bounds (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hG_of X τ) X.p0 X.p0_le (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) hdet (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hsg_of X hx τ)
      (X.embV ξ τ) (hiso τ).1 i (Nat.lt_succ_iff.mp i.isLt)
    have hmi := hmin i
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_eq] at hmi ⊢
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_flow X hx _ τ (hiso τ).1 s, Complex.re_mul_ofReal, ← mul_assoc]
    rw [hm0] at hmaj hsτ
    have hc := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ
    have hp0 : 0 < _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (τ : E →+* ℂ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (X.embV ξ τ) X.p0 := by linarith
    exact mul_pos hmi (one_add_two_mul_pos_of_le hc hb.1 hb.2 (one_add_two_mul_pos_of_inv_add_pos hc hp0 hsτ))

open NumberField Complex Filter Topology in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in

theorem _root_.GlobalTheory.FjCauchy.tt_flow {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hs : X.flow ξ s x ∈ X.dom) (τ : X.Ψ) :
    X.tt ξ (X.flow ξ s x) τ = X.tt ξ x τ + (s τ).im := by
  have hiso := _root_.GlobalTheory.FjCauchy.isIsoV_embV X hξ
  rw [show X.flow ξ s x = X.flowV (X.embV ξ) s x from rfl] at hs ⊢
  have hf : 1 + 2 * X.c τ * (s τ).im *
      _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (τ : E →+* ℂ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (X.embV ξ τ) X.p0 ≠ 0 := by
    intro h0
    have h1 := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hsg_of X hs τ X.p0 X.p0_le
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_flow X hx _ τ (hiso τ).1 s, h0] at h1
    simp at h1
  have hm := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.maj_flow X hx (X.embV ξ) τ (hiso τ).1 s hf
  have hm0 := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.maj_eq X hx (X.embV ξ) τ (hiso τ).1
  have hmaj := X.maj_pos hx τ (hiso τ).2
  have hc := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.tt
  change 1 / (X.c τ * X.maj (X.flowV (X.embV ξ) s x) τ (X.embV ξ τ)) =
    1 / (X.c τ * X.maj x τ (X.embV ξ τ)) + (s τ).im
  rw [hm, hm0]
  rw [hm0] at hmaj
  generalize _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (τ : E →+* ℂ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (X.embV ξ τ) X.p0 = H at hf hmaj ⊢
  have hH : H ≠ 0 := by linarith
  have hc' : X.c τ ≠ 0 := hc.ne'
  field_simp

open NumberField Complex Filter Topology in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
private theorem differentiable_flow_affine_line (ξ : Fin r → E) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (a b : X.Ψ → ℂ) :
    Differentiable ℂ (fun t : ℂ ↦ X.flow ξ (fun τ ↦ a τ + t * b τ) x) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.flow _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.flowMat _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
  refine differentiable_pi.2 fun τ ↦ ?_
  refine differentiable_pi.2 fun i ↦ ?_
  refine differentiable_pi.2 fun j ↦ ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

open NumberField Complex Filter Topology in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in

theorem _root_.GlobalTheory.FjCauchy.fj_flow {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hP : X.IsBddSec la P) {ξ : Fin r → E}
    (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ)
    (hs : X.flow ξ s x ∈ X.dom) :
    X.fj la ξ ν P (X.flow ξ s x) =
      cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ) * X.fj la ξ ν P x := by
  have hP' : X.IsSec la P ∧ ∃ C, ∀ y ∈ X.dom, X.pnorm la P y ≤ C := hP
  obtain ⟨hsec, hbdd⟩ := hP'
  have hGξ := hξ.2.1
  obtain ⟨W, hWdef⟩ : ∃ W : Set ℂ,
      W = {t | X.flow ξ (fun τ ↦ ((s τ).re : ℂ) + t * (s τ).im) x ∈ X.dom} := ⟨_, rfl⟩
  have hW : W = (fun t : ℂ ↦ fun τ : X.Ψ ↦ t.im * (s τ).im) ⁻¹' _root_.ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.admissibleImaginary X ξ x := by
    ext t
    rw [hWdef, Set.mem_setOf_eq, Set.mem_preimage, _root_.ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.flow_mem_dom_iff X hGξ x hx]
    have him : (fun τ ↦ (((s τ).re : ℂ) + t * (s τ).im).im) = fun τ ↦ t.im * (s τ).im := by
      funext τ
      simp
    rw [him]
  have hlin : IsLinearMap ℝ (fun t : ℂ ↦ fun τ : X.Ψ ↦ t.im * (s τ).im) :=
    ⟨fun u v ↦ by funext τ; simp [add_mul], fun c u ↦ by funext τ; simp [mul_assoc]⟩
  have hcont : Continuous (fun t : ℂ ↦ fun τ : X.Ψ ↦ t.im * (s τ).im) := by fun_prop
  obtain ⟨hopen, hconv⟩ := _root_.ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.admissibleImaginary_open_convex X (ξ := ξ) x hx
  have hWo : IsOpen W := hW ▸ hopen.preimage hcont
  have hWc : IsPreconnected W := hW ▸ (hconv.is_linear_preimage hlin).isPreconnected
  have hreal : ∀ a : ℝ, (fun τ ↦ ((s τ).re : ℂ) + (a : ℂ) * (s τ).im) =
      fun τ ↦ (((s τ).re + a * (s τ).im : ℝ) : ℂ) := by
    intro a
    funext τ
    push_cast
    ring
  have h0W : (0 : ℂ) ∈ W := by
    rw [hWdef, Set.mem_setOf_eq, show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, hreal]
    exact (_root_.ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.flow_real X hξ hx _ la).1
  have hline : ∀ τ, ((s τ).re : ℂ) + I * (s τ).im = s τ := by
    intro τ
    rw [mul_comm]
    exact Complex.re_add_im (s τ)
  have hIW : I ∈ W := by
    rw [hWdef, Set.mem_setOf_eq]
    simp only [hline]
    exact hs
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = fun t ↦
      X.fj la ξ ν P (X.flow ξ (fun τ ↦ ((s τ).re : ℂ) + t * (s τ).im) x) -
        cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * (((s τ).re : ℂ) + t * (s τ).im)) *
          X.fj la ξ ν P x := ⟨_, rfl⟩
  have hgd : DifferentiableOn ℂ g W := by
    rw [hg]
    apply DifferentiableOn.sub
    · refine (_root_.ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.fj_diffOn X la P hP hξ ν).comp
        (differentiable_flow_affine_line X ξ x _ _).differentiableOn ?_
      intro t ht
      rw [hWdef] at ht
      exact ht
    · apply DifferentiableOn.mul_const
      apply Differentiable.differentiableOn
      fun_prop
  have hg0 : ∀ a : ℝ, g a = 0 := by
    intro a
    have h := _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.fj_flow_real X la ξ hξ ν P hsec hbdd x hx
      (fun τ ↦ (s τ).re + a * (s τ).im)
    push_cast at h
    rw [hg]
    simp only
    rw [h, sub_self]
  have hto : Tendsto (fun a : ℝ ↦ (a : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with a ha
      simpa using ha
  have hfreq : ∃ᶠ t in 𝓝[≠] (0 : ℂ), g t = 0 := hto.frequently (Frequently.of_forall hg0)
  have hgI := (hgd.analyticOnNhd hWo).eqOn_zero_of_preconnected_of_frequently_eq_zero
    hWc h0W hfreq hIW
  rw [hg] at hgI
  simp only [hline, Pi.zero_apply, sub_eq_zero] at hgI
  exact hgI

end GlobalTheory.FjCauchy

namespace GlobalTheory

end GlobalTheory
