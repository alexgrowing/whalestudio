import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.SmoothSeries
import Lemmata.GeneralBFactVersion.Imports

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem lactDom (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := (PairUnfoldPf.lact_mem_dom_iff X hγ x).2 hx

theorem rmulDom (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    rmul x b ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom X hx hb

theorem isOpenDom (X : Data E r) : IsOpen X.dom := FourierCoefficientDomain.isOpen_dom X

theorem lact_mul' {Ψ : Finset (E →+* ℂ)} (γ γ' : GL (Fin r) E) (x : Frame Ψ r) :
    lact (γ * γ') x = lact γ (lact γ' x) := by
  funext τ
  simp only [lact, mat, Units.val_mul, Matrix.map_mul]
  rw [Matrix.mul_assoc]
  rfl

theorem lact_rmul' {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x b : Frame Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm

theorem norm_chi (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ‖X.χ la γ‖ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  have h1 := congrArg norm (h γ hγ)
  rw [norm_pow, norm_one] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1

theorem chi_ne (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    X.χ la γ ≠ 0 := by
  intro h
  have := norm_chi X la hγ
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem poin_mul (X : Data E r) (la la' : Wt X.Ψ r) (P g : Frame X.Ψ r → ℂ) (hg : X.IsSec la' g)
    (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    poin X (la + la') (fun y => g y * P y) x = g x * poin X la P x := by
  unfold poin
  rw [← tsum_mul_left]
  congr 1
  funext γ
  dsimp only
  rw [X.χ_add la la' γ.1 γ.2, hg.2.2 γ.1 γ.2 x hx]
  have h1 := chi_ne X la' γ.2
  have h2 := chi_ne X la γ.2
  field_simp

theorem poin_rmul (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hP : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    poin X la P (rmul x b) = bchar la b * poin X la P x := by
  unfold poin
  rw [← tsum_mul_left]
  congr 1
  funext γ
  rw [lact_rmul', hP _ (lactDom X γ.2 hx) b hb]
  ring

theorem poin_lact (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {γ' : GL (Fin r) E}
    (hγ' : γ' ∈ X.Γ) (x : Frame X.Ψ r) :
    poin X la P (lact γ' x) = X.χ la γ' * poin X la P x := by
  unfold poin
  set g : X.Γ := ⟨γ', hγ'⟩
  have key : ∀ γ : X.Γ, (X.χ la γ.1)⁻¹ * P (lact γ.1 (lact γ' x)) =
      X.χ la γ' * ((X.χ la (γ * g).1)⁻¹ * P (lact (γ * g).1 x)) := by
    intro γ
    have hm : ((γ * g : X.Γ) : GL (Fin r) E) = γ.1 * γ' := rfl
    rw [hm, lact_mul', X.χ_mul la γ.1 γ.2 γ' hγ']
    have h1 := chi_ne X la hγ'
    have h2 := chi_ne X la γ.2
    field_simp
  rw [tsum_congr key, tsum_mul_left]
  congr 1
  exact (Equiv.mulRight g).tsum_eq (fun δ : X.Γ => (X.χ la δ.1)⁻¹ * P (lact δ.1 x))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open Metric

theorem fderiv_bound_ball {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {g : Y → ℂ} {y : Y}
    {R M : ℝ} (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball y (2 * R)))
    (hM : ∀ v ∈ ball y (2 * R), ‖g v‖ ≤ M) : ‖fderiv ℂ g y‖ ≤ M / R := by
  first | exact Bl.general_b_fact_version.goal1 .. | (apply Bl.general_b_fact_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_version.goal1 <;> assumption)

theorem differentiableOn_tsum_loc {ι Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {U : Set Y}
    (hU : IsOpen U) (f : ι → Y → ℂ) (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hb : ∀ y ∈ U, ∃ ε > 0, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ v ∈ ball y ε, ‖f i v‖ ≤ u i) :
    DifferentiableOn ℂ (fun y => ∑' i, f i y) U := by
  intro y0 hy0
  obtain ⟨ε, hε, u, hu, hub⟩ := hb y0 hy0
  obtain ⟨δ, hδ, hδU⟩ := isOpen_iff.1 hU y0 hy0
  set m := min ε δ with hm
  have hm0 : 0 < m := lt_min hε hδ
  set R := m / 4 with hR
  have hR0 : 0 < R := by positivity
  have hsub : ∀ y ∈ ball y0 R, ball y (2 * R) ⊆ ball y0 m := by
    intro y hy v hv
    rw [mem_ball] at *
    calc dist v y0 ≤ dist v y + dist y y0 := dist_triangle _ _ _
      _ < 2 * R + R := add_lt_add hv hy
      _ ≤ m := by rw [hR]; linarith
  have hε' : ball y0 m ⊆ ball y0 ε := ball_subset_ball (min_le_left _ _)
  have hδ' : ball y0 m ⊆ U := (ball_subset_ball (min_le_right _ _)).trans hδU
  have hin : ∀ y ∈ ball y0 R, y ∈ U := fun y hy => hδ' (hsub y hy (mem_ball_self (by linarith)))
  have hder : ∀ i, ∀ y ∈ ball y0 R, HasFDerivAt (f i) (fderiv ℂ (f i) y) y := fun i y hy =>
    ((hf i y (hin y hy)).differentiableAt (hU.mem_nhds (hin y hy))).hasFDerivAt
  have hbd : ∀ i, ∀ y ∈ ball y0 R, ‖fderiv ℂ (f i) y‖ ≤ u i / R := fun i y hy =>
    fderiv_bound_ball hR0 ((hf i).mono ((hsub y hy).trans hδ')) (fun v hv => hub i v (hε' (hsub y hy hv)))
  have hs := hasFDerivAt_tsum_of_isPreconnected (hu.div_const R) isOpen_ball
    (convex_ball y0 R).isPreconnected hder hbd (mem_ball_self hR0)
    (Summable.of_norm_bounded hu fun i => hub i y0 (mem_ball_self hε)) (mem_ball_self hR0)
  exact hs.differentiableAt.differentiableWithinAt

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
