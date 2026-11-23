import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureDetOneFactorNearIdentityLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolLow.OneMeasure

open Filter Topology

section Density

open scoped Matrix.Norms.Operator

theorem tendsto_of_density {p q : ℕ} (m : Measure (UpqT p q)) (hH : m.IsHaarMeasure) (lam : Measure (lieU p q))
    (hlam : lam.IsAddHaarMeasure) (c : ℝ≥0∞)
    (ht : Tendsto (fun r : ℝ => m {g | ∃ X ∈ ballU p q r, UpqT.mat g =
      NormedSpace.exp (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)} / lam (ballU p q r)) (𝓝[>] 0) (𝓝 c))
    (S : ℝ → Set (lieU p q)) (hm : ∀ r, MeasurableSet (S r))
    (hS : ∀ δ > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), S r ⊆ ballU p q δ)
    (h0 : ∀ᶠ r in 𝓝[>] (0 : ℝ), lam (S r) ≠ 0) :
    Tendsto (fun r : ℝ => m {g | ∃ X ∈ S r, UpqT.mat g =
      NormedSpace.exp (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)} / lam (S r)) (𝓝[>] 0) (𝓝 c) := by
  obtain ⟨c', -, -, h⟩ := (Examples₂.CD.chart p q).exists_density' (Examples₂.CD.finDimLie p q) _ (Examples₂.CD.instBorelLie p q) _
    (Examples₂.CD.instBorelU p q) (Examples₂.CD.instTopGroupU p q) m hH lam hlam
  have h1 := h (ballU p q) (fun r => (Examples₂.CD.isOpen_ballU p q r).measurableSet)
    (fun δ hδ => by
      filter_upwards [Ioo_mem_nhdsGT hδ] with r hr X hX
      exact lt_of_le_of_lt (Examples₂.CD.norm_le_sum p q X) (lt_trans hX hr.2))
    (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact ⟨(Examples₂.CD.ballU_pos p q lam hr).ne', (Examples₂.CD.ballU_lt_top p q lam r).ne⟩)
  have hcc : c' = c := tendsto_nhds_unique h1 ht
  subst hcc
  exact h S hm
    (fun δ hδ => by
      filter_upwards [hS δ hδ] with r hr X hX
      exact lt_of_le_of_lt (Examples₂.CD.norm_le_sum p q X) (hr hX))
    (by
      filter_upwards [h0, hS 1 one_pos] with r hr hr1
      exact ⟨hr, ne_top_of_le_ne_top (Examples₂.CD.ballU_lt_top p q lam 1).ne (measure_mono hr1)⟩)

end Density

theorem exists_sign {p q : ℕ} (a b : Fin p ⊕ Fin q) : ∃ σ : ℂ, σ * σ = 1 ∧ ‖σ‖ = 1 ∧ ∀ X : lieU p q,
    star (X.1 b a) = σ * X.1 a b := by
  have key : ∀ X : lieU p q, (X.1ᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * X.1) a b = 0 := by
    intro X
    have hX : X.1ᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * X.1 = 0 := X.2
    rw [hX]; rfl
  rcases a with i | i <;> rcases b with j | j
  · refine ⟨-1, by simp, by simp, fun X => ?_⟩
    have := key X
    simp [Formalism.UG.Jpq, Matrix.mul_apply, Matrix.one_apply] at this
    simp only [Complex.star_def]
    linear_combination this
  · refine ⟨1, by simp, by simp, fun X => ?_⟩
    have := key X
    simp [Formalism.UG.Jpq, Matrix.mul_apply, Matrix.one_apply] at this
    simp only [Complex.star_def]
    linear_combination -this
  · refine ⟨1, by simp, by simp, fun X => ?_⟩
    have := key X
    simp [Formalism.UG.Jpq, Matrix.mul_apply, Matrix.one_apply] at this
    simp only [Complex.star_def]
    linear_combination this
  · refine ⟨-1, by simp, by simp, fun X => ?_⟩
    have := key X
    simp [Formalism.UG.Jpq, Matrix.mul_apply, Matrix.one_apply] at this
    simp only [Complex.star_def]
    linear_combination -this

def box {p q : ℕ} (r : Fin p ⊕ Fin q → Fin p ⊕ Fin q → ℝ) : Set (lieU p q) := {X | ∀ a b, ‖X.1 a b‖ < r a b}

theorem measurableSet_box {p q : ℕ} (r : Fin p ⊕ Fin q → Fin p ⊕ Fin q → ℝ) : MeasurableSet (box r) := by
  haveI : BorelSpace (lieU p q) := ⟨rfl⟩
  refine IsOpen.measurableSet ?_
  unfold box
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
  exact isOpen_lt (continuous_subtype_val.matrix_elem a b).norm continuous_const

theorem le_lam_box {p q : ℕ} (lam : Measure (lieU p q)) (h : IsOmegaLeb lam)
    (r s : Fin p ⊕ Fin q → Fin p ⊕ Fin q → ℝ) (hr : ∀ a b, r a b = r b a) (hr0 : ∀ a b, 0 ≤ r a b)
    (hs0 : ∀ a b, 0 ≤ s a b) (hs : ∀ a b, s a b ^ 2 ≤ r a b ^ 2 * Real.pi) :
    ENNReal.ofReal (∏ a, ∏ b, s a b) ≤ lam (box r) := by
  haveI : BorelSpace (lieU p q) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace ((Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → ℂ))
  haveI : LocallyCompactSpace (lieU p q) :=
    (Submodule.closed_of_finiteDimensional (lieU p q)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (lieU p q) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨h1, h2⟩ := h
  have hm := AEMeasurable.of_map_ne_zero (h2 ▸ (NeZero.ne volume))
  have hT : MeasurableSet (Set.univ.pi fun ab : (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) =>
      Metric.ball (0 : ℂ) (r ab.1 ab.2)) := MeasurableSet.univ_pi fun _ => measurableSet_ball
  have he := Measure.map_apply_of_aemeasurable hm hT
  rw [h2, volume_pi_pi] at he
  refine (ENNReal.pow_le_pow_left_iff two_ne_zero).1 ?_
  calc ENNReal.ofReal (∏ a, ∏ b, s a b) ^ 2
      = ∏ ab : (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q), ENNReal.ofReal (s ab.1 ab.2 ^ 2) := by
        rw [← Fintype.prod_prod_type', ENNReal.ofReal_prod_of_nonneg fun _ _ => hs0 _ _, ← Finset.prod_pow]
        exact Finset.prod_congr rfl fun ab _ => (ENNReal.ofReal_pow (hs0 _ _) 2).symm
    _ ≤ ∏ ab : (Fin p ⊕ Fin q) × (Fin p ⊕ Fin q), volume (Metric.ball (0 : ℂ) (r ab.1 ab.2)) := by
        refine Finset.prod_le_prod' fun ab _ => ?_
        rw [Complex.volume_ball, ← ENNReal.ofReal_pow (hr0 _ _), ← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_mul (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hs _ _)
    _ ≤ (lam.prod lam) (box r ×ˢ box r) := by
        rw [he]
        refine measure_mono ?_
        rintro ⟨x, y⟩ hxy
        have hz : ∀ a b, ‖x.1 a b + Complex.I * y.1 a b‖ < r a b := by
          intro a b
          have := hxy (a, b) (Set.mem_univ _)
          simpa [Formalism.BasicNotions.entries] using this
        have key : ∀ a b, ‖x.1 a b‖ < r a b ∧ ‖y.1 a b‖ < r a b := by
          intro a b
          obtain ⟨σ, hσ, hσ1, hX⟩ := exists_sign a b
          have h3 : ‖σ * star (x.1 b a + Complex.I * y.1 b a)‖ < r a b := by
            rw [norm_mul, hσ1, one_mul, norm_star, hr a b]; exact hz b a
          have e : σ * star (x.1 b a + Complex.I * y.1 b a) = x.1 a b - Complex.I * y.1 a b := by
            rw [star_add, star_mul', hX x, hX y, Complex.star_def, Complex.conj_I]
            linear_combination (x.1 a b - Complex.I * y.1 a b) * hσ
          rw [e] at h3
          have h4 := hz a b
          have h5 := norm_add_le (x.1 a b + Complex.I * y.1 a b) (x.1 a b - Complex.I * y.1 a b)
          have h6 := norm_sub_le (x.1 a b + Complex.I * y.1 a b) (x.1 a b - Complex.I * y.1 a b)
          rw [show x.1 a b + Complex.I * y.1 a b + (x.1 a b - Complex.I * y.1 a b) = 2 * x.1 a b by ring,
            norm_mul, Complex.norm_two] at h5
          rw [show x.1 a b + Complex.I * y.1 a b - (x.1 a b - Complex.I * y.1 a b) =
            2 * (Complex.I * y.1 a b) by ring, norm_mul, norm_mul, Complex.norm_two, Complex.norm_I] at h6
          constructor <;> linarith
        exact ⟨fun a b => (key a b).1, fun a b => (key a b).2⟩
    _ = lam (box r) ^ 2 := by rw [Measure.prod_prod, sq]

theorem exists_exp_approx (n : Type) [Fintype n] [DecidableEq n] (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ ∀ Y : Matrix n n ℂ, ∑ i, ∑ j, ‖Y i j‖ < r →
      ∀ a b, ‖(NormedSpace.exp Y - 1 - Y) a b‖ ≤ δ * ∑ i, ∑ j, ‖Y i j‖ := by
  letI := GlobalTheory.CompactDualExists.sumNormedAddCommGroup (n := n)
  letI := GlobalTheory.CompactDualExists.sumNormedSpace (n := n)
  have h := (GlobalTheory.CompactDualExists.exp_strict (n := n)).hasFDerivAt
  have h2 := h.isLittleO.def hδ
  obtain ⟨r, hr, H⟩ := Metric.eventually_nhds_iff_ball.1 h2
  refine ⟨r, hr, fun Y hY a b => ?_⟩
  rw [← GlobalTheory.CompactDualExists.sum_norm_def] at hY ⊢
  have h3 := H Y (mem_ball_zero_iff.2 hY)
  rw [NormedSpace.exp_zero, sub_zero] at h3
  refine le_trans ?_ h3
  rw [GlobalTheory.CompactDualExists.sum_norm_def]
  exact (Finset.single_le_sum (f := fun j => ‖(NormedSpace.exp Y - 1 - Y) a j‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ b)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖(NormedSpace.exp Y - 1 - Y) i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a))

theorem norm_sMat_dg_mul {p q : ℕ} (a₀ : Fin p ⊕ Fin q) {c : ℂ} (hc : ‖c‖ = 1) (d u : UpqT p q)
    (hd : UpqT.mat d = dg a₀ c) (a b : Fin p ⊕ Fin q) :
    ‖(sMat a₀ (d * u) - 1) a b‖ = ‖(sMat a₀ u - 1) a b‖ := by
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  have hmat : UpqT.mat (d * u) = dg a₀ c * UpqT.mat u := by rw [GlobalTheory.CartanInt.mat_mul, hd]
  unfold sMat
  rw [hmat, Matrix.det_mul, det_dg]
  simp only [dg, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Function.update_apply, Pi.one_apply]
  by_cases ha : a = a₀ <;> by_cases hb : b = a₀
  · simp only [ha, hb, if_true]
    congr 2
    rw [mul_inv]; field_simp
  · have : a ≠ b := by rintro rfl; exact hb ha
    rw [Matrix.one_apply_ne this]
    simp [ha, hb, hc]
  · have : a ≠ b := by rintro rfl; exact ha hb
    rw [Matrix.one_apply_ne this]
    simp [ha, hb, hc]
  · simp [ha, hb]

def rad {ι : Type} [DecidableEq ι] (a₀ : ι) (n t : ℝ) (a b : ι) : ℝ := t * (if a = b ∧ a ≠ a₀ then n⁻¹ else 1)

theorem rad_symm {ι : Type} [DecidableEq ι] (a₀ : ι) (n t : ℝ) (a b : ι) : rad a₀ n t a b = rad a₀ n t b a := by
  unfold rad
  by_cases h : a = b
  · subst h; rfl
  · simp [h, Ne.symm h]

theorem rad_le {ι : Type} [DecidableEq ι] (a₀ : ι) {n t : ℝ} (hn : 1 ≤ n) (ht : 0 ≤ t) (a b : ι) :
    rad a₀ n t a b ≤ t := by
  unfold rad
  split_ifs
  · exact mul_le_of_le_one_right ht (inv_le_one_of_one_le₀ hn)
  · simp

theorem rad_nonneg {ι : Type} [DecidableEq ι] (a₀ : ι) {n t : ℝ} (hn : 0 ≤ n) (ht : 0 ≤ t) (a b : ι) :
    0 ≤ rad a₀ n t a b := by
  unfold rad
  split_ifs <;> positivity

theorem prod_rad {ι : Type} [Fintype ι] [DecidableEq ι] (a₀ : ι) (n t : ℝ) :
    ∏ a, ∏ b, rad a₀ n t a b = t ^ (Fintype.card ι ^ 2) / n ^ (Fintype.card ι - 1) := by
  unfold rad
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have h1 : ∀ a : ι, (∏ b : ι, if a = b ∧ a ≠ a₀ then n⁻¹ else 1) = if a ∈ Finset.univ.erase a₀ then n⁻¹ else 1 := by
    intro a
    by_cases h : a = a₀
    · simp [h]
    · simp [h]
  simp only [h1]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ← pow_mul, ← sq, inv_pow, div_eq_mul_inv]

theorem sum_le_of_mem_box {p q : ℕ} (a₀ : Fin p ⊕ Fin q) {n t : ℝ} (hn : n = ((p + q : ℕ) : ℝ)) (hn1 : 1 ≤ n)
    (ht : 0 ≤ t) {X : lieU p q} (hX : X ∈ box (rad a₀ n t)) : ∑ i, ∑ j, ‖X.1 i j‖ ≤ n ^ 2 * t := by
  calc ∑ i, ∑ j, ‖X.1 i j‖ ≤ ∑ _i : Fin p ⊕ Fin q, ∑ _j : Fin p ⊕ Fin q, t :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => (hX i j).le.trans (rad_le a₀ hn1 ht i j)
    _ = n ^ 2 * t := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul]
        rw [hn]; push_cast; ring

theorem exp_box {p q : ℕ} (a₀ : Fin p ⊕ Fin q) {n : ℝ} (hn : n = ((p + q : ℕ) : ℝ)) (hn1 : 1 ≤ n) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ X ∈ box (rad a₀ n (9 / 10 * ε)), ∀ u : UpqT p q,
      UpqT.mat u = NormedSpace.exp (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) →
      (∀ a b, ‖(sMat a₀ u - 1) a b‖ < ε) ∧
        ∃ t : ℝ, |t| < 2 * ε ∧ (UpqT.mat u).det = Complex.exp (t * Complex.I) := by
  have hn2 : 0 < n ^ 2 := by positivity
  obtain ⟨r, hr, H⟩ := exists_exp_approx (Fin p ⊕ Fin q) (1 / (40 * n ^ 2)) (by positivity)
  refine ⟨min (1 / 100) (r / n ^ 2), by positivity, fun ε hε hεlt X hX u hu => ?_⟩
  have hε1 : ε < 1 / 100 := hεlt.trans_le (min_le_left _ _)
  have hεr : n ^ 2 * ε < r := by
    have := hεlt.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ hn2] at this; linarith
  have hsum := sum_le_of_mem_box a₀ hn hn1 (by positivity) hX
  have herr : ∀ a b, ‖(UpqT.mat u - 1 - X.1) a b‖ ≤ ε / 40 := by
    intro a b
    rw [hu]
    refine (H X.1 (by nlinarith) a b).trans ?_
    calc 1 / (40 * n ^ 2) * ∑ i, ∑ j, ‖X.1 i j‖ ≤ 1 / (40 * n ^ 2) * (n ^ 2 * ε) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      _ = ε / 40 := by field_simp
  have hent : ∀ a b, ‖X.1 a b‖ < 9 / 10 * ε := fun a b => (hX a b).trans_le (rad_le a₀ hn1 (by positivity) a b)
  have hent' : ∀ a b, ‖(UpqT.mat u - 1) a b‖ < ε := by
    intro a b
    have h1 := herr a b
    rw [Matrix.sub_apply] at h1
    have h2 := norm_le_norm_add_norm_sub' ((UpqT.mat u - 1) a b) (X.1 a b)
    linarith [hent a b]
  have hrest : ‖∑ i ∈ Finset.univ.erase a₀, X.1 i i‖ ≤ 9 / 10 * ε := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ Finset.univ.erase a₀, ‖X.1 i i‖ ≤ ∑ _i ∈ Finset.univ.erase a₀, 9 / 10 * ε * n⁻¹ := by
          refine Finset.sum_le_sum fun i hi => ?_
          have h1 := (hX i i).le
          rwa [rad, if_pos ⟨rfl, Finset.ne_of_mem_erase hi⟩] at h1
      _ ≤ ∑ _i : Fin p ⊕ Fin q, 9 / 10 * ε * n⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun _ _ _ => by positivity
      _ = 9 / 10 * ε := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul]
          rw [← hn]; field_simp
  have htr : X.1.trace = X.1 a₀ a₀ + ∑ i ∈ Finset.univ.erase a₀, X.1 i i :=
    (Finset.add_sum_erase Finset.univ (fun i => X.1 i i) (Finset.mem_univ a₀)).symm
  have htrn : ‖X.1.trace‖ < 9 / 5 * ε := by
    rw [htr]
    have := norm_add_le (X.1 a₀ a₀) (∑ i ∈ Finset.univ.erase a₀, X.1 i i)
    linarith [hent a₀ a₀]
  have hdet : (UpqT.mat u).det = Complex.exp X.1.trace := by rw [hu]; exact GlobalTheory.DetSqrtCover.det_exp X.1
  have hz1 : ‖(UpqT.mat u).det‖ = 1 := GlobalTheory.CovTop.VolUp.OneMeasure.norm_det_mat u
  have hz0 : (UpqT.mat u).det ≠ 0 := by intro h; rw [h, norm_zero] at hz1; exact zero_ne_one hz1
  refine ⟨fun a b => ?_, X.1.trace.im, ?_, ?_⟩
  · have h0 := hent' a b
    unfold sMat
    simp only [dg, Matrix.sub_apply, Matrix.mul_diagonal, Function.update_apply, Pi.one_apply] at h0 ⊢
    by_cases hb : b = a₀
    · rw [if_pos hb]
      by_cases hab : a = b
      · subst hab
        subst hb
        rw [Matrix.one_apply_eq]
        have h1 := herr a a
        simp only [Matrix.sub_apply, Matrix.one_apply_eq] at h1
        have h2 := Complex.norm_exp_sub_one_sub_id_le (x := X.1.trace) (by linarith)
        rw [← hdet] at h2
        have e : UpqT.mat u a a * (UpqT.mat u).det⁻¹ - 1 =
            ((UpqT.mat u a a - 1 - X.1 a a) - ((UpqT.mat u).det - 1 - X.1.trace) -
              ∑ i ∈ Finset.univ.erase a, X.1 i i) * (UpqT.mat u).det⁻¹ := by
          rw [htr]; field_simp; ring
        rw [e, norm_mul, norm_inv, hz1, inv_one, mul_one]
        have h3 := norm_sub_le ((UpqT.mat u a a - 1 - X.1 a a) - ((UpqT.mat u).det - 1 - X.1.trace))
          (∑ i ∈ Finset.univ.erase a, X.1 i i)
        have h4 := norm_sub_le (UpqT.mat u a a - 1 - X.1 a a) ((UpqT.mat u).det - 1 - X.1.trace)
        have h5 : ‖X.1.trace‖ ^ 2 ≤ ε / 20 := by nlinarith [norm_nonneg X.1.trace]
        linarith
      · rw [Matrix.one_apply_ne hab, sub_zero] at h0 ⊢
        rwa [norm_mul, norm_inv, hz1, inv_one, mul_one]
    · rwa [if_neg hb, mul_one]
  · linarith [Complex.abs_im_le_norm X.1.trace]
  · rw [hdet, Complex.norm_exp, Real.exp_eq_one_iff] at hz1
    rw [hdet]
    congr 1
    apply Complex.ext <;> simp [hz1]

theorem num_ge (N : ℕ) (hN : 1 ≤ N) (ε K : ℝ) (hε : 0 < ε) (hK : 3 / (4 * ε) ≤ K) :
    ε ^ (N ^ 2 - 1) / (N : ℝ) ^ (N - 1) ≤
      K * (9 / 10 * ((2 : ℝ) ^ (N * (N - 1) / 2))⁻¹ * ((3 / 2 * ε) ^ (N ^ 2) / (N : ℝ) ^ (N - 1))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hK0 : 0 ≤ K := le_trans (by positivity) hK
  set k := N * (N - 1) / 2 with hk
  have h1 : 2 * k + 1 ≤ N ^ 2 := by
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le' hN
    have : 2 * k ≤ (M + 1) * (M + 1 - 1) := Nat.mul_div_le _ _
    rw [Nat.add_sub_cancel] at this
    nlinarith
  obtain ⟨M, hM⟩ : ∃ M, N ^ 2 = M + 1 := ⟨N ^ 2 - 1, by omega⟩
  have h2 : 3 / 2 * (2 : ℝ) ^ k ≤ (3 / 2) ^ (M + 1) := by
    calc 3 / 2 * (2 : ℝ) ^ k ≤ 3 / 2 * ((3 / 2 : ℝ) ^ 2) ^ k := by gcongr; norm_num
      _ = (3 / 2) ^ (2 * k + 1) := by rw [← pow_mul, pow_succ]; ring
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [hM, Nat.add_sub_cancel]
  calc ε ^ M / (N : ℝ) ^ (N - 1) ≤ (81 / 80) * (ε ^ M / (N : ℝ) ^ (N - 1)) :=
        le_mul_of_one_le_left (by positivity) (by norm_num)
    _ = 3 / (4 * ε) * (9 / 10 * ((2 : ℝ) ^ k)⁻¹ * ((3 / 2 * 2 ^ k) * ε ^ (M + 1) / (N : ℝ) ^ (N - 1))) := by
        field_simp; ring
    _ ≤ _ := by rw [mul_pow]; gcongr

theorem le_measure_sMat_near : ∀ (p q : ℕ) (a₀ : Fin p ⊕ Fin q) (m : Measure (UpqT p q)), IsMinf m → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ENNReal.ofReal (ε ^ ((p + q) ^ 2 - 1) / ((p + q : ℕ) : ℝ) ^ (p + q - 1)) ≤ m {u | (∀ a b, ‖(sMat a₀ u - 1) a b‖ < ε) ∧ 0 < (UpqT.mat u).det.im} := by
  intro p q a₀ m hm
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc p q
  obtain ⟨hH, lam, hlam, ht⟩ := hm
  have hpq : 1 ≤ p + q := by
    rcases a₀ with i | i
    · have := i.pos; omega
    · have := i.pos; omega
  set n : ℝ := ((p + q : ℕ) : ℝ) with hn
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast hpq
  have hn2 : 0 < n ^ 2 := by positivity
  have hlow : ∀ ε : ℝ, 0 < ε → ENNReal.ofReal ((3 / 2 * ε) ^ ((p + q) ^ 2) / n ^ (p + q - 1)) ≤
      lam (box (rad a₀ n (9 / 10 * ε))) := by
    intro ε hε
    have := le_lam_box lam hlam (rad a₀ n (9 / 10 * ε)) (rad a₀ n (3 / 2 * ε)) (rad_symm a₀ n _)
      (rad_nonneg a₀ (by linarith) (by positivity)) (rad_nonneg a₀ (by linarith) (by positivity)) (by
        intro a b
        unfold rad
        generalize (if a = b ∧ a ≠ a₀ then n⁻¹ else 1) = w
        nlinarith [mul_nonneg (sq_nonneg (ε * w)) (sub_nonneg.2 Real.pi_gt_three.le), sq_nonneg (ε * w)])
    rwa [prod_rad, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at this
  have hT := tendsto_of_density m hH lam hlam.1 _ ht (fun ε => box (rad a₀ n (9 / 10 * ε)))
    (fun _ => measurableSet_box _)
    (fun δ hδ => by
      filter_upwards [Ioo_mem_nhdsGT (show 0 < δ / n ^ 2 by positivity)] with r hr X hX
      have h1 := sum_le_of_mem_box a₀ hn hn1 (by linarith [hr.1]) hX
      have h2 := hr.2
      rw [lt_div_iff₀ hn2] at h2
      exact h1.trans_lt (by nlinarith [mul_pos hr.1 hn2]))
    (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : 0 < r := hr
      exact (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by positivity)) (hlow r hr')).ne')
  have hc : ENNReal.ofReal (9 / 10 * ((2 : ℝ) ^ ((p + q) * (p + q - 1) / 2))⁻¹) < minfDensity (p + q) := by
    have e : minfDensity (p + q) = ENNReal.ofReal (((2 : ℝ) ^ ((p + q) * (p + q - 1) / 2))⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
      rfl
    rw [e, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact mul_lt_of_lt_one_left (by positivity) (by norm_num)
  obtain ⟨r₁, hr₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hT.eventually (lt_mem_nhds hc))
  have hr₁' : 0 < r₁ := hr₁
  obtain ⟨r₂, hr₂, hbox⟩ := exp_box a₀ hn hn1
  refine ⟨min (1 / 100) (min r₁ r₂), by positivity, fun ε hε hεlt => ?_⟩
  have hε1 : ε < 1 / 100 := hεlt.trans_le (min_le_left _ _)
  have hεr₁ : ε < r₁ := hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεr₂ : ε < r₂ := hεlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  set B : Set (UpqT p q) := {g | ∃ X ∈ box (rad a₀ n (9 / 10 * ε)), UpqT.mat g =
      NormedSpace.exp (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)} with hB
  have hE : ENNReal.ofReal (9 / 10 * ((2 : ℝ) ^ ((p + q) * (p + q - 1) / 2))⁻¹ *
      ((3 / 2 * ε) ^ ((p + q) ^ 2) / n ^ (p + q - 1))) ≤ m B := by
    have hr : ENNReal.ofReal (9 / 10 * ((2 : ℝ) ^ ((p + q) * (p + q - 1) / 2))⁻¹) <
        m B / lam (box (rad a₀ n (9 / 10 * ε))) := hsub ⟨hε, hεr₁⟩
    rw [ENNReal.ofReal_mul (by positivity)]
    exact (mul_le_mul_right (hlow ε hε) _).trans (ENNReal.mul_le_of_le_div hr.le)
  set S : Set (UpqT p q) := {u | (∀ a b, ‖(sMat a₀ u - 1) a b‖ < ε) ∧ 0 < (UpqT.mat u).det.im} with hS
  set K : ℕ := ⌊Real.pi / (4 * ε)⌋₊ with hK
  have hK1 : (K : ℝ) * (4 * ε) ≤ Real.pi := by
    rw [← le_div_iff₀ (by positivity)]; exact Nat.floor_le (by positivity)
  have hK2 : 3 / (4 * ε) ≤ (K : ℝ) := by
    have h1 : Real.pi / (4 * ε) < K + 1 := Nat.lt_floor_add_one _
    rw [div_lt_iff₀ (by positivity)] at h1
    rw [div_le_iff₀ (by positivity)]
    linarith [Real.pi_gt_d2]
  set T : ℕ → Set (UpqT p q) := fun k =>
    (fun u => (UpqT.mat u).det.arg) ⁻¹' Set.Ioo ((k : ℝ) * (4 * ε)) (((k : ℝ) + 1) * (4 * ε)) with hTdef
  have hTm : ∀ k, MeasurableSet (T k) := fun k =>
    (Complex.measurable_arg.comp (GlobalTheory.CompactDualExists.continuous_mat.matrix_det).measurable) measurableSet_Ioo
  have hdisj : Set.Pairwise (↑(Finset.range K) : Set ℕ) (Function.onFun (AEDisjoint (m.restrict S)) T) := by
    have key : ∀ i j : ℕ, i < j → Disjoint (T i) (T j) := by
      intro i j hij
      rw [Set.disjoint_left]
      intro u h1 h2
      have h3 : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      have h4 := h1.2
      have h5 := h2.1
      nlinarith [mul_le_mul_of_nonneg_right h3 (show 0 ≤ 4 * ε by positivity)]
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact (key i j h).aedisjoint
    · exact (key j i h).symm.aedisjoint
  have hsum := sum_measure_le_measure_univ (μ := m.restrict S) (fun k _ => (hTm k).nullMeasurableSet) hdisj
  rw [Measure.restrict_apply_univ] at hsum
  have hk : ∀ k ∈ Finset.range K, m B ≤ m.restrict S (T k) := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ K := by exact_mod_cast Finset.mem_range.1 hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    set θ : ℝ := (k : ℝ) * (4 * ε) + 2 * ε with hθ
    have hc1 : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    obtain ⟨d, hd⟩ := GlobalTheory.CovTop.VolUp.OneMeasure.exists_of_dg a₀ hc1
    rw [Measure.restrict_apply (hTm k), ← measure_preimage_mul m d (T k ∩ S)]
    refine measure_mono ?_
    rintro u ⟨X, hX, hu⟩
    obtain ⟨h1, t, ht1, ht2⟩ := hbox ε hε hεr₂ X hX u hu
    rw [abs_lt] at ht1
    have hdet : (UpqT.mat (d * u)).det = Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I) := by
      rw [GlobalTheory.CartanInt.mat_mul, hd, Matrix.det_mul, det_dg, ht2, ← Complex.exp_add]
      congr 1; push_cast; ring
    have hpos : 0 < θ + t := by nlinarith [mul_nonneg hk0 hε.le]
    have hpi : θ + t < Real.pi := by
      nlinarith [mul_le_mul_of_nonneg_right hk' (show 0 ≤ 4 * ε by positivity)]
    refine ⟨?_, fun a b => ?_, ?_⟩
    · show (UpqT.mat (d * u)).det.arg ∈ Set.Ioo ((k : ℝ) * (4 * ε)) (((k : ℝ) + 1) * (4 * ε))
      rw [hdet, Complex.exp_mul_I, Complex.arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], hpi.le⟩]
      constructor <;> linarith [ht1.1, ht1.2]
    · rw [norm_sMat_dg_mul a₀ hc1 d u hd]; exact h1 a b
    · rw [hdet, Complex.exp_ofReal_mul_I_im]
      exact Real.sin_pos_of_pos_of_lt_pi hpos hpi
  refine le_trans ?_ ((Finset.sum_le_sum hk).trans hsum)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine le_trans ?_ (mul_le_mul_right hE _)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (num_ge (p + q) hpq ε K hε hK2)

end GlobalTheory.CovTop.VolLow.OneMeasure
