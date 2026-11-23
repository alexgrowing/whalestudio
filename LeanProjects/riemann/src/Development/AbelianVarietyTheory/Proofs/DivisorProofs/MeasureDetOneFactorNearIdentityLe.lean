import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpLogNearOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LamBallULe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.OneMeasure

open Filter Topology

theorem norm_update_one {ι : Type} [DecidableEq ι] (a₀ a : ι) {c : ℂ} (hc : ‖c‖ = 1) :
    ‖Function.update (1 : ι → ℂ) a₀ c a‖ = 1 := by
  rw [Function.update_apply]; split_ifs <;> simp [hc]

theorem dg_unitary {p q : ℕ} (a₀ : Fin p ⊕ Fin q) {c : ℂ} (hc : ‖c‖ = 1) :
    (dg a₀ c)ᴴ * Formalism.UG.Jpq p q * dg a₀ c = Formalism.UG.Jpq p q := by
  ext a b
  simp only [dg, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hab : a = b
  · subst hab
    have h1 : star (Function.update (1 : Fin p ⊕ Fin q → ℂ) a₀ c a) *
        Function.update (1 : Fin p ⊕ Fin q → ℂ) a₀ c a = 1 := by
      rw [Complex.star_def, Complex.conj_mul', norm_update_one a₀ a hc]; simp
    calc _ = (star (Function.update (1 : Fin p ⊕ Fin q → ℂ) a₀ c a) *
        Function.update (1 : Fin p ⊕ Fin q → ℂ) a₀ c a) * Formalism.UG.Jpq p q a a := by
          simp only [Pi.star_apply]; ring
      _ = _ := by rw [h1, one_mul]
  · have : Formalism.UG.Jpq p q a b = 0 := by
      rcases a with i | i <;> rcases b with j | j <;>
        simp_all [Formalism.UG.Jpq, Matrix.one_apply]
    simp [this]

theorem exists_of_dg {p q : ℕ} (a₀ : Fin p ⊕ Fin q) {c : ℂ} (hc : ‖c‖ = 1) :
    ∃ d : UpqT p q, UpqT.mat d = dg a₀ c := by
  have h : dg a₀ c ∈ Set.range (UpqT.mat (P := p) (Q := q)) := by
    rw [GlobalTheory.UpqTopology.range_mat]; exact dg_unitary a₀ hc
  exact h

theorem norm_det_mat {p q : ℕ} (u : UpqT p q) : ‖(UpqT.mat u).det‖ = 1 := by
  have h := congrArg Matrix.det (GlobalTheory.UpqTopology.mat_unitary u)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hJ : (Formalism.UG.Jpq p q).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det (GlobalTheory.UpqTopology.jpq_sq (P := p) (Q := q))
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have h2 : star (UpqT.mat u).det * (UpqT.mat u).det = 1 := by
    have : (star (UpqT.mat u).det * (UpqT.mat u).det) * (Formalism.UG.Jpq p q).det =
        1 * (Formalism.UG.Jpq p q).det := by
      rw [one_mul]; nth_rewrite 2 [← h]; ring
    exact mul_right_cancel₀ hJ this
  rw [Complex.star_def, Complex.conj_mul'] at h2
  have h3 : ‖(UpqT.mat u).det‖ ^ 2 = 1 := by exact_mod_cast h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3

theorem mat_eq_sMat_mul {p q : ℕ} (a₀ : Fin p ⊕ Fin q) (u : UpqT p q) (hz : (UpqT.mat u).det ≠ 0)
    (a b : Fin p ⊕ Fin q) :
    UpqT.mat u a b = sMat a₀ u a b * Function.update (1 : Fin p ⊕ Fin q → ℂ) a₀ (UpqT.mat u).det b := by
  simp only [sMat, dg, Matrix.mul_diagonal, Function.update_apply]
  split_ifs
  · rw [mul_assoc, inv_mul_cancel₀ hz, mul_one]
  · simp

theorem entry_lt {ι : Type} [DecidableEq ι] (a₀ : ι) {c z : ℂ} {ε : ℝ} (hc : ‖c‖ = 1) (hz : ‖z‖ = 1)
    (hcz : ‖c * z - 1‖ ≤ ε) (S : Matrix ι ι ℂ) (hS : ∀ a b, ‖(S - 1) a b‖ < ε) (a b : ι) :
    ‖Function.update (1 : ι → ℂ) a₀ c a * (S a b * Function.update (1 : ι → ℂ) a₀ z b) -
      (1 : Matrix ι ι ℂ) a b‖ < 2 * ε := by
  have hca := norm_update_one a₀ a hc
  have hzb := norm_update_one a₀ b hz
  have hε : 0 < ε := lt_of_le_of_lt (norm_nonneg _) (hS a b)
  by_cases hab : a = b
  · subst hab
    have h1 := hS a a
    rw [Matrix.sub_apply, Matrix.one_apply_eq] at h1
    rw [Matrix.one_apply_eq]
    have h2 : ‖Function.update (1 : ι → ℂ) a₀ c a * Function.update (1 : ι → ℂ) a₀ z a - 1‖ ≤ ε := by
      rw [Function.update_apply, Function.update_apply]
      split_ifs
      · exact hcz
      · simp; exact hε.le
    have e : Function.update (1 : ι → ℂ) a₀ c a * (S a a * Function.update (1 : ι → ℂ) a₀ z a) - 1 =
        (Function.update (1 : ι → ℂ) a₀ c a * Function.update (1 : ι → ℂ) a₀ z a) * (S a a - 1) +
          (Function.update (1 : ι → ℂ) a₀ c a * Function.update (1 : ι → ℂ) a₀ z a - 1) := by ring
    rw [e]
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_mul, norm_mul, hca, hzb]
    linarith
  · have h1 := hS a b
    rw [Matrix.sub_apply, Matrix.one_apply_ne hab, sub_zero] at h1
    rw [Matrix.one_apply_ne hab, sub_zero, norm_mul, norm_mul, hca, hzb]
    linarith

theorem num_le (n ε C : ℝ) (N : ℕ) (hn : 1 ≤ n) (hN : 1 ≤ N) (hε : 0 < ε) (hC : C ≤ 9 / ε) :
    C * (2 * (18 / 5 * (11 / 5 * n ^ 2 * ε) / n) ^ N) ≤ (200 * n) ^ N * ε ^ (N - 1) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le' hN
  have hn0 : 0 < n := by linarith
  have e : 18 / 5 * (11 / 5 * n ^ 2 * ε) / n = 198 / 25 * n * ε := by field_simp; ring
  rw [e, Nat.add_sub_cancel]
  have key : C * (2 * (198 / 25 * n * ε) ^ (M + 1)) ≤ 9 / ε * (2 * (198 / 25 * n * ε) ^ (M + 1)) :=
    mul_le_mul_of_nonneg_right hC (by positivity)
  refine key.trans ?_
  have e2 : 9 / ε * (2 * (198 / 25 * n * ε) ^ (M + 1)) =
      (18 * (198 / 25)) * ((198 / 25) ^ M * (n ^ (M + 1) * ε ^ M)) := by
    rw [mul_pow, mul_pow, pow_succ ε, pow_succ (198 / 25 : ℝ)]; field_simp; ring
  rw [e2]
  calc (18 * (198 / 25)) * ((198 / 25 : ℝ) ^ M * (n ^ (M + 1) * ε ^ M))
      ≤ 200 * ((200 : ℝ) ^ M * (n ^ (M + 1) * ε ^ M)) := by
        gcongr
        · norm_num
        · norm_num
    _ = (200 * n) ^ (M + 1) * ε ^ M := by ring

end GlobalTheory.CovTop.VolUp.OneMeasure

namespace GlobalTheory.CovTop.VolUp.OneMeasure

open Filter Topology

theorem measure_sMat_near_le : ∀ (p q : ℕ) (a₀ : Fin p ⊕ Fin q) (m : Measure (UpqT p q)), IsMinf m →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      m {u | ∀ a b, ‖(sMat a₀ u - 1) a b‖ < ε} ≤
        ENNReal.ofReal ((200 * ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2) * ε ^ ((p + q) ^ 2 - 1)) := by
  intro p q a₀ m hm
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc p q
  obtain ⟨hH, lam, hlam, ht⟩ := hm
  obtain ⟨ρ₀, hρ₀, -, hlog⟩ := GlobalTheory.CartanInt.ExpLocal.exp_log_near_one p q
  have hpq : 1 ≤ p + q := by
    rcases a₀ with i | i
    · have := i.pos; omega
    · have := i.pos; omega
  set n : ℝ := ((p + q : ℕ) : ℝ) with hn
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast hpq
  have hn2 : 0 < n ^ 2 := by positivity
  have hc : minfDensity (p + q) < 2 :=
    lt_of_le_of_lt (ENNReal.inv_le_one.2 (one_le_pow₀ one_le_two)) (by norm_num)
  obtain ⟨r₁, hr₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (ht.eventually (gt_mem_nhds hc))
  have hr₁' : 0 < r₁ := hr₁
  refine ⟨min (1 / 3) (min (ρ₀ / (2 * n ^ 2)) (r₁ / (3 * n ^ 2))),
    lt_min (by norm_num) (lt_min (by positivity) (by positivity)), fun ε hε hεlt => ?_⟩
  have hε3 : ε < 1 / 3 := hεlt.trans_le (min_le_left _ _)
  have hερ : 2 * n ^ 2 * ε < ρ₀ := by
    have := hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    rw [lt_div_iff₀ (by positivity)] at this; linarith
  have hεr : 3 * n ^ 2 * ε < r₁ := by
    have := hεlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    rw [lt_div_iff₀ (by positivity)] at this; linarith
  set ρ : ℝ := 11 / 5 * n ^ 2 * ε with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρr : ρ < r₁ := by rw [hρ]; nlinarith

  have hE : m {g | ∃ X ∈ ballU p q ρ, UpqT.mat g =
      NormedSpace.exp (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)} ≤
      2 * ENNReal.ofReal ((18 / 5 * ρ / n) ^ ((p + q) ^ 2)) := by
    have hr : m {g | ∃ X ∈ ballU p q ρ, UpqT.mat g =
        NormedSpace.exp (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)} / lam (ballU p q ρ) < 2 :=
      hsub ⟨hρ0, hρr⟩
    have hl := GlobalTheory.CartanInt.LamBall.lam_ballU_le p q lam hlam ρ hρ0
    by_cases h0 : m {g | ∃ X ∈ ballU p q ρ, UpqT.mat g =
        NormedSpace.exp (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)} = 0
    · rw [h0]; exact zero_le
    have h1 := (ENNReal.div_lt_iff (Or.inr h0) (Or.inl (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hl))).1 hr
    exact h1.le.trans (by gcongr)

  set K : ℤ := ⌈4 / ε⌉ with hK
  have hd : ∀ k : ℤ, ∃ d : UpqT p q, UpqT.mat d =
      dg a₀ (Complex.exp (((-((k : ℝ) * ε)) : ℝ) * Complex.I)) :=
    fun k => exists_of_dg a₀ (Complex.norm_exp_ofReal_mul_I _)
  choose d hd using hd
  have hcover : {u : UpqT p q | ∀ a b, ‖(sMat a₀ u - 1) a b‖ < ε} ⊆
      ⋃ k ∈ Finset.Icc (-K) K, (fun x => d k * x) ⁻¹' {g | ∃ X ∈ ballU p q ρ, UpqT.mat g =
        NormedSpace.exp (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)} := by
    intro u hu
    have hu' : ∀ a b, ‖(sMat a₀ u - 1) a b‖ < ε := hu
    set z := (UpqT.mat u).det with hzdef
    have hz1 : ‖z‖ = 1 := norm_det_mat u
    have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz1; exact zero_ne_one hz1
    set θ := z.arg with hθ
    set k : ℤ := round (θ / ε) with hk
    have hround := abs_sub_round (θ / ε)
    rw [← hk] at hround
    have hθπ := Complex.abs_arg_le_pi z
    rw [← hθ] at hθπ
    have hkK : k ∈ Finset.Icc (-K) K := by
      have h1 : |(k : ℝ)| ≤ 4 / ε := by
        have a1 : |(k : ℝ)| ≤ |θ / ε| + 1 / 2 := by
          have := abs_sub_abs_le_abs_sub (k : ℝ) (θ / ε)
          rw [abs_sub_comm] at this; linarith
        have a2 : |θ / ε| ≤ Real.pi / ε := by
          rw [abs_div, abs_of_pos hε]; exact div_le_div_of_nonneg_right hθπ hε.le
        have a3 : Real.pi / ε + 1 / 2 ≤ 4 / ε := by
          rw [div_add' _ _ _ hε.ne', div_le_div_iff_of_pos_right hε]
          linarith [Real.pi_lt_d2]
        linarith
      have h2 : (4 / ε : ℝ) ≤ (K : ℝ) := Int.le_ceil _
      rw [Finset.mem_Icc]
      constructor
      · have : -(K : ℝ) ≤ (k : ℝ) := by linarith [neg_abs_le (k : ℝ)]
        exact_mod_cast this
      · have : (k : ℝ) ≤ (K : ℝ) := by linarith [le_abs_self (k : ℝ)]
        exact_mod_cast this
    rw [Set.mem_iUnion₂]
    refine ⟨k, hkK, ?_⟩
    show ∃ X ∈ ballU p q ρ, UpqT.mat (d k * u) =
      NormedSpace.exp (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    set c : ℂ := Complex.exp (((-((k : ℝ) * ε)) : ℝ) * Complex.I) with hcdef
    have hc1 : ‖c‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have hcz : ‖c * z - 1‖ ≤ ε := by
      have ez : z = Complex.exp ((θ : ℂ) * Complex.I) := by
        have := Complex.norm_mul_exp_arg_mul_I z
        rw [hz1, Complex.ofReal_one, one_mul] at this
        exact this.symm
      have e : c * z = Complex.exp (Complex.I * ((θ - (k : ℝ) * ε : ℝ) : ℂ)) := by
        rw [hcdef, ez, ← Complex.exp_add]; congr 1; push_cast; ring
      rw [e]
      refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
      rw [Real.norm_eq_abs]
      have e2 : θ - (k : ℝ) * ε = ε * (θ / ε - k) := by field_simp
      rw [e2, abs_mul, abs_of_pos hε]
      nlinarith
    have hmat : UpqT.mat (d k * u) = dg a₀ c * UpqT.mat u := by
      rw [GlobalTheory.CartanInt.mat_mul, hd]
    have hent : ∀ a b, ‖(UpqT.mat (d k * u) - 1) a b‖ < 2 * ε := by
      intro a b
      rw [hmat, Matrix.sub_apply, dg, Matrix.diagonal_mul, mat_eq_sMat_mul a₀ u hz0 a b]
      exact entry_lt a₀ hc1 hz1 hcz (sMat a₀ u) hu' a b
    have hl1 : GlobalTheory.CartanInt.l1 (UpqT.mat (d k * u) - 1) ≤ 2 * n ^ 2 * ε := by
      unfold GlobalTheory.CartanInt.l1
      calc ∑ i, ∑ j, ‖(UpqT.mat (d k * u) - 1) i j‖ ≤ ∑ _i : Fin p ⊕ Fin q, ∑ _j : Fin p ⊕ Fin q, 2 * ε :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => (hent i j).le
        _ = 2 * n ^ 2 * ε := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul]
            rw [hn]; push_cast; ring
    obtain ⟨X, hX, hXl⟩ := hlog (d k * u) (hl1.trans_lt hερ)
    refine ⟨X, ?_, hX⟩
    show ∑ i, ∑ j, ‖(X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ < ρ
    have : GlobalTheory.CartanInt.l1 (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) < ρ := by
      rw [hρ]; nlinarith
    exact this

  have hK0 : 0 ≤ K := Int.ceil_nonneg (by positivity)
  have hcard : ((Finset.Icc (-K) K).card : ℝ) ≤ 9 / ε := by
    rw [Int.card_Icc, show K + 1 - -K = 2 * K + 1 by ring]
    have e : ((2 * K + 1).toNat : ℝ) = 2 * (K : ℝ) + 1 := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
    rw [e]
    have h1 : (K : ℝ) < 4 / ε + 1 := Int.ceil_lt_add_one _
    have h2 : 3 ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
    have h3 : 9 / ε = 2 * (4 / ε) + 1 / ε := by ring
    linarith
  calc m {u | ∀ a b, ‖(sMat a₀ u - 1) a b‖ < ε}
      ≤ ∑ k ∈ Finset.Icc (-K) K, m ((fun x => d k * x) ⁻¹' {g | ∃ X ∈ ballU p q ρ, UpqT.mat g =
          NormedSpace.exp (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)}) :=
        (measure_mono hcover).trans (measure_biUnion_finset_le _ _)
    _ = ((Finset.Icc (-K) K).card : ℝ≥0∞) * m {g | ∃ X ∈ ballU p q ρ, UpqT.mat g =
          NormedSpace.exp (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)} := by
        simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Finset.Icc (-K) K).card : ℝ≥0∞) * (2 * ENNReal.ofReal ((18 / 5 * ρ / n) ^ ((p + q) ^ 2))) :=
        by gcongr
    _ = ENNReal.ofReal (((Finset.Icc (-K) K).card : ℝ) * (2 * (18 / 5 * ρ / n) ^ ((p + q) ^ 2))) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast,
          ENNReal.ofReal_ofNat]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
        (num_le n ε _ ((p + q) ^ 2) hn1 (Nat.one_le_pow _ _ hpq) hε hcard)

end GlobalTheory.CovTop.VolUp.OneMeasure
