import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivative
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.HaarSmallBall

variable {n : ℕ} {ε : Fin n → Bool}

lemma toMK_mem_unitary (k : Formalism.REAL.KG ε) : toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  ((Formalism.REAL.mem_KG ε (k : Formalism.REAL.UJ ε)).1 k.2).1

lemma toMK_mul' (a b : Formalism.REAL.KG ε) : toMK (a * b) = toMK a * toMK b := rfl

lemma toMK_inv'' (k : Formalism.REAL.KG ε) : toMK k⁻¹ = star (toMK k) := by
  show ((((k : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    Matrix (Fin n) (Fin n) ℂ) = _
  exact Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem (toMK_mem_unitary k))

lemma norm_entry_le_one (k : Formalism.REAL.KG ε) (i j : Fin n) : ‖toMK k i j‖ ≤ 1 :=
  entry_norm_bound_of_unitary (toMK_mem_unitary k) i j

lemma hs_translate_le (a b : Formalism.REAL.KG ε) (η : ℝ)
    (hη : ∀ i j, ‖toMK b i j - toMK a i j‖ ≤ η) :
    Formalism.REAL.hs (toMK (a⁻¹ * b) - 1) ≤ (n : ℝ) * n * ((n : ℝ) * η) ^ 2 := by
  have hA : star (toMK a) * toMK a = 1 := Unitary.star_mul_self_of_mem (toMK_mem_unitary a)
  have heq : toMK (a⁻¹ * b) - 1 = star (toMK a) * (toMK b - toMK a) := by
    rw [toMK_mul', toMK_inv'', Matrix.mul_sub, hA]
  rw [heq]
  have hent : ∀ i j, ‖(star (toMK a) * (toMK b - toMK a)) i j‖ ≤ (n : ℝ) * η := by
    intro i j
    rw [Matrix.mul_apply]
    calc ‖∑ l, star (toMK a) i l * (toMK b - toMK a) l j‖
        ≤ ∑ l, ‖star (toMK a) i l * (toMK b - toMK a) l j‖ := norm_sum_le _ _
      _ ≤ ∑ _l : Fin n, η := by
          apply Finset.sum_le_sum
          intro l _
          rw [norm_mul, Matrix.star_apply, norm_star, Matrix.sub_apply]
          calc ‖toMK a l i‖ * ‖toMK b l j - toMK a l j‖ ≤ 1 * η :=
                mul_le_mul (norm_entry_le_one a l i) (hη l j) (norm_nonneg _) zero_le_one
            _ = η := one_mul η
      _ = (n : ℝ) * η := by simp
  unfold Formalism.REAL.hs
  calc ∑ i, ∑ j, ‖(star (toMK a) * (toMK b - toMK a)) i j‖ ^ 2
      ≤ ∑ _i : Fin n, ∑ _j : Fin n, ((n : ℝ) * η) ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact pow_le_pow_left₀ (norm_nonneg _) (hent i j) 2
    _ = (n : ℝ) * n * ((n : ℝ) * η) ^ 2 := by simp [Finset.sum_const]; ring

noncomputable def cell (h x : ℝ) : Fin (⌊2 / h⌋₊ + 1) :=
  ⟨min ⌊(x + 1) / h⌋₊ ⌊2 / h⌋₊, Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma abs_sub_lt_of_cell_eq {h x y : ℝ} (hh : 0 < h) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hc : cell h x = cell h y) : |x - y| < h := by
  have hx' := abs_le.1 hx
  have hy' := abs_le.1 hy
  have ha0 : 0 ≤ (x + 1) / h := div_nonneg (by linarith) hh.le
  have hb0 : 0 ≤ (y + 1) / h := div_nonneg (by linarith) hh.le
  have hfa : ⌊(x + 1) / h⌋₊ ≤ ⌊2 / h⌋₊ :=
    Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hh.le)
  have hfb : ⌊(y + 1) / h⌋₊ ≤ ⌊2 / h⌋₊ :=
    Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hh.le)
  have hc' : ⌊(x + 1) / h⌋₊ = ⌊(y + 1) / h⌋₊ := by
    have := congrArg Fin.val hc
    simp only [cell, min_eq_left hfa, min_eq_left hfb] at this
    exact this
  have h1 := Nat.floor_le ha0
  have h2 := Nat.lt_floor_add_one ((x + 1) / h)
  have h3 := Nat.floor_le hb0
  have h4 := Nat.lt_floor_add_one ((y + 1) / h)
  rw [hc'] at h1 h2
  have hab : |(x + 1) / h - (y + 1) / h| < 1 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have : (x + 1) / h - (y + 1) / h = (x - y) / h := by ring
  rw [this, abs_div, abs_of_pos hh, div_lt_one hh] at hab
  exact hab

end GlobalTheory.HaarSmallBall

namespace GlobalTheory.HaarSmallBall

variable {n : ℕ} {ε : Fin n → Bool}

noncomputable def roundK (h : ℝ) (k : Formalism.REAL.KG ε) :
    Fin n → Fin n → Fin (⌊2 / h⌋₊ + 1) × Fin (⌊2 / h⌋₊ + 1) :=
  fun i j => (cell h (toMK k i j).re, cell h (toMK k i j).im)

lemma norm_sub_lt_of_round_eq {h : ℝ} (hh : 0 < h) {a b : Formalism.REAL.KG ε}
    (hab : roundK h b = roundK h a) (i j : Fin n) : ‖toMK b i j - toMK a i j‖ ≤ 2 * h := by
  have e := congrFun (congrFun hab i) j
  simp only [roundK, Prod.mk.injEq] at e
  have hre := abs_sub_lt_of_cell_eq hh ((Complex.abs_re_le_norm _).trans (norm_entry_le_one b i j))
    ((Complex.abs_re_le_norm _).trans (norm_entry_le_one a i j)) e.1
  have him := abs_sub_lt_of_cell_eq hh ((Complex.abs_im_le_norm _).trans (norm_entry_le_one b i j))
    ((Complex.abs_im_le_norm _).trans (norm_entry_le_one a i j)) e.2
  calc ‖toMK b i j - toMK a i j‖ ≤ |(toMK b i j - toMK a i j).re| + |(toMK b i j - toMK a i j).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * h := by rw [Complex.sub_re, Complex.sub_im]; linarith

theorem smallBall : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧ ∃ D : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → c * δ ^ D ≤ (muK ε {k | Formalism.REAL.hs (toMK k - 1) ≤ δ}).toReal := by
  intro n ε
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, one_pos, 0, fun δ hδ _ => ?_⟩
    have hset : {k : Formalism.REAL.KG ε | Formalism.REAL.hs (toMK k - 1) ≤ δ} = Set.univ := by
      ext k; simp [Formalism.REAL.hs, hδ.le]
    rw [hset, measure_univ]; simp
  set C : ℝ := 5 * (n : ℝ) ^ 2 with hC
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hCpos : 0 < C := by positivity
  refine ⟨(C ^ (2 * n * n))⁻¹, by positivity, 2 * n * n, fun δ hδ hδ1 => ?_⟩
  set h : ℝ := δ / (2 * (n : ℝ) ^ 2) with hhdef
  have hh : 0 < h := by positivity
  set B : Set (Formalism.REAL.KG ε) := {k | Formalism.REAL.hs (toMK k - 1) ≤ δ} with hB
  set m : ℕ := ⌊2 / h⌋₊ + 1 with hm
  let R : Formalism.REAL.KG ε → Fin n → Fin n → Fin m × Fin m := roundK (ε := ε) h

  have hfib : ∀ g, muK ε (R ⁻¹' {g}) ≤ muK ε B := by
    intro g
    by_cases hne : (R ⁻¹' {g}).Nonempty
    · obtain ⟨a, ha⟩ := hne
      calc muK ε (R ⁻¹' {g}) ≤ muK ε ((fun x => a⁻¹ * x) ⁻¹' B) := by
            apply measure_mono
            intro b hb
            have hab : R b = R a := by
              rw [Set.mem_preimage, Set.mem_singleton_iff] at ha hb; rw [ha, hb]
            show Formalism.REAL.hs (toMK (a⁻¹ * b) - 1) ≤ δ
            refine (hs_translate_le a b (2 * h) (norm_sub_lt_of_round_eq hh hab)).trans ?_
            have : (n : ℝ) * n * ((n : ℝ) * (2 * h)) ^ 2 = δ ^ 2 := by
              rw [hhdef]; field_simp
            rw [this]; nlinarith
        _ = muK ε B := measure_preimage_mul _ _ _
    · rw [Set.not_nonempty_iff_eq_empty.1 hne]; simp
  have hcov : (1 : ENNReal) ≤
      (Fintype.card (Fin n → Fin n → Fin m × Fin m) : ENNReal) * muK ε B := by
    calc (1 : ENNReal) = muK ε Set.univ := measure_univ.symm
      _ = muK ε (⋃ g, R ⁻¹' {g}) := by
          congr 1; ext k; simp
      _ ≤ ∑ g, muK ε (R ⁻¹' {g}) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _g : Fin n → Fin n → Fin m × Fin m, muK ε B := Finset.sum_le_sum fun g _ => hfib g
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hcard : (Fintype.card (Fin n → Fin n → Fin m × Fin m) : ℝ) = (m : ℝ) ^ (2 * n * n) := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
    push_cast; ring
  have hcovR : (1 : ℝ) ≤ (m : ℝ) ^ (2 * n * n) * (muK ε B).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_ne_top _ _)) hcov
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, hcard, ENNReal.toReal_one] at this
    exact this
  have hmδ : (m : ℝ) * δ ≤ C := by
    have hfl : ((⌊2 / h⌋₊ : ℕ) : ℝ) ≤ 2 / h := Nat.floor_le (by positivity)
    have h2h : 2 / h * δ = 4 * (n : ℝ) ^ 2 := by rw [hhdef]; field_simp; ring
    have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
    calc (m : ℝ) * δ = ((⌊2 / h⌋₊ : ℕ) : ℝ) * δ + δ := by rw [hm]; push_cast; ring
      _ ≤ 2 / h * δ + δ := by nlinarith
      _ ≤ C := by rw [h2h, hC]; nlinarith
  have hpow : ((m : ℝ) * δ) ^ (2 * n * n) ≤ C ^ (2 * n * n) :=
    pow_le_pow_left₀ (by positivity) hmδ _
  have hμ0 : 0 ≤ (muK ε B).toReal := ENNReal.toReal_nonneg
  rw [inv_mul_le_iff₀ (by positivity)]
  calc δ ^ (2 * n * n) ≤ δ ^ (2 * n * n) * ((m : ℝ) ^ (2 * n * n) * (muK ε B).toReal) :=
        le_mul_of_one_le_right (by positivity) hcovR
    _ = ((m : ℝ) * δ) ^ (2 * n * n) * (muK ε B).toReal := by rw [mul_pow]; ring
    _ ≤ C ^ (2 * n * n) * (muK ε B).toReal := mul_le_mul_of_nonneg_right hpow hμ0

end GlobalTheory.HaarSmallBall
