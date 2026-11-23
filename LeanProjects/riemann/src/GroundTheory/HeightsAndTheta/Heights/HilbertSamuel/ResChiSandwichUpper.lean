import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjectionBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStF
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ResChiSandwich

open MvPolynomial MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds
open scoped ComplexOrder Matrix

noncomputable section

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem trace_comb_le {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) {N r : ℕ}
    (f : Fin r → MvPolynomial (Ix κ) ℤ) (g : Fin r → MvPolynomial (Fin (D + 1)) ℤ)
    (hf : ∀ k, (f k).IsHomogeneous N) (hg : ∀ k, (g k).IsHomogeneous N)
    (htr : ∀ k, aeval (x ∘ e) (g k) = secTrace x e N (aeval x (f k))) (c : Fin r → ℂ) {S : ℝ}
    (hS : ∀ z ∈ pts (coordIdeal ℤ x),
      ‖∑ k, c k * eval z (map (Int.castRingHom ℂ) (f k))‖ ≤ S * pnorm e z ^ N)
    (w : Fin (D + 1) → ℂ) :
    ‖∑ k, c k * eval w (map (Int.castRingHom ℂ) (g k))‖ ≤
      (projDeg x e : ℝ) * S * Real.sqrt (sqN w) ^ N := by
  classical
  obtain ⟨Δ, hΔ0, hΔ⟩ := exists_isDiscr hfr
  have hFc : Continuous fun w : Fin (D + 1) → ℂ => ‖∑ k, c k * eval w (map (Int.castRingHom ℂ) (g k))‖ :=
    (continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_eval _)).norm
  have hGc : Continuous fun w : Fin (D + 1) → ℂ => (projDeg x e : ℝ) * S * Real.sqrt (sqN w) ^ N := by
    unfold sqN
    fun_prop
  have hgood : ∀ w ∈ {w : Fin (D + 1) → ℂ | eval w Δ ≠ 0},
      w ∈ {w : Fin (D + 1) → ℂ | ‖∑ k, c k * eval w (map (Int.castRingHom ℂ) (g k))‖ ≤
        (projDeg x e : ℝ) * S * Real.sqrt (sqN w) ^ N} := by
    intro w hw
    obtain ⟨hfin, hcard, -, htrace⟩ := hΔ w hw
    simp only [Set.mem_ofPred_eq]
    have hsum : ∑ k, c k * eval w (map (Int.castRingHom ℂ) (g k)) =
        ∑ z ∈ hfin.toFinset, ∑ k, c k * eval z (map (Int.castRingHom ℂ) (f k)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [htrace N (f k) (g k) (hf k) (hg k) (htr k), finsum_mem_eq_finite_toFinset_sum _ hfin,
        Finset.mul_sum]
    rw [hsum]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ z ∈ hfin.toFinset,
        ‖∑ k, c k * eval z (map (Int.castRingHom ℂ) (f k))‖ ≤ S * Real.sqrt (sqN w) ^ N := by
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      have h := hS z hz.1
      have hw' : z ∘ e = w := funext hz.2
      rwa [pnorm_eq_sqN, hw'] at h
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin, hcard, mul_assoc]
  have hcl := closure_minimal hgood (isClosed_le hFc hGc)
  rw [(dense_eval_ne_zero hΔ0).closure_eq] at hcl
  exact hcl (Set.mem_univ w)

theorem quad_upper_pull {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) (hFS : IsPullFS x e m)
    {n k r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ} (hb : IsSecBasis x n b)
    (H : Fin (projDeg x e) → MvPolynomial (Ix κ) ℤ) (hH : ∀ l, (H l).IsHomogeneous k)
    (g : Fin r → Fin (projDeg x e) → MvPolynomial (Fin (D + 1)) ℤ)
    (hgh : ∀ j l, (g j l).IsHomogeneous (n + k))
    (hgv : ∀ j l, aeval (x ∘ e) (g j l) = secTrace x e (n + k) (aeval x (b j) * aeval x (H l)))
    {Cε : ℝ} (hCε : ∀ l, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ Cε * m.ρ z ^ k)
    {B : ℝ} (hB : 0 ≤ B) (hsup : ∀ c : Fin r → ℂ, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖∑ j, c j * secFun (b j) z‖ ^ 2 * wgt m n z ≤ B * bNormSq μ (fun j => secFun (b j)) (wgt m n) c)
    (c : Fin r → ℂ) :
    (star c ⬝ᵥ (((traceMat D (n + k) g).map (Int.cast : ℤ → ℂ))ᴴ * monoDiag D (n + k) (projDeg x e) *
      (traceMat D (n + k) g).map (Int.cast : ℤ → ℂ)) *ᵥ c).re ≤
      (projDeg x e : ℝ) ^ 3 * Cε ^ 2 * B * bNormSq μ (fun j => secFun (b j)) (wgt m n) c := by
  classical
  choose F hFh hFb using hb.1
  set β := bNormSq μ (fun j => secFun (b j)) (wgt m n) c with hβ
  have hβ0 : 0 ≤ β := bNormSq_nonneg' μ m _ c
  set S := Cε * Real.sqrt (B * β) with hSdef
  have hl : ∀ l, ∫ w, ‖∑ j, c j * eval w (map (Int.castRingHom ℂ) (g j l))‖ ^ 2 ∂(sphProb (D + 1)) ≤
      ((projDeg x e : ℝ) * S) ^ 2 := by
    intro l
    have htr : ∀ j, aeval (x ∘ e) (g j l) = secTrace x e (n + k) (aeval x (F j * H l)) := fun j => by
      rw [hgv, map_mul, hFb j, aeval_map_intQ]
    have hS : ∀ z ∈ pts (coordIdeal ℤ x),
        ‖∑ j, c j * eval z (map (Int.castRingHom ℂ) (F j * H l))‖ ≤ S * pnorm e z ^ (n + k) := by
      intro z hz
      have hmz : m.ρ z = pnorm e z := hFS z hz
      have e1 : ∑ j, c j * eval z (map (Int.castRingHom ℂ) (F j * H l)) =
          (∑ j, c j * secFun (b j) z) * eval z (map (Int.castRingHom ℂ) (H l)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, map_mul, hFb j, secFun_map_intQ]; ring
      rw [e1, norm_mul, hSdef, pow_add, ← hmz]
      have h1 := norm_le_of_sq_wgt_le hz.1 (norm_nonneg _) (mul_nonneg hB hβ0) (hsup c z hz)
      have h2 := hCε l z hz
      calc ‖∑ j, c j * secFun (b j) z‖ * ‖eval z (map (Int.castRingHom ℂ) (H l))‖
          ≤ (Real.sqrt (B * β) * m.ρ z ^ n) * (Cε * m.ρ z ^ k) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by have := m.nonneg z; positivity)
        _ = Cε * Real.sqrt (B * β) * (m.ρ z ^ n * m.ρ z ^ k) := by ring
    refine integral_sphProb_le _ (fun w => sq_nonneg _) fun w hw => ?_
    have ht := trace_comb_le hfr (fun j => F j * H l) (fun j => g j l)
      (fun j => (hFh j).mul (hH l)) (fun j => hgh j l) htr c hS w
    rw [hw, Real.sqrt_one, one_pow, mul_one] at ht
    exact pow_le_pow_left₀ (norm_nonneg _) ht 2
  rw [quad_conj, quad_monoDiag]
  simp_rw [sum_monoNormSq_traceMat g hgh c]
  calc ∑ l : Fin (projDeg x e), ∫ w, ‖∑ j, c j * eval w (map (Int.castRingHom ℂ) (g j l))‖ ^ 2 ∂(sphProb (D + 1))
      ≤ ∑ _l : Fin (projDeg x e), ((projDeg x e : ℝ) * S) ^ 2 := Finset.sum_le_sum fun l _ => hl l
    _ = (projDeg x e : ℝ) ^ 3 * Cε ^ 2 * B * β := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hSdef, mul_pow, mul_pow,
        Real.sq_sqrt (mul_nonneg hB hβ0)]
      ring

theorem upper {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) (hFS : IsPullFS x e m)
    (hint : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b → ∀ i j,
      Integrable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt m n z : ℂ)) μ)
    (hpd : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b →
      (bGram μ (fun k => secFun (b k)) (wgt m n)).PosDef)
    (hsup : ∃ K : ℝ, ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), 1 ≤ n → IsSecBasis x n b →
      ∀ (c : Fin r → ℂ), ∀ z ∈ pts (coordIdeal ℤ x),
        ‖∑ k, c k * secFun (b k) z‖ ^ 2 * wgt m n z ≤
          K * (n : ℝ) ^ D * bNormSq μ (fun k => secFun (b k)) (wgt m n) c) :
    ∃ (k : ℕ) (C : ℝ), ∀ n : ℕ, 1 ≤ n → ∀ (r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b →
      -(1 / 2) * Real.log (bGram μ (fun j => secFun (b j)) (wgt m n)).det.re ≤
        (projDeg x e : ℝ) * chiP D (n + k) + C * (n : ℝ) ^ D * Real.log (n + 1) := by
  classical
  have hrat := hfr.isRatProjFrame
  obtain ⟨k, ε, hε, hli⟩ := exists_indep_sections x e hrat
  have hεH : ∀ l, ∃ Hl : MvPolynomial (Ix κ) ℤ, Hl.IsHomogeneous k ∧ aeval x Hl = ε l := fun l => by
    obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.mp (hε l)
    exact ⟨p, (mem_homogeneousSubmodule _ _).mp hp, hpe⟩
  choose H hHh hHe using hεH
  have hHe' : (fun l => aeval x (H l)) = ε := funext hHe
  have hCl : ∀ l, ∃ S : ℝ, 0 ≤ S ∧ ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ S * pnorm e z ^ k :=
    fun l => form_le_pnorm hfr k _ ((hHh l).map _)
  choose Cl _ hCl using hCl
  set Cε := ∑ l, |Cl l| with hCεdef
  have hCε : ∀ l, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ Cε * m.ρ z ^ k := fun l z hz => by
    have hmz : m.ρ z = pnorm e z := hFS z hz
    rw [hmz]
    exact (hCl l z hz).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Cl i|) (fun i _ => abs_nonneg _) (Finset.mem_univ l)))
      (pow_nonneg (pnorm_nonneg e z) _))
  obtain ⟨K, hK⟩ := hsup
  obtain ⟨k', hk'⟩ := finrank_sec_le x e hfr
  set T : ℝ := max 1 ((projDeg x e : ℝ) ^ 3 * Cε ^ 2 * |K|) with hTdef
  have hT1 : 1 ≤ T := le_max_left _ _
  refine ⟨k, (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * ((1 / 2) * (Real.log T / Real.log 2 + D)),
    fun n hn r b hb => ?_⟩
  obtain rfl := hb.card_eq
  choose F hFh hFb using hb.1
  have hbF : ∀ j, aeval x (b j) = aeval x (F j) := fun j => by rw [hFb j, aeval_map_intQ]
  have hgex : ∀ j l, ∃ p : MvPolynomial (Fin (D + 1)) ℤ, p.IsHomogeneous (n + k) ∧
      aeval (x ∘ e) p = secTrace x e (n + k) (aeval x (b j) * aeval x (H l)) := fun j l => by
    have hmem : aeval x (b j) * aeval x (H l) ∈ sec ℤ x (n + k) := by
      rw [hbF j, ← map_mul]
      exact Submodule.mem_map.mpr ⟨F j * H l, (mem_homogeneousSubmodule _ _).mpr ((hFh j).mul (hHh l)), rfl⟩
    obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.mp (secTrace_mem x e hfr (n + k) hmem)
    exact ⟨p, (mem_homogeneousSubmodule _ _).mp hp, hpe⟩
  choose g hgh hgv using hgex
  have hinj := traceMat_injective hrat hb H hHh (by rw [hHe']; exact hli) g hgh hgv
  have hr := le_of_injective_mulVec _ hinj
  have hG' := hpd n _ b hb
  have hG := monoDiag_posDef D (n + k) (projDeg x e)
  set A := Real.sqrt (T * (n : ℝ) ^ D) with hAdef
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hTn : 1 ≤ T * (n : ℝ) ^ D := one_le_mul_of_one_le_of_one_le hT1 (one_le_pow₀ hn1)
  have hA : 0 < A := Real.sqrt_pos.mpr (by linarith)
  have hA2 : A ^ 2 = T * (n : ℝ) ^ D := Real.sq_sqrt (by linarith)
  have hnorm : (((A : ℂ) ^ 2) • bGram μ (fun j => secFun (b j)) (wgt m n) -
      ((traceMat D (n + k) g).map (Int.cast : ℤ → ℂ))ᴴ * monoDiag D (n + k) (projDeg x e) *
        (traceMat D (n + k) g).map (Int.cast : ℤ → ℂ)).PosSemidef := by
    refine psd_sub_of_quad_le (isHermitian_sq_smul hG'.isHermitian A)
      (Matrix.isHermitian_conjTranspose_mul_mul _ hG.isHermitian) fun c => ?_
    have hq := quad_upper_pull hfr hFS hb H hHh g hgh hgv hCε (mul_nonneg (abs_nonneg K)
      (pow_nonneg (Nat.cast_nonneg n) D)) (fun c z hz => (hK n _ b hn hb c z hz).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K)
          (pow_nonneg (Nat.cast_nonneg n) D)) (bNormSq_nonneg' μ m _ c))) c
    have hβ0 := bNormSq_nonneg' μ m (n := n) (fun j => secFun (b j)) c
    have hre : (star c ⬝ᵥ (((A : ℂ) ^ 2) • bGram μ (fun j => secFun (b j)) (wgt m n)) *ᵥ c).re =
        A ^ 2 * bNormSq μ (fun j => secFun (b j)) (wgt m n) c := by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
        bNormSq_eq_re μ _ _ (hint n _ b hb)]
    rw [hre, hA2]
    refine hq.trans (mul_le_mul_of_nonneg_right ?_ hβ0)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (Nat.cast_nonneg n) D)
  have hsmall : ∀ i, ((((1 : Matrix (Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n + k)).card))
      (Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n + k)).card)) ℤ).map (Int.cast : ℤ → ℂ))ᴴ *
      monoDiag D (n + k) (projDeg x e) *
      (1 : Matrix (Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n + k)).card))
      (Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n + k)).card)) ℤ).map (Int.cast : ℤ → ℂ)) i i).re
      ≤ (1 : ℝ) ^ 2 := by
    intro i
    rw [Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one, monoDiag, Matrix.diagonal_apply_eq, Complex.ofReal_re, one_pow]
    exact monoNormSq_le_one _
  have key := neg_log_det_le hr hG' hG _ hinj 1 (by simp) hA one_pos hnorm hsmall
  rw [Real.log_one, mul_zero, add_zero, neg_log_det_monoDiag] at key
  obtain ⟨hL0, hL⟩ := log_sqrt_bound D hT1 hn
  have hrb : ((finrank ℤ (sec ℤ x n) : ℕ) : ℝ) ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by
    have h1 : ((finrank ℤ (sec ℤ x n) : ℕ) : ℝ) ≤ (projDeg x e : ℝ) * (((n + k' + D).choose D : ℕ) : ℝ) := by
      exact_mod_cast hk' n
    rw [mul_assoc]
    exact h1.trans (mul_le_mul_of_nonneg_left (choose_bound k' D hn) (Nat.cast_nonneg _))
  have hX : 0 ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by positivity
  have h3 : ((finrank ℤ (sec ℤ x n) : ℕ) : ℝ) * Real.log A ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D *
      ((1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1)) :=
    (mul_le_mul_of_nonneg_right hrb hL0).trans (mul_le_mul_of_nonneg_left hL hX)
  have h4 : (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D *
      ((1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1)) =
      (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * ((1 / 2) * (Real.log T / Real.log 2 + D)) *
        (n : ℝ) ^ D * Real.log (n + 1) := by ring
  linarith

end

end ResChiSandwich

end GroundTheory.Heights₂.Heights.HilbertSamuel
