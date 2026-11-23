import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPosGramFormIntegralLatticeProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashUnnormalizedConstMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.SlashAddSmulPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.DualLatticeIndexEqDiscrPowMulDetPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSeriesTranslationTwistsCoefficients
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsFiniteRepsScaledLatticeCardNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertThetaSeriesPeriodicInversionFormula
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.LatticeGaussSumTwistDualEqIndicator
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.LatticeNormalizedGaussSumEighthRoot

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.ThetaLevel

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem pos_toInf {γ : GL (Fin 2) F} (h : γ.val.det = 1) : Pos (toInf γ) := by
  intro v
  have e : (↑(toInf γ) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det = rhom γ.val.det := by
    rw [RingHom.map_det]
    rfl
  rw [e, h, map_one]
  exact one_pos

def low (x : F) : GL (Fin 2) F where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem natCast_int (N : ℕ) : IsIntegral ℤ (N : F) := by
  exact isIntegral_natCast N

theorem decomp (γ : GL (Fin 2) F) (hdet : γ.val.det = 1) (hc : γ.val 1 0 ≠ 0) :
    γ = aff 1 (γ.val 0 0 / γ.val 1 0) * wm (Units.mk0 _ hc) * aff 1 (γ.val 1 1 / γ.val 1 0) := by
  have had : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = 1 := by rw [← hdet, Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, wm, Matrix.mul_apply, Fin.sum_univ_succ] <;> field_simp <;> linear_combination (-1 : F) * had

private theorem sl0_mul_of_pos (k : ℕ) (g h : GL (Fin 2) (InfinitePlace F → ℝ)) (hh : Pos h)
    (f : Hn F → ℂ) : sl0 k (g * h) f = sl0 k h (sl0 k g f) := by
  funext z
  simp only [sl0]
  have hact : act (g * h) z = act g (act h z) := by
    funext v
    simp only [act, map_mul, mul_smul]
  have hden : ∀ v, UpperHalfPlane.denom (cmp v (g * h)) (z v) =
      UpperHalfPlane.denom (cmp v g) (act h z v) * UpperHalfPlane.denom (cmp v h) (z v) := by
    intro v
    have hpos : 0 < ((cmp v h).det : ℝ) := by
      have e : ((cmp v h).det : ℝ) =
          (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v := by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two]
        simp [cmp]
      rw [e]
      exact hh v
    rw [map_mul, UpperHalfPlane.denom_cocycle_σ]
    simp only [UpperHalfPlane.σ, if_pos hpos, ContinuousAlgEquiv.refl_apply]
    rfl
  rw [hact, Finset.prod_congr rfl (fun v _ => hden v), Finset.prod_mul_distrib, mul_inv, mul_pow]
  ring

private theorem sl0_smul (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (ζ : ℂ)
    (f : Hn F → ℂ) : sl0 k h (ζ • f) = ζ • sl0 k h f := by
  funext z
  simp only [sl0, Pi.smul_apply, smul_eq_mul]
  ring

theorem main_abcd {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) (hG : EvenPos G) (t : ℕ)
    (ht : G.det = (t : ℤ) ^ 2) (k : ℕ) (hk : Fintype.card κ = 2 * k) (N : ℕ) (hN0 : 0 < N)
    (hN : ∀ y ∈ dualL F G, (N : F) • y ∈ LL F κ ∧ IsIntegral ℤ ((N : F) * QF G y))
    (a b c d : F) (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b) (hcN : IsIntegral ℤ (c / N)) (hd : IsIntegral ℤ d)
    (had : a * d - b * c = 1) (hc : c ≠ 0) :
    ∃ ζ : ℂ, ζ ^ 8 = 1 ∧
      sl0 k (toInf (aff 1 (a / c) * wm (Units.mk0 c hc) * aff 1 (d / c))) (th G oneL) = ζ • th G oneL := by
  have hNF : (N : F) ≠ 0 := by exact_mod_cast hN0.ne'
  have hcI : IsIntegral ℤ c := by
    have h1 := (natCast_int (F := F) N).mul hcN
    rwa [mul_div_cancel₀ _ hNF] at h1
  obtain ⟨T, hT, -, hTle, -⟩ := GlobalTheory.T.exists_finite_reps_scaled_lattice_card_norm F κ c 1 hc one_ne_zero (by rwa [div_one])
  obtain ⟨hsymm, hsc, -, hint, hLL, haL, het, hLd⟩ := GlobalTheory.T.evenPos_gramForm_integral_lattice_properties F κ G hG
  have hsupp : ∀ x : κ → F, (fun x => oneL x * et (a / c * QF G x)) x ≠ 0 → x ∈ aL κ (1 : F) := by
    intro x hx
    have hxL : x ∈ LL F κ := by
      by_contra hn
      apply hx
      simp [oneL, hn]
    exact (haL 1 x).2 ⟨x, hxL, (one_smul F x).symm⟩
  have hper : ∀ x l : κ → F, l ∈ aL κ c →
      (fun x => oneL x * et (a / c * QF G x)) (x + l) = (fun x => oneL x * et (a / c * QF G x)) x := by
    intro x l hl
    obtain ⟨m, hm, rfl⟩ := (haL c l).1 hl
    have hcm : c • m ∈ LL F κ := by
      rw [hLL]
      intro i
      rw [Pi.smul_apply, smul_eq_mul]
      exact hcI.mul ((hLL m).1 hm i)
    by_cases hx : x ∈ LL F κ
    · have hxl : x + c • m ∈ LL F κ := add_mem hx hcm
      simp only [oneL, if_pos hx, if_pos hxl, one_mul]
      rw [(hsymm x (c • m)).2, (hsymm x (c • m)).1, (hsc c m x).1, (hsc c m x).2.1]
      have e : a / c * (QF G x + c * BF G m x + c ^ 2 * QF G m) =
          a / c * QF G x + (a * BF G m x + a * c * QF G m) := by
        field_simp
        ring
      have hi : IsIntegral ℤ (a * BF G m x + a * c * QF G m) :=
        (ha.mul ((hint m hm).2 x hx)).add ((ha.mul hcI).mul (hint m hm).1)
      rw [e, (het (a / c * QF G x) (a * BF G m x + a * c * QF G m)).1,
        (het (a * BF G m x + a * c * QF G m) 0).2.2.2 hi, mul_one]
    · have hxl : x + c • m ∉ LL F κ := by
        intro h
        apply hx
        simpa using sub_mem h hcm
      simp [oneL, hx, hxl]
  have hW' := GlobalTheory.T.hilbertThetaSeries_periodic_inversion_formula F κ G hG t ht k hk c 1 (Units.mk0 c hc) T
    (fun x => oneL x * et (a / c * QF G x)) hc one_ne_zero hTle hT hsupp hper
  have hW : Pos (toInf (wm (Units.mk0 c hc))) := pos_toInf (by simp [wm, Matrix.det_fin_two, hc])
  have hB : Pos (toInf (aff 1 (d / c))) := pos_toInf (by simp [aff, Matrix.det_fin_two])
  rw [map_mul, sl0_mul_of_pos _ _ _ hB, map_mul, sl0_mul_of_pos _ _ _ hW, GlobalTheory.T.thetaSeries_translation_twists_coefficients, hW',
    GlobalTheory.T.thetaSeries_translation_twists_coefficients]
  refine ⟨wC k t c c * ∑ x ∈ T, et (a / c * QF G x),
    GlobalTheory.T.lattice_normalized_gaussSum_eighth_root F κ G hG t ht k hk N a b c d T hN0 hN ha hb hcN hd had hc hT, ?_⟩
  funext z
  simp only [th, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  congr 1
  funext y
  have key : wT G k t c (↑(Units.mk0 c hc)) T (fun x => oneL x * et (a / c * QF G x)) y *
      et (d / c * QF G y) = wC k t c c * (∑ x ∈ T, et (a / c * QF G x)) * oneL y := by
    have hcc : (c / c) • y = y := by rw [div_self hc, one_smul]
    by_cases hy : y ∈ dualL F G
    · have hsum : ∑ x ∈ T, oneL x * et (a / c * QF G x) * et (BF G y x / c) =
          ∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxL : x ∈ LL F κ := by
          obtain ⟨l, hl, hxl⟩ := (haL 1 x).1 (hT.1 x hx)
          rw [hxl, one_smul]
          exact hl
        simp [oneL, hxL]
      have h62 := GlobalTheory.T.lattice_gaussSum_twist_dual_eq_indicator F κ G hG N a b c d T hN0 hN ha hb hcN hd had hc hT y hy
      simp only [wT, Units.val_mk0, hcc, hy, ↓reduceIte]
      rw [hsum, mul_assoc, h62]
      ring
    · have hyL : y ∉ LL F κ := fun h => hy (hLd h)
      simp only [wT, Units.val_mk0, hcc, hy, ↓reduceIte, oneL, hyL]
      ring
  rw [key]
  ring

theorem main_ne {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) (hG : EvenPos G) (t : ℕ)
    (ht : G.det = (t : ℤ) ^ 2) (k : ℕ) (hk : Fintype.card κ = 2 * k) (N : ℕ) (hN0 : 0 < N)
    (hN : ∀ y ∈ dualL F G, (N : F) • y ∈ LL F κ ∧ IsIntegral ℤ ((N : F) * QF G y))
    (γ : GL (Fin 2) F) (hγ : InGam N γ) (hc : γ.val 1 0 ≠ 0) :
    ∃ ζ : ℂ, ζ ^ 8 = 1 ∧ sl0 k (toInf γ) (th G oneL) = ζ • th G oneL := by
  obtain ⟨hdet, ha, hb, hcN, hd⟩ := hγ
  have had : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact hdet
  rw [decomp γ hdet hc]
  exact main_abcd G hG t ht k hk N hN0 hN _ _ _ _ ha hb hcN hd had hc

theorem low_inGam (N : ℕ) (hN0 : 0 < N) : InGam N (low (-(N : F))) := by
  have hNF : (N : F) ≠ 0 := by exact_mod_cast hN0.ne'
  refine ⟨by simp [low, Matrix.det_fin_two], by simp [low, isIntegral_one], by simp [low, isIntegral_zero], ?_, by simp [low, isIntegral_one]⟩
  have : (low (-(N : F))).val 1 0 / N = -1 := by simp [low, hNF]
  rw [this]; exact isIntegral_one.neg

end GlobalTheory.HilbertThetaSeries.ThetaLevel

open GlobalTheory.HilbertThetaSeries.ThetaLevel in

theorem GlobalTheory.HilbertThetaSeries.theta_level_eighth_root : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∃ N : ℕ, 0 < N ∧ ∀ γ : GL (Fin 2) F, InGam N γ → ∃ ζ : ℂ, ζ ^ 8 = 1 ∧ sl0 k (toInf γ) (th G oneL) = ζ • th G oneL := by
  intro F _ _ _ κ _ _ G hG t ht k hk
  obtain ⟨N, hN0, hN⟩ := (GlobalTheory.T.dualLattice_index_eq_discr_pow_mul_det_pow F κ G hG).2.1
  refine ⟨N, hN0, fun γ hγ => ?_⟩
  by_cases hc : γ.val 1 0 = 0
  · have hNF : (N : F) ≠ 0 := by exact_mod_cast hN0.ne'
    obtain ⟨hdet, ha, hb, hcN, hd⟩ := hγ
    have hdet' : γ.val 0 0 * γ.val 1 1 = 1 := by
      rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
      exact hdet
    have hd0 : γ.val 1 1 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hdet'
      exact zero_ne_one hdet'
    have hNI : IsIntegral ℤ (N : F) := natCast_int N
    have e3 : ∀ i j, (γ * low (N : F)).val i j =
        γ.val i 0 * (low (N : F)).val 0 j + γ.val i 1 * (low (N : F)).val 1 j := by
      intro i j
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hγ3 : InGam N (γ * low (N : F)) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [Units.val_mul, Matrix.det_mul, hdet]
        simp [low, Matrix.det_fin_two]
      · rw [e3]
        simp only [low, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, mul_one]
        exact ha.add (hb.mul hNI)
      · rw [e3]
        simpa [low] using hb
      · rw [e3]
        simp only [low, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, mul_one, hc, zero_mul, zero_add]
        rw [mul_div_cancel_right₀ _ hNF]
        exact hd
      · rw [e3]
        simpa [low, hc] using hd
    have hc3 : (γ * low (N : F)).val 1 0 ≠ 0 := by
      rw [e3]
      simpa [low, hc] using mul_ne_zero hd0 hNF
    have hlow : (low (-(N : F))).val 1 0 ≠ 0 := by
      simpa [low] using hNF
    obtain ⟨ζ1, h1, e1⟩ := main_ne G hG t ht k hk N hN0 hN _ hγ3 hc3
    obtain ⟨ζ2, h2, e2⟩ := main_ne G hG t ht k hk N hN0 hN _ (low_inGam N hN0) hlow
    have hγe : γ = γ * low (N : F) * low (-(N : F)) := by
      rw [mul_assoc]
      conv_lhs => rw [← mul_one γ]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [low, Matrix.mul_apply, Fin.sum_univ_succ]
    have hP : Pos (toInf (low (-(N : F)))) := pos_toInf (by simp [low, Matrix.det_fin_two])
    refine ⟨ζ1 * ζ2, by rw [mul_pow, h1, h2, one_mul], ?_⟩
    rw [hγe, map_mul, sl0_mul_of_pos _ _ _ hP, e1, sl0_smul, e2, smul_smul]
  · exact main_ne G hG t ht k hk N hN0 hN γ hγ hc

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_slash_eighth_root_of_square_det : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∃ N : ℕ, 0 < N ∧ ∀ γ : GL (Fin 2) F, InGam N γ → ∃ ζ : ℂ, ζ ^ 8 = 1 ∧ sl0 k (toInf γ) (th G oneL) = ζ • th G oneL := by
  first | exact @GlobalTheory.HilbertThetaSeries.theta_level_eighth_root | exact GlobalTheory.HilbertThetaSeries.theta_level_eighth_root | (intros; apply GlobalTheory.HilbertThetaSeries.theta_level_eighth_root <;> assumption)
