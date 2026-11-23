import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecPos
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecLog
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecMoments
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecSum
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecALogLower

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

def phiReal (ν : Fin n → ℝ) (x : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∏ i : Fin n, (lead ((i : ℕ) + 1) x).re ^ (-(ν i - nuNext ν i))

theorem phi_decay_core (ν : Fin n → ℝ) (hν : Antitone ν) {g : ℝ}
    (hg : ∀ a b : Fin n, ε a ≠ ε b → b < a → g ≤ ν b - ν a) (hq : 1 ≤ q0 ε) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : inP ε Y) :
    phiReal ν (NormedSpace.exp Y) ≤
      Real.exp (-(g / 8) * min (hs Y) (Real.sqrt (hs Y) / Real.sqrt (2 * q0 ε))) := by
  classical
  by_cases h0 : hs Y = 0
  · have hY0 : Y = 0 := by
      ext a b
      have hsum := (Finset.sum_eq_zero_iff_of_nonneg
        (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg ‖Y a b‖)).mp h0 a (Finset.mem_univ _)
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg ‖Y a b‖)).mp hsum b (Finset.mem_univ _)
      simpa using this
    subst hY0
    have hl : ∀ i : Fin n, lead ((i : ℕ) + 1) (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := fun i => by
      unfold lead
      rw [dif_pos (show (i : ℕ) + 1 ≤ n from i.isLt), Matrix.submatrix_one _ (Fin.castLE_injective _),
        Matrix.det_one]
    unfold phiReal
    rw [NormedSpace.exp_zero, h0]
    simp [hl]
  have hpos : 0 < hs Y := lt_of_le_of_ne (by unfold hs; positivity) (Ne.symm h0)
  obtain ⟨U, y, hU, hYe⟩ := decA_spec hY
  have hq' : (0 : ℝ) < 2 * q0 ε := by
    have : (1 : ℝ) ≤ q0 ε := by exact_mod_cast hq
    linarith
  set R := Real.sqrt (2 * q0 ε) * Real.sqrt (hs Y) with hRdef
  have hR : 0 < R := mul_pos (Real.sqrt_pos.mpr hq') (Real.sqrt_pos.mpr hpos)
  set t := min 1 (1 / R) with htdef
  have ht0 : 0 ≤ t := le_min zero_le_one (by positivity)
  set V : Fin n → ℝ := fun i =>
    ∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ‖Y a b‖ ^ 2 else 0 with hVdef
  have hx := exp_noncompactPart_posDef hY
  set c : Fin n → ℝ := fun i => (lead ((i : ℕ) + 1) (NormedSpace.exp Y)).re with hcdef
  have hc : ∀ i, 0 < c i := fun i => (lead_posDef hx _ i.isLt).1
  have hterm : ∀ i : Fin n, (ν i - nuNext ν i) * (t * V i / 4) ≤ (ν i - nuNext ν i) * Real.log (c i) := by
    intro i
    by_cases hlast : (i : ℕ) + 1 < n
    · have hnn : 0 ≤ ν i - nuNext ν i := by
        simp only [nuNext, dif_pos hlast]
        exact sub_nonneg.mpr (hν (show i ≤ ⟨(i : ℕ) + 1, hlast⟩ from Fin.le_def.mpr (by simp)))
      apply mul_le_mul_of_nonneg_left _ hnn
      have h := decA_log_lower hY hU hYe hq hpos ((i : ℕ) + 1) i.isLt
      simp only [Nat.lt_add_one_iff, Nat.add_one_le_iff] at h
      exact h
    · have hV : V i = 0 :=
        Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => if_neg (by have := a.isLt; omega)
      have hn : (i : ℕ) + 1 = n := by have := i.isLt; omega
      have hL : c i = 1 := by
        simp only [hcdef, hn]
        exact decA_lead_last hY hU hYe
      rw [hV, hL, Real.log_one]
      simp
  have hsum : t * (g * hs Y / 2) / 4 ≤ ∑ i, (ν i - nuNext ν i) * Real.log (c i) := by
    have hw := dec_weighted ν hν hg hY
    calc t * (g * hs Y / 2) / 4 ≤ t * (∑ i, (ν i - nuNext ν i) * V i) / 4 := by
          have := mul_le_mul_of_nonneg_left hw ht0
          linarith
      _ = ∑ i, (ν i - nuNext ν i) * (t * V i / 4) := by
          rw [Finset.mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => hterm i
  have hphi : phiReal ν (NormedSpace.exp Y) = Real.exp (-∑ i, (ν i - nuNext ν i) * Real.log (c i)) := by
    unfold phiReal
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.rpow_def_of_pos (hc i)]
    congr 1
    ring
  have hmin : t * hs Y = min (hs Y) (Real.sqrt (hs Y) / Real.sqrt (2 * q0 ε)) := by
    rw [htdef, min_mul_of_nonneg _ _ hpos.le, one_mul]
    congr 1
    have hs2 : hs Y = Real.sqrt (hs Y) * Real.sqrt (hs Y) := (Real.mul_self_sqrt hpos.le).symm
    have hsq : 0 < Real.sqrt (hs Y) := Real.sqrt_pos.mpr hpos
    have hsq2 : 0 < Real.sqrt (2 * q0 ε) := Real.sqrt_pos.mpr hq'
    rw [hRdef]
    field_simp
    nlinarith [Real.sq_sqrt hpos.le, Real.mul_self_sqrt hpos.le]
  rw [hphi]
  apply Real.exp_le_exp.mpr
  rw [← hmin]
  nlinarith [hsum]

private lemma posDef_exp_of_hermitian {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Yᴴ = Y) :
    (NormedSpace.exp Y).PosDef := by
  have hB : (NormedSpace.exp ((2 : ℂ)⁻¹ • Y))ᴴ = NormedSpace.exp ((2 : ℂ)⁻¹ • Y) := by
    rw [← Matrix.exp_conjTranspose]
    congr 1
    simp [hY]
  have hBB : NormedSpace.exp Y =
      (NormedSpace.exp ((2 : ℂ)⁻¹ • Y))ᴴ * 1 * NormedSpace.exp ((2 : ℂ)⁻¹ • Y) := by
    rw [hB, Matrix.mul_one, ← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul]
    norm_num
  rw [hBB]
  exact Matrix.PosDef.one.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_exp _))

private lemma lead_exp_pos_of_hermitian {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Yᴴ = Y) (i : Fin n) :
    0 < lead ((i : ℕ) + 1) (NormedSpace.exp Y) := by
  have hle : (i : ℕ) + 1 ≤ n := i.isLt
  rw [lead, dif_pos hle]
  exact ((posDef_exp_of_hermitian hY).submatrix (Fin.castLE_injective hle)).det_pos

theorem phiM_exp_le (μ : Fin n → ℤ) (hμ : IsMu lam μ) (hlam : IsHCParam lam) {h : ℝ}
    (hgap : GapAtLeast ε lam h) (hq : 1 ≤ q0 ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) :
    (PhiM μ (NormedSpace.exp Y)).re ≤
      Real.exp (-(h / 8) * min (hs Y) (Real.sqrt (hs Y) / Real.sqrt (2 * q0 ε))) := by
  have hYh : Yᴴ = Y := by
    obtain ⟨h1, h2⟩ := hY
    have h1' : Yᴴ * Jm ε + Jm ε * Y = 0 := h1
    have hJ : Jm ε * Jm ε = 1 := by
      rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      split_ifs <;> norm_num
    have h3 : Yᴴ * Jm ε = Y * Jm ε := by
      rw [h2]
      exact eq_neg_of_add_eq_zero_left h1'
    calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = Y * Jm ε * Jm ε := by rw [h3]
      _ = Y := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
  have hpos : ∀ i : Fin n, 0 < lead ((i : ℕ) + 1) (NormedSpace.exp Y) := fun i => lead_exp_pos_of_hermitian hYh i
  have hν : Antitone fun i => (μ i : ℝ) := by
    intro a b hab
    show (μ b : ℝ) ≤ μ a
    rw [hμ a, hμ b]
    have h1 := hlam.1.antitone hab
    have h2 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := Nat.cast_le.2 (Fin.le_def.1 hab)
    simp only [rho]
    linarith
  have hg : ∀ a b : Fin n, ε a ≠ ε b → b < a → h ≤ (μ b : ℝ) - μ a := by
    intro a b hne hba
    have h1 := hgap a b hne
    have h2 := hlam.1 hba
    rw [abs_of_neg (by linarith)] at h1
    rw [hμ a, hμ b]
    have h3 : ((b : ℕ) : ℝ) ≤ ((a : ℕ) : ℝ) := Nat.cast_le.2 (Fin.le_def.1 hba.le)
    simp only [rho]
    linarith
  have hcore := phi_decay_core (fun i => (μ i : ℝ)) hν hg hq hY
  refine le_trans (le_of_eq ?_) hcore
  have hfac : ∀ i : Fin n, lead ((i : ℕ) + 1) (NormedSpace.exp Y) ^ (-(μ i - muNext μ i)) =
      (((lead ((i : ℕ) + 1) (NormedSpace.exp Y)).re ^
        (-((μ i : ℝ) - nuNext (fun j => (μ j : ℝ)) i)) : ℝ) : ℂ) := by
    intro i
    have him : (lead ((i : ℕ) + 1) (NormedSpace.exp Y)).im = 0 := by
      have := (Complex.lt_def.1 (hpos i)).2
      simpa using this.symm
    have hre : lead ((i : ℕ) + 1) (NormedSpace.exp Y) =
        ((lead ((i : ℕ) + 1) (NormedSpace.exp Y)).re : ℂ) :=
      Complex.ext (by simp) (by simp [him])
    have hexp : (-((μ i : ℝ) - nuNext (fun j => (μ j : ℝ)) i)) = ((-(μ i - muNext μ i) : ℤ) : ℝ) := by
      simp only [nuNext, muNext]
      split_ifs <;> push_cast <;> ring
    rw [hexp, Real.rpow_intCast, Complex.ofReal_zpow, ← hre]
  simp only [PhiM, phiReal]
  rw [Finset.prod_congr rfl fun i _ => hfac i, ← Complex.ofReal_prod, Complex.ofReal_re]

theorem psiM_dec (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) (hlam : IsHCParam lam)
    {h : ℝ} (hgap : GapAtLeast ε lam h) (hq : 1 ≤ q0 ε) (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    ‖PsiM T μ (toMK k * NormedSpace.exp X)‖ ≤
      Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * q0 ε))) := by
  rw [psiM_kexp T μ k hX]
  have hB : ∀ k' : KG ε, (PhiM μ (toMK k'⁻¹ * NormedSpace.exp X * toMK k')).re ≤
      Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * q0 ε))) := by
    intro k'
    obtain ⟨hP, hE⟩ := inP_conj k'⁻¹ hX
    rw [inv_inv] at hP hE
    rw [← hE]
    have := phiM_exp_le μ hμ hlam hgap hq hP
    rw [toMK_inv, decA_hs_conj (toMK_facts k').2.1] at this
    rwa [toMK_inv]
  calc ‖T.op k * psM T μ (NormedSpace.exp X)‖ = ‖psM T μ (NormedSpace.exp X)‖ :=
        CStarRing.norm_coe_unitary_mul _ _
    _ ≤ _ := psM_norm_le T μ (exp_noncompactPart_posDef hX) hB

end ReciprocityTheory.ChartRestriction.DS.S7
