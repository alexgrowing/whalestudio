import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.EisSep

open EisensteinSeries Complex

def pt (n : ℕ) : ℍ := UpperHalfPlane.mk (((n : ℂ) + 1) * Complex.I) (by simp; positivity)

theorem coe_pt (n : ℕ) : ((pt n : ℍ) : ℂ) = ((n : ℂ) + 1) * Complex.I := rfl

def lim0 (v : Fin 2 → ℤ) : ℂ := if v 0 = 0 then (v 1 : ℂ) ^ (-3 : ℤ) else 0

theorem re_im_summand (v : Fin 2 → ℤ) (n : ℕ) :
    ((v 0 : ℂ) * (pt n : ℂ) + v 1).re = v 1 ∧ ((v 0 : ℂ) * (pt n : ℂ) + v 1).im = v 0 * ((n : ℝ) + 1) := by
  rw [coe_pt]; constructor <;> simp

theorem norm_le (v : Fin 2 → ℤ) (n : ℕ) : ‖eisSummand 3 v (pt n)‖ ≤ ‖v‖ ^ (-(3 : ℝ)) := by
  obtain ⟨hre, him⟩ := re_im_summand v n
  set w : ℂ := (v 0 : ℂ) * (pt n : ℂ) + v 1 with hw
  have hvw : ‖v‖ ≤ ‖w‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    fin_cases i
    · have h1 := Complex.abs_im_le_norm w
      rw [him, abs_mul] at h1
      have h2 : |(v 0 : ℝ)| ≤ |(v 0 : ℝ)| * |(n : ℝ) + 1| := by
        have : (1 : ℝ) ≤ |(n : ℝ) + 1| := by rw [abs_of_pos (by positivity)]; simp
        nlinarith [abs_nonneg (v 0 : ℝ)]
      simp only [Int.norm_eq_abs]
      simpa using h2.trans h1
    · have h1 := Complex.abs_re_le_norm w
      rw [hre] at h1
      simpa [Int.norm_eq_abs] using h1
  have he : eisSummand 3 v (pt n) = w ^ (-3 : ℤ) := rfl
  rw [he, norm_zpow, Real.rpow_neg (norm_nonneg _), zpow_neg]
  rcases (norm_nonneg v).eq_or_lt with h0 | h0
  · have : v = 0 := norm_eq_zero.1 h0.symm
    have hw0 : w = 0 := by simp [hw, this]
    simp [hw0]
  · rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, zpow_ofNat]
    exact inv_anti₀ (pow_pos h0 _) (pow_le_pow_left₀ h0.le hvw _)

theorem tendsto_term (v : Fin 2 → ℤ) : Tendsto (fun n => eisSummand 3 v (pt n)) atTop (𝓝 (lim0 v)) := by
  by_cases h : v 0 = 0
  · have : ∀ n, eisSummand 3 v (pt n) = (v 1 : ℂ) ^ (-3 : ℤ) := fun n => by simp [eisSummand, h]
    simp only [this, lim0, h, if_true]
    exact tendsto_const_nhds
  · simp only [lim0, h, if_false]
    refine squeeze_zero_norm (a := fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨_, him⟩ := re_im_summand v n
    set w : ℂ := (v 0 : ℂ) * (pt n : ℂ) + v 1
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by simp
    have hw : (n : ℝ) + 1 ≤ ‖w‖ := by
      have h1 := Complex.abs_im_le_norm w
      rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)] at h1
      have : (1 : ℝ) ≤ |(v 0 : ℝ)| := by exact_mod_cast Int.one_le_abs h
      nlinarith
    have he : eisSummand 3 v (pt n) = w ^ (-3 : ℤ) := rfl
    rw [he, norm_zpow, zpow_neg, one_div]
    have hw1 : (1 : ℝ) ≤ ‖w‖ := hn.trans hw
    have : ‖w‖ ≤ ‖w‖ ^ (3 : ℤ) := by
      rw [zpow_ofNat]; nlinarith [mul_le_mul hw1 hw1 zero_le_one (by linarith)]
    exact inv_anti₀ (by positivity) (hw.trans this)

theorem tendsto_eis {M : ℕ} (c : Fin 2 → ZMod M) :
    Tendsto (fun n => eisensteinSeries c 3 (pt n)) atTop (𝓝 (∑' v : gammaSet M 1 c, lim0 v)) :=
  tendsto_tsum_of_dominated_convergence (bound := fun v : gammaSet M 1 c => ‖v.1‖ ^ (-(3 : ℝ)))
    ((summable_one_div_norm_rpow (by norm_num)).subtype _) (fun v => tendsto_term v.1)
    (Eventually.of_forall fun n v => norm_le v.1 n)

theorem eq_of_zero {M : ℕ} {c : Fin 2 → ZMod M} {v : Fin 2 → ℤ} (hv : v ∈ gammaSet M 1 c) (h0 : v 0 = 0) :
    v = ![0, 1] ∨ v = ![0, -1] := by
  have h := hv.2
  rw [h0, Int.gcd_zero_left, Int.natAbs_eq_iff] at h
  rcases h with h | h
  · left; ext i; fin_cases i <;> simp [h0, h]
  · right; ext i; fin_cases i <;> simp [h0, h]

theorem cast_zero_one (M : ℕ) : ((↑) : ℤ → ZMod M) ∘ (![0, 1] : Fin 2 → ℤ) = ![0, 1] := by
  ext i; fin_cases i <;> simp

theorem lim_one {M : ℕ} (hM : 3 ≤ M) : ∑' v : gammaSet M 1 (![0, 1] : Fin 2 → ZMod M), lim0 v = 1 := by
  haveI : Fact (2 < M) := ⟨by omega⟩
  have hm : (![0, 1] : Fin 2 → ℤ) ∈ gammaSet M 1 (![0, 1] : Fin 2 → ZMod M) := ⟨cast_zero_one M, by simp⟩
  rw [tsum_eq_single ⟨_, hm⟩]
  · simp [lim0]
  · intro v hv
    by_contra hne
    have h0 : v.1 0 = 0 := by by_contra h; simp [lim0, h] at hne
    rcases eq_of_zero v.2 h0 with h | h
    · exact hv (Subtype.ext h)
    · have h1 := congrFun v.2.1 1
      rw [h] at h1
      exact ZMod.neg_one_ne_one (n := M) (by simpa using h1)

theorem lim_ne {M : ℕ} {c : Fin 2 → ZMod M} (hc : c ≠ ![0, 1]) : ∑' v : gammaSet M 1 c, lim0 v ≠ 1 := by
  have key : ∀ v : gammaSet M 1 c, v.1 ≠ ![0, -1] → lim0 v = 0 := by
    intro v hv
    by_contra hne
    have h0 : v.1 0 = 0 := by by_contra h; simp [lim0, h] at hne
    rcases eq_of_zero v.2 h0 with h | h
    · exact hc (by rw [← v.2.1, h, cast_zero_one])
    · exact hv h
  by_cases hm : (![0, -1] : Fin 2 → ℤ) ∈ gammaSet M 1 c
  · rw [tsum_eq_single ⟨_, hm⟩ fun v hv => key v fun h => hv (Subtype.ext h)]
    simp only [lim0]
    norm_num
  · rw [tsum_congr fun v => key v fun h => hm (h ▸ v.2)]
    simp

theorem eq_of_eis_eq {M : ℕ} (hM : 3 ≤ M) {c : Fin 2 → ZMod M}
    (h : eisensteinSeries c 3 = eisensteinSeries (![0, 1] : Fin 2 → ZMod M) 3) : c = ![0, 1] := by
  by_contra hc
  have h1 := tendsto_eis c
  rw [h] at h1
  exact lim_ne hc ((tendsto_nhds_unique h1 (tendsto_eis _)).trans (lim_one hM))

theorem exists_isMF_slash_ne : ∀ M : ℕ, 3 ≤ M → ∀ x : SL(2, ℤ), x ∉ CongruenceSubgroup.Gamma M →
    ∃ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f ∧ f ∣[k] x ≠ f := by
  intro M hM x hx
  haveI : NeZero M := ⟨by omega⟩
  have hMF : ∀ a : Fin 2 → ZMod M, IsMF (CongruenceSubgroup.Gamma M) 3 (eisensteinSeries a 3) := fun a =>
    isMF_coe (ModularForm.eisensteinSeriesMF le_rfl a)
  rw [CongruenceSubgroup.Gamma_mem] at hx
  by_cases hrow : ((x 1 0 : ℤ) : ZMod M) = 0 ∧ ((x 1 1 : ℤ) : ZMod M) = 1
  · refine ⟨3, _, hMF ![-1, 0], fun h => ?_⟩
    have h2 := congrArg (fun f => f ∣[(3 : ℤ)] ModularGroup.S) h
    simp only [eisensteinSeries_slash_apply] at h2
    have hS0 : ((ModularGroup.S : SL(2, ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) = !![0, -1; 1, 0] := by
      rw [Matrix.SpecialLinearGroup.map_apply_coe, ModularGroup.coe_S]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hS : Matrix.vecMul (![-1, 0] : Fin 2 → ZMod M) ((ModularGroup.S : SL(2, ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) = ![0, 1] := by
      rw [hS0]; ext i; fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [hS, hS0] at h2
    have h3 := eq_of_eis_eq hM h2
    have h30 := congrFun h3 0
    have h31 := congrFun h3 1
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h30 h31
    exact hx ⟨h31, h30, hrow⟩
  · refine ⟨3, _, hMF ![0, 1], fun h => ?_⟩
    rw [eisensteinSeries_slash_apply] at h
    have h3 := eq_of_eis_eq hM h
    have h30 := congrFun h3 0
    have h31 := congrFun h3 1
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h30 h31
    exact hrow ⟨h30, h31⟩

end GlobalTheory.EisSep
