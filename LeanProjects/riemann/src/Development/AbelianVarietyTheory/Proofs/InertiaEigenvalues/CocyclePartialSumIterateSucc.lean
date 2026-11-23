import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaussGCTarget
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisUniqueStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

variable {l : ℕ} [Fact l.Prime]

theorem iSup_pow_eq {f : ℕ → ℝ} (h0 : ∀ n, 0 ≤ f n) (hb : BddAbove (Set.range f)) (k : ℕ) :
    (⨆ n, f n ^ k) = (⨆ n, f n) ^ k := by
  have hS : 0 ≤ ⨆ n, f n := le_ciSup_of_le hb 0 (h0 0)
  have hle : ∀ n, f n ^ k ≤ (⨆ n, f n) ^ k := fun n => pow_le_pow_left₀ (h0 n) (le_ciSup hb n) k
  have hb' : BddAbove (Set.range fun n => f n ^ k) := ⟨_, Set.forall_mem_range.2 hle⟩
  refine le_antisymm (ciSup_le hle) ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  by_contra hlt
  push_neg at hlt
  set T := ⨆ n, f n ^ k
  have hT : 0 ≤ T := le_ciSup_of_le hb' 0 (pow_nonneg (h0 0) k)
  have hroot : T ^ ((1 : ℝ) / k) < ⨆ n, f n := by
    have := Real.rpow_lt_rpow hT hlt (by positivity : (0 : ℝ) < 1 / k)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hS, mul_one_div_cancel (by positivity), Real.rpow_one] at this
  obtain ⟨n, hn⟩ := exists_lt_of_lt_ciSup hroot
  have h1 := pow_lt_pow_left₀ hn (Real.rpow_nonneg hT _) hk.ne'
  rw [← Real.rpow_natCast, ← Real.rpow_mul hT, one_div_mul_cancel (by positivity), Real.rpow_one] at h1
  exact absurd (le_ciSup hb' n) (not_le.2 h1)

theorem gA_phi (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (a : Formalism.Per.Ainf l) :
    gA l ρ (Formalism.Per.φA l a) = gA l (ρ ^ ((1 : ℝ) / l)) a ^ l := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  set σ := ρ ^ ((1 : ℝ) / l)
  have hσ0 : 0 ≤ σ := Real.rpow_nonneg hρ0 _
  have hσ1 : σ ≤ 1 := Real.rpow_le_one hρ0 hρ1 (by positivity)
  have hσl : σ ^ l = ρ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0, one_div_mul_cancel hl.ne', Real.rpow_one]
  set f : ℕ → ℝ := fun n => ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * σ ^ n
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hf1 : ∀ n, f n ≤ 1 := fun n =>
    mul_le_one₀ (Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity))
      (pow_nonneg hσ0 _) (pow_le_one₀ hσ0 hσ1)
  have hterm : ∀ n, ‖((((Formalism.Per.φA l a).coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n
      = f n ^ l := by
    intro n
    have hc : (Formalism.Per.φA l a).coeff n = a.coeff n ^ l := by
      rw [GlobalTheory.RingBasics.φA_apply, WittVector.coeff_frobenius_charP]
    rw [hc, map_pow, SubmonoidClass.coe_pow, norm_pow, ← hσl, mul_pow, ← pow_mul, ← pow_mul, mul_comm n l, pow_mul]
    congr 1
    rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Real.rpow_mul_natCast (norm_nonneg _), mul_comm]
  simp only [gA]
  simp_rw [hterm]
  exact iSup_pow_eq hf0 ⟨1, Set.forall_mem_range.2 hf1⟩ l

theorem isGauss_phi (ρ : ℝ) (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    IsGauss l (ρ ^ ((1 : ℝ) / l)) (fun x => gC l ρ (φc l x) ^ ((1 : ℝ) / l)) := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hρ0 : 0 ≤ ρ := (inv_nonneg.2 hl.le).trans h0
  obtain ⟨e1, e2, e3, e4, e5⟩ := isGauss_gC_of_le l ρ h0 h1
  have hpos : (0 : ℝ) < 1 / l := by positivity
  refine ⟨fun x => ⟨Real.rpow_nonneg (e1 _).1 _, Real.rpow_le_one (e1 _).1 (e1 _).2 hpos.le⟩, fun x y => ?_,
    fun x => ?_, fun x y => ?_, fun a => ?_⟩
  · simp only [map_add]
    refine (Real.rpow_le_rpow (e1 _).1 (e2 _ _) hpos.le).trans ?_
    rcases le_total (gC l ρ (φc l x)) (gC l ρ (φc l y)) with h | h
    · rw [max_eq_right h, max_eq_right (Real.rpow_le_rpow (e1 _).1 h hpos.le)]
    · rw [max_eq_left h, max_eq_left (Real.rpow_le_rpow (e1 _).1 h hpos.le)]
  · simp only [map_neg, e3]
  · simp only [map_mul, e4]
    exact Real.mul_rpow (e1 _).1 (e1 _).1
  · simp only
    have ha : φc l (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) =
        algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.φA l a) := (GlobalTheory.CrisMaps.phiA_extends l).alg a
    rw [ha, e5, gA_phi ρ hρ0 h1.le, ← Real.rpow_natCast, ← Real.rpow_mul, mul_one_div_cancel hl.ne', Real.rpow_one]
    exact le_ciSup_of_le ⟨1, by
      rintro _ ⟨n, rfl⟩
      exact mul_le_one₀ (Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity))
        (pow_nonneg (Real.rpow_nonneg hρ0 _) _) (pow_le_one₀ (Real.rpow_nonneg hρ0 _)
          (Real.rpow_le_one hρ0 h1.le (by positivity)))⟩ 0 (by positivity)

theorem gC_phi : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → ∀ x : Formalism.Per.Acris l,
    gC l ρ (φc l x) = gC l (ρ ^ ((1 : ℝ) / l)) x ^ l := by
  intro l _ ρ h0 h1 x
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl : (0 : ℝ) < l := by linarith
  have hρ0 : 0 ≤ ρ := (inv_nonneg.2 hl.le).trans h0
  have hσ0 : ρ ≤ ρ ^ ((1 : ℝ) / l) := by
    conv_lhs => rw [← Real.rpow_one ρ]
    exact Real.rpow_le_rpow_of_exponent_ge' hρ0 h1.le (by positivity)
      (by rw [div_le_one hl]; exact hl1.le)
  have hσ1 : ρ ^ ((1 : ℝ) / l) < 1 := Real.rpow_lt_one hρ0 h1 (by positivity)
  have e := GlobalTheory.T.gaussNormAcris_unique l (ρ ^ ((1 : ℝ) / l)) _ _ (h0.trans hσ0) hσ1 (isGauss_phi ρ h0 h1)
    (isGauss_gC_of_le l _ (h0.trans hσ0) hσ1)
  have ex : gC l ρ (φc l x) ^ ((1 : ℝ) / l) = gC l (ρ ^ ((1 : ℝ) / l)) x := congrFun e x
  rw [← ex, ← Real.rpow_natCast, ← Real.rpow_mul ((isGauss_gC_of_le l ρ h0 h1).1 _).1,
    one_div_mul_cancel hl.ne', Real.rpow_one]

end GlobalTheory.PMon.Gauss

end
