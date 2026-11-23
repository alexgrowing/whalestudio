import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDiff
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import GroundTheory.AutomorphicForms.NormDetDiagUnitsPosRealToUnits
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces

open NumberField IsDedekindDomain Topology Filter Set MeasureTheory
open scoped NumberField.AdeleRing Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open AutomorphicForm

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem exists_height_le_of_isCompact {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω) :
    ∃ M : ℝ, ∀ b ∈ ω, height b ≤ M := by
  obtain ⟨C₀, hC₀c, hC₀⟩ := exists_compact_mem_nhds (1 : archGroup K n)
  obtain ⟨MA, hMA⟩ := exists_height_infEmb_le (K := K) (n := n) hC₀c
  set W : Set (AdelicGLn.AdelicGL K n) :=
    (fun g => archPart g) ⁻¹' C₀ ∩
      (fun g => finPart g) ⁻¹' (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n))
  have hcA : Continuous fun g : AdelicGLn.AdelicGL K n => archPart g :=
    (archEquiv K n).continuous.comp (continuous_fst.comp (AdelicGLn.prodEquiv K n).continuous)
  have hcF : Continuous fun g : AdelicGLn.AdelicGL K n => finPart g :=
    continuous_snd.comp (AdelicGLn.prodEquiv K n).continuous
  have hW : W ∈ 𝓝 (1 : AdelicGLn.AdelicGL K n) := by
    refine inter_mem (hcA.continuousAt.preimage_mem_nhds ?_) (hcF.continuousAt.preimage_mem_nhds ?_)
    · rw [show archPart (1 : AdelicGLn.AdelicGL K n) = 1 by simp [archPart]]
      exact hC₀
    · have : finPart (1 : AdelicGLn.AdelicGL K n) = 1 := by simp [finPart]
      rw [this]
      exact (AdelicGLn.isOpen_integralFiniteGL K n).mem_nhds (one_mem _)
  set c := heightConst K n
  have hc0 : 0 ≤ c := le_trans zero_le_one one_le_heightConst
  have hWb : ∀ w ∈ W, height w ≤ c * max MA 1 := by
    intro w hw
    rw [← infEmb_archPart_mul_finEmb_finPart w]
    refine (height_mul_le _ _).trans ?_
    rw [height_eq_one_of_mem_maxCompact (finEmb_mem_maxCompact hw.2), mul_one]
    exact mul_le_mul_of_nonneg_left ((hMA _ hw.1).trans (le_max_left _ _)) hc0
  obtain ⟨s, -, hs⟩ := hω.elim_nhds_subcover (fun g => (fun y => g * y) '' W) fun g _ => by
    have := (Homeomorph.mulLeft g).isOpenMap.image_mem_nhds hW
    simpa using this
  refine ⟨∑ g ∈ s, c * height g * (c * max MA 1), fun b hb => ?_⟩
  obtain ⟨g, hg, hbg⟩ := mem_iUnion₂.1 (hs hb)
  obtain ⟨w, hw, rfl⟩ := hbg
  have hterm : height (g * w) ≤ c * height g * (c * max MA 1) :=
    (height_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hWb w hw)
      (mul_nonneg hc0 (height_pos g).le))
  refine hterm.trans (Finset.single_le_sum (f := fun g => c * height g * (c * max MA 1))
    (fun g _ => ?_) hg)
  have := height_pos g
  have : 0 ≤ max MA 1 := le_trans zero_le_one (le_max_right _ _)
  positivity

theorem mult_le_two (w : InfinitePlace K) : w.mult ≤ 2 := by
  unfold InfinitePlace.mult
  split_ifs <;> norm_num

theorem height_diagUnits_posIdele_le {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) {L : ℝ} (hL1 : 1 ≤ L)
    (hL : ∀ i, ρ i ≤ L ∧ (ρ i)⁻¹ ≤ L) :
    height (Reduction.diagUnits n fun i => Reduction.posIdele (K := K) (ρ i) (hρ i)) ≤
      L ^ (2 * Fintype.card (InfinitePlace K)) := by
  set a := Reduction.diagUnits n fun i => Reduction.posIdele (K := K) (ρ i) (hρ i)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 K), Reduction.finAt v a = 1 := by
    intro v
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [Reduction.finAt_apply, Reduction.coe_diagUnits, Matrix.diagonal_apply, Units.val_one, Matrix.one_apply]
    split_ifs with h
    · subst h
      exact Reduction.posIdele_finite (K := K) (ρ i) (hρ i) v
    · rfl
  have hinf : ∀ w : InfinitePlace K, locHeight (Reduction.infAt w a) ≤ L := by
    intro w
    rw [Reduction.infAt_diagUnits_posIdele]
    refine locHeight_le hL1 (fun i j => ?_) (fun i j => ?_)
    · rw [Reduction.coe_diagUnits, Matrix.diagonal_apply]
      split_ifs with h
      · subst h
        rw [Reduction.norm_posRealToUnits w (hρ i)]
        exact (hL i).1
      · simp only [norm_zero]; linarith
    · rw [← map_inv, Reduction.coe_diagUnits, Matrix.diagonal_apply]
      split_ifs with h
      · subst h
        rw [Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv, Reduction.norm_posRealToUnits w (hρ i)]
        exact (hL i).2
      · simp only [norm_zero]; linarith
  unfold height
  rw [finprod_eq_one_of_forall_eq_one (fun v => by rw [hfin v, locHeight_one]), mul_one]
  calc ∏ w : InfinitePlace K, locHeight (Reduction.infAt w a) ^ w.mult
      ≤ ∏ _w : InfinitePlace K, L ^ 2 :=
        Finset.prod_le_prod (fun w _ => pow_nonneg (locHeight_pos _).le _) fun w _ =>
          (pow_le_pow_left₀ (locHeight_pos _).le (hinf w) _).trans
            (pow_le_pow_right₀ hL1 (mult_le_two w))
    _ = L ^ (2 * Fintype.card (InfinitePlace K)) := by
        rw [Finset.prod_const, Finset.card_univ, ← pow_mul]

theorem detModule_diagUnits_posIdele {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) :
    (Reduction.detModule K n (Reduction.diagUnits n fun i =>
      Reduction.posIdele (K := K) (ρ i) (hρ i)) : ℝ) = (∏ i, ρ i) ^ Module.finrank ℚ K := by
  rw [Reduction.detModule, MonoidHom.comp_apply, Reduction.det_diagUnits, map_prod,
    Reduction.coe_finset_prod_pos, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => Reduction.ideleModule_posIdele (ρ i) (hρ i)

theorem exists_height_le_normOne {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      ∀ kk ∈ (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)),
      ∀ x : AdelicGLn.AdelicGL K n, x ∈ Reduction.normOneGL K n →
      x = b * Reduction.diagUnits n (fun i => Reduction.posIdele (K := K) (ρ i) (hρ i)) * kk →
      ∀ A : ℝ, 1 ≤ A → (∀ i j : Fin n, ρ i / ρ j ≤ A) →
      height x ≤ C * A ^ (2 * Fintype.card (InfinitePlace K)) := by
  obtain ⟨Mb, hMb⟩ := exists_height_le_of_isCompact hω
  have hdc : Continuous fun g : AdelicGLn.AdelicGL K n => (Reduction.detModule K n g : ℝ) :=
    continuous_subtype_val.comp Reduction.continuous_detModule
  obtain ⟨M₁, hM₁⟩ := hω.exists_bound_of_continuousOn hdc.continuousOn
  obtain ⟨M₂, hM₂⟩ := hω.exists_bound_of_continuousOn
    (hdc.inv₀ fun g => (Reduction.detModule K n g).2.ne').continuousOn
  set e := 2 * Fintype.card (InfinitePlace K)
  set c₀ := max 1 (max M₁ M₂)
  have hc₀1 : 1 ≤ c₀ := le_max_left _ _
  set c := heightConst K n
  have hc0 : 0 ≤ c := le_trans zero_le_one one_le_heightConst
  have hMb1 : 0 ≤ max Mb 1 := le_trans zero_le_one (le_max_right _ _)
  refine ⟨c * (c * max Mb 1 * c₀ ^ e), by positivity, ?_⟩
  intro b hb ρ hρ kk hkk x hx hxe A hA1 hA
  set a := Reduction.diagUnits n fun i => Reduction.posIdele (K := K) (ρ i) (hρ i) with ha
  set d := Module.finrank ℚ K
  have hd : d ≠ 0 := Module.finrank_pos.ne'
  set P := ∏ i, ρ i
  have hP : 0 < P := Finset.prod_pos fun i _ => hρ i
  have hdet : (Reduction.detModule K n b : ℝ) * P ^ d = 1 := by
    have h1 := Reduction.mem_normOneGL_iff_detModule.1 hx
    have hk := Reduction.mem_normOneGL_iff_detModule.1 (Reduction.maxCompact_le_normOneGL hkk)
    rw [hxe, map_mul, map_mul, hk, mul_one] at h1
    have h2 := congrArg Subtype.val h1
    rw [Positive.val_mul, detModule_diagUnits_posIdele, Positive.val_one] at h2
    exact h2
  have hb0 : 0 < (Reduction.detModule K n b : ℝ) := (Reduction.detModule K n b).2
  have hPd : P ^ d ≤ c₀ := by
    have h1 := hM₂ b hb
    have h2 : P ^ d = (Reduction.detModule K n b : ℝ)⁻¹ := eq_inv_of_mul_eq_one_right hdet
    rw [h2]
    refine le_trans (le_abs_self _) ?_
    refine le_trans ?_ (le_max_right _ _)
    exact (by simpa [Real.norm_eq_abs] using h1 : |(Reduction.detModule K n b : ℝ)⁻¹| ≤ M₂).trans
      (le_max_right _ _)
  have hPd' : (P⁻¹) ^ d ≤ c₀ := by
    have h1 := hM₁ b hb
    have h2 : (P⁻¹) ^ d = (Reduction.detModule K n b : ℝ) := by
      rw [inv_pow, eq_inv_of_mul_eq_one_right hdet, inv_inv]
    rw [h2]
    refine le_trans (le_abs_self _) ?_
    refine le_trans ?_ (le_max_right _ _)
    exact (by simpa [Real.norm_eq_abs] using h1 : |(Reduction.detModule K n b : ℝ)| ≤ M₁).trans
      (le_max_left _ _)
  have hPc : P ≤ c₀ := by
    rcases le_or_gt P 1 with h | h
    · exact h.trans hc₀1
    · exact (le_self_pow₀ h.le hd).trans hPd
  have hPc' : P⁻¹ ≤ c₀ := by
    rcases le_or_gt P⁻¹ 1 with h | h
    · exact h.trans hc₀1
    · exact (le_self_pow₀ h.le hd).trans hPd'
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  have hbound : ∀ i, ρ i ≤ c₀ * A ∧ (ρ i)⁻¹ ≤ c₀ * A := by
    intro i
    have hn : n ≠ 0 := (Fin.pos i).ne'
    have hpow : c₀ * A ^ n ≤ (c₀ * A) ^ n := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (le_self_pow₀ hc₀1 hn) (pow_nonneg hA0 _)
    have hprodA : ∀ f : Fin n → ℝ, (∀ j, 0 ≤ f j) → (∀ j, f j ≤ A) → ∏ j, f j ≤ A ^ n := by
      intro f hf0 hfA
      calc ∏ j, f j ≤ ∏ _j : Fin n, A := Finset.prod_le_prod (fun j _ => hf0 j) fun j _ => hfA j
        _ = A ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    constructor
    · have e1 : ρ i ^ n = P * ∏ j, (ρ i / ρ j) := by
        have hPe : ∏ j, ρ j = P := rfl
        rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hPe]
        field_simp
      have h1 : ρ i ^ n ≤ (c₀ * A) ^ n := by
        rw [e1]
        refine le_trans ?_ hpow
        exact mul_le_mul hPc (hprodA _ (fun j => (div_pos (hρ i) (hρ j)).le) fun j => hA i j)
          (Finset.prod_nonneg fun j _ => (div_pos (hρ i) (hρ j)).le) (by linarith)
      exact le_of_pow_le_pow_left₀ hn (by positivity) h1
    · have e1 : (ρ i)⁻¹ ^ n = P⁻¹ * ∏ j, (ρ j / ρ i) := by
        have hPe : ∏ j, ρ j = P := rfl
        rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hPe,
          ← mul_div_assoc, inv_mul_cancel₀ hP.ne', one_div, inv_pow]
      have h1 : (ρ i)⁻¹ ^ n ≤ (c₀ * A) ^ n := by
        rw [e1]
        refine le_trans ?_ hpow
        exact mul_le_mul hPc' (hprodA _ (fun j => (div_pos (hρ j) (hρ i)).le) fun j => hA j i)
          (Finset.prod_nonneg fun j _ => (div_pos (hρ j) (hρ i)).le) (by linarith)
      exact le_of_pow_le_pow_left₀ hn (by positivity) h1
  have hL1 : 1 ≤ c₀ * A := one_le_mul_of_one_le_of_one_le hc₀1 hA1
  have hha := height_diagUnits_posIdele_le (K := K) hρ hL1 hbound
  rw [← ha] at hha
  rw [hxe]
  calc height (b * a * kk) ≤ c * height (b * a) * height kk := height_mul_le _ _
    _ = c * height (b * a) := by rw [height_eq_one_of_mem_maxCompact hkk, mul_one]
    _ ≤ c * (c * height b * height a) :=
        mul_le_mul_of_nonneg_left (height_mul_le _ _) hc0
    _ ≤ c * (c * max Mb 1 * (c₀ * A) ^ e) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left
          ((hMb b hb).trans (le_max_left _ _)) hc0) hha (height_pos _).le
          (mul_nonneg hc0 hMb1)) hc0
    _ = c * (c * max Mb 1 * c₀ ^ e) * A ^ e := by rw [mul_pow]; ring

end CuspidalSpectrum

end

end GroundTheory.Automorphic
