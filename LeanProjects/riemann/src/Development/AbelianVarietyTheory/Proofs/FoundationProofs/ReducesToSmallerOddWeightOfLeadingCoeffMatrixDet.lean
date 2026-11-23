import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashQExpansionCoeffWidthTransformStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEqZeroOfSumPlusMinusRepsEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashSubQExpansionPartialSumIsBigOStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOneFormOneAddExpDecayStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqDiscriminantMulOfExpDecayCuspsStatement

open UpperHalfPlane Filter GlobalTheory.OddFrame Asymptotics
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

private theorem slash_finset_sum {ι : Type*} (t : Finset ι) (k : ℤ) (f : ι → ℍ → ℂ) (x : SL(2, ℤ)) :
    (∑ i ∈ t, f i) ∣[k] x = ∑ i ∈ t, (f i) ∣[k] x := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

private theorem tendsto_exp_neg_im :
    Tendsto (fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) atImInfty (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  have h : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  exact h.const_mul_atTop_of_neg (by linarith [Real.pi_pos])

theorem reduces_of_det_leadM_eq_zero : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ))
    (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsReps Γ s →
    (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (leadM M s w F).det = 0 → Reduces Γ w F := by
  classical
  intro M Γ r s w F hM hΓ hs hF hdet
  obtain ⟨c, hc, hcv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hT := fun j => GlobalTheory.T.slashQExpansionCoeffWidth_transform M Γ (w j) (F j) hM hΓ (hF j).2
  have hb : ∀ (x : SL(2, ℤ)) (n : ℕ), n < M → ∑ j, c j * co M (w j) (F j) x n = 0 := by
    refine GlobalTheory.T.coeff_eq_zero_of_sum_plusMinusReps_eq_zero M Γ r s (fun x n => ∑ j, c j * co M (w j) (F j) x n) hM hs ?_ ?_ ?_ ?_
    · intro x n
      simp only [fun j => (hT j).1 x n, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    · intro γ hγ x n
      simp only [fun j => (hT j).2.1 γ hγ x n]
    · intro x n
      simp only [fun j => (hT j).2.2 (hF j).1 x n, mul_neg, Finset.sum_neg_distrib]
    · intro i
      have := congrFun hcv i
      simp only [Matrix.mulVec, dotProduct, leadM, Matrix.of_apply, Pi.zero_apply, Finset.sum_mul] at this
      rw [Finset.sum_comm, ← this]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n _ => mul_comm _ _
  have hO : ∀ x : SL(2, ℤ), (fun τ : ℍ => ∑ j, c j * (F j ∣[w j] x) τ) =O[atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
    intro x
    have h1 := IsBigO.sum (s := Finset.univ) fun j _ =>
      (GlobalTheory.T.slash_sub_qExpansion_partialSum_isBigO M Γ (w j) (F j) hM hΓ (hF j).2 x).const_mul_left (c j)
    refine h1.congr_left fun τ => ?_
    simp only [Finset.sum_apply, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm, sub_eq_self]
    refine Finset.sum_eq_zero fun n hn => ?_
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, hb x n (Finset.mem_range.mp hn), zero_mul]
  have hne : (Finset.univ.filter fun j => c j ≠ 0).Nonempty := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
    exact ⟨j, by simpa using hj⟩
  obtain ⟨j₀, hj₀, hmax⟩ := Finset.exists_max_image _ w hne
  have hc₀ : c j₀ ≠ 0 := by simpa using hj₀
  have he : ∀ j, ∃ e : ℍ → ℂ, IsMF ⊤ (w j₀ - w j + 4) e ∧
      (fun τ : ℍ => e τ - c j) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
    intro j
    by_cases hj : c j = 0
    · exact ⟨0, IsMF.zero _ _, by simp [hj, isBigO_zero]⟩
    · have hle : w j ≤ w j₀ := hmax j (by simpa using hj)
      obtain ⟨e, h1, h2⟩ := GlobalTheory.T.exists_levelOne_form_one_add_expDecay (w j₀ - w j + 4) (by omega)
        (((hF j₀).1.sub_odd (hF j).1).add (by decide))
      refine ⟨c j • e, h1.smul _, (h2.const_mul_left (c j)).congr_left fun τ => ?_⟩
      simp [mul_sub]
  choose e heMF heO using he
  have hH : IsMF Γ (w j₀ + 4) (∑ j, e j * F j) :=
    IsMF.sum _ fun j _ => ((heMF j).mono le_top).mul (hF j).2 (by ring)
  have hHx : ∀ x : SL(2, ℤ), (∑ j, e j * F j) ∣[w j₀ + 4] x = ∑ j, e j * (F j ∣[w j] x) := by
    intro x
    rw [slash_finset_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : w j₀ + 4 = (w j₀ - w j + 4) + w j := by ring
    rw [this, ModularForm.mul_slash_SL2, (heMF j).slash_top]
  have hHO : ∀ x : SL(2, ℤ), ((∑ j, e j * F j) ∣[w j₀ + 4] x) =O[atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
    intro x
    have h1 : (fun τ : ℍ => ∑ j, (e j τ - c j) * (F j ∣[w j] x) τ) =O[atImInfty]
        fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
      have h2 : ∀ j, (fun τ : ℍ => (e j τ - c j) * (F j ∣[w j] x) τ) =O[atImInfty]
          fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
        intro j
        have hb' : (F j ∣[w j] x) =O[atImInfty] (fun _ => (1 : ℝ)) := (hF j).2.2.2 x
        simpa only [mul_one] using (heO j).mul hb'
      exact (IsBigO.sum (s := Finset.univ) fun j _ => h2 j).congr_left fun τ => Finset.sum_apply _ _ _
    rw [hHx]
    refine (h1.add (hO x)).congr_left fun τ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by simp; ring
  obtain ⟨G, hG, hHG⟩ := GlobalTheory.T.exists_eq_discriminant_mul_of_expDecay_cusps Γ _ _ hH hHO
  have hΔ : IsMF ⊤ 12 ModularForm.discriminant := (isCF_coe_top CuspForm.discriminant).isMF
  refine ⟨j₀, w j₀ + 4 - 12, G, ModularForm.discriminant, e, by omega, ?_, hG,
    fun j => (heMF j).2.1, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := (hF j₀).1
    exact ⟨m - 4, by omega⟩
  · intro h0
    have h1 := (heO j₀).trans_tendsto tendsto_exp_neg_im
    rw [h0] at h1
    simp only [Pi.zero_apply, zero_sub] at h1
    have := tendsto_nhds_unique h1 tendsto_const_nhds
    exact hc₀ (neg_eq_zero.mp this.symm)
  · intro x τ
    have h1 := hHx x
    have h2 : w j₀ + 4 = 12 + (w j₀ + 4 - 12) := by ring
    rw [hHG, h2, ModularForm.mul_slash_SL2, hΔ.slash_top] at h1
    have h3 := congrFun h1 τ
    simpa [Finset.sum_apply] using h3

end GlobalTheory.OddFrame
