import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsScaledFSTopPos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFSGeomDegPos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralAgainstPositive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturbSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountLeOfInjOn
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.WhittakerFunctional
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIUnique
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace ScaledFSTopPos

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem geoNum_nonneg : ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin n → K → ℤ), (∀ j k, 0 ≤ a j k) →
    0 ≤ geoNum n V a
  | 0, V, a, _ => by
    unfold geoNum
    split_ifs <;> positivity
  | n + 1, V, a, ha => by
    unfold geoNum
    split_ifs with h
    · exact Finset.sum_nonneg fun k _ => mul_nonneg (ha _ _) (finsum_nonneg fun W => finsum_nonneg fun _ =>
        mul_nonneg (Nat.cast_nonneg _) (geoNum_nonneg n W _ fun j k => ha _ _))
    · exact le_rfl

theorem semipos_of_h_eq {P0 P : Ideal (MRing ι)} {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (h : A.h = B.h)
    (hA : IsSemipositiveRel P0 P A) : IsSemipositiveRel P0 P B := by
  unfold IsSemipositiveRel IsSmoothHerm at *
  rw [← h]
  exact hA

theorem semipos (P : Ideal (MRing ι)) : IsSemipositiveRel ⊥ P (scaledFSH ι) := by
  have hM : IsSemipositiveRel ⊥ P (constLine (ι := ι) 0) := by
    refine ⟨G5.isSmoothHerm_constLine 0, fun z _ w _ => ?_⟩
    simp [leviForm, constLine, HermLine.ofWeight]
  have hfs : IsSemipositiveRel ⊥ P (fsH ι) :=
    semipos_of_h_eq (funext fun z => by simp [HermLine.zcomb])
      (PerturbSemipos.proof K ι ⊥ P _ 0 1 hM le_rfl zero_le_one)
  exact semipos_of_h_eq rfl (Mono.semipos_constShift hfs (-1))

theorem logNorm_fsH_nonpos (c : ∀ k, ι k) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    logNorm (fsH ι) (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (fun _ : K => (1 : ℕ)) k) z ≤ 0 := by
  have hpos := (fsH ι).pos z hz
  have hH : ∏ k, ‖z ⟨k, c k⟩‖ ≤ (fsH ι).h z := by
    have hfs : (fsH ι).h z = ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
      rw [fsH, GroundTheory.Heights₂.Heights.Inter.ofMetrics_fs_h]
      simp
    rw [hfs]
    refine Finset.prod_le_prod (fun k _ => norm_nonneg _) fun k _ => Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ (c k))
  unfold logNorm
  apply Real.log_nonpos (div_nonneg (norm_nonneg _) hpos.le)
  rw [div_le_one hpos]
  simpa [map_prod, norm_prod] using hH

theorem step (II : IntersectionSystem) (hII : IsIntersectionSystem II) (hG : FSGeomDegPos.Statement) (n : ℕ)
    (hlow : ∀ W : Ideal (MRing ι), IsArithVar W n → IsHorizontal W → 0 ≤ II K ι W n (fun _ => scaledFSH ι))
    (P : Ideal (MRing ι)) (hP : IsArithVar P (n + 1)) :
    0 < II K ι P (n + 1) (fun _ => scaledFSH ι) := by
  classical
  have hF := hII K ι
  set L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun _ => scaledFSH ι with hLdef
  have hHs : IsSmoothHerm (scaledFSH ι) := (semipos (ι := ι) ⊥).1
  have hFs : IsSmoothHerm (fsH ι) := GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1
  have hCs : IsSmoothHerm (constLine (ι := ι) (-1)) := G5.isSmoothHerm_constLine (-1)
  have hLs : ∀ j, IsSmoothHerm (L j) := fun _ => hHs
  have e0 : (fun _ : Fin (n + 1) => scaledFSH ι) = Fin.snoc L ((fsH ι).tensor (constLine (-1))) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [L, scaledFSH]
  rw [e0, hF.2.1 P n L _ _ hP hLs hFs hCs]
  obtain ⟨c, hc⟩ : ∃ c : ∀ k, ι k, ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P :=
    ⟨fun k => (hP.2.1.2.2 k).choose, fun k => (hP.2.1.2.2 k).choose_spec⟩
  have hsH := GroundTheory.Heights₂.Heights.Inter.ThmIUnique.isMultiHomog_coordMonomial c (fun _ : K => (1 : ℕ))
  have hsP := GroundTheory.Heights₂.Heights.Inter.ThmIUnique.coordMonomial_not_mem hP.2.1.1 c hc (fun _ : K => (1 : ℕ))
  have hfa : ∀ k, (fsH ι).a k = ((fun _ : K => (1 : ℕ)) k : ℤ) := fun k => by simp [fsH, HermLine.ofMetrics]

  have hA : 0 ≤ II K ι P (n + 1) (Fin.snoc L (fsH ι)) := by
    rw [hF.2.2 P n L (fsH ι) _ _ hP hLs hFs hfa hsH hsP, recR_eq]
    refine sub_nonneg.mpr (le_trans ?_ (finsum_nonneg fun W => finsum_nonneg fun hW =>
      mul_nonneg (Nat.cast_nonneg _) ?_))
    · exact IntegralAgainstPositive.proof K ι P ⊥ n L _ bot_le (fun _ => semipos P)
        fun z hz => logNorm_fsH_nonpos c hz.1
    · split_ifs with hh
      · exact hlow W ((divSuppArith K ι P n (fsH ι) _ W hP ⟨_, hfa, hsH, hsP⟩ hW).1 hh) hh
      · exact mul_nonneg (by exact_mod_cast geoNum_nonneg n W _ fun j k => by simp [L, scaledFSH_a])
          (Real.log_natCast_nonneg _)

  have hone : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  have hca : ∀ k, (constLine (ι := ι) (-1)).a k = ((0 : K → ℕ) k : ℤ) := fun k => by
    simp [constLine, HermLine.ofWeight]
  have hB : II K ι P (n + 1) (Fin.snoc L (constLine (-1))) = ptsIntegral P (pot L) (fun _ => 1) := by
    rw [hF.2.2 P n L _ 1 0 hP hLs hCs hca GroundTheory.Heights₂.Heights.Inter.ThmIUnique.isMultiHomog_one' hone, recR_eq]
    have hd : divSupp P (1 : MRing ι) = ∅ := by
      ext W
      simp only [divSupp, Ideal.span_singleton_one, le_top, sup_of_le_right, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h => (h.1.1.ne_top (top_le_iff.mp h.1.2)).elim
    have hl : logNorm (constLine (ι := ι) (-1)) 1 = fun _ => -1 := by
      funext z
      simp [logNorm, constLine, HermLine.ofWeight]
    rw [cycR, hd, finsum_mem_empty, arInt, hl, G5.ptsIntegral_const]
    simp only [zero_sub, neg_mul, one_mul, neg_neg]
    rfl
  have heq : ptsIntegral P (pot L) (fun _ => 1) = ptsIntegral P (pot fun _ : Fin n => fsH ι) (fun _ => 1) :=
    G5.ptsIntegral_eq_of_add_const P _ _ (fun j => ⟨1, fun z hz => by
      show Real.log ((scaledFSH ι).h z) = Real.log ((fsH ι).h z) + 1
      rw [show (1 : ℝ) = -(-1) by norm_num]
      exact G5.log_tensor_constLine (fsH ι) (-1) z hz.1⟩) _
  have hpos := hG K ι P n hP
  linarith
end ScaledFSTopPos

theorem ScaledFSTopPos.proof (hG : FSGeomDegPos.Statement) : ScaledFSTopPos.Statement := by
  intro K _ ι _ P d II hII hd hP
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  clear hd
  induction n generalizing P with
  | zero =>
    exact ScaledFSTopPos.step II hII hG 0
      (fun W hW _ => absurd hW (GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι W)) P hP
  | succ m ih => exact ScaledFSTopPos.step II hII hG (m + 1) (fun W hW _ => (ih W hW).le) P hP

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
