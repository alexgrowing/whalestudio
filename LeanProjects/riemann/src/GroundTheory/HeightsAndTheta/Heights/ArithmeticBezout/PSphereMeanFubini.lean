import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Set

noncomputable section

namespace SphereMeanFubini

def groupSplit (k n : ℕ) : Fin n ⊕ (Fin k × Fin n) ≃ Fin (k + 1) × Fin n where
  toFun := Sum.elim (fun j => (0, j)) (fun p => (p.1.succ, p.2))
  invFun p := Fin.cases (motive := fun _ => Fin n ⊕ (Fin k × Fin n)) (Sum.inl p.2)
    (fun i => Sum.inr (i, p.2)) p.1
  left_inv := by rintro (j | ⟨i, j⟩) <;> simp
  right_inv := by
    rintro ⟨i, j⟩
    cases i using Fin.cases <;> simp

def consEquiv {n : ℕ} (k : ℕ) : ((Fin n → ℂ) × (Fin k × Fin n → ℂ)) ≃ᵐ (Fin (k + 1) × Fin n → ℂ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ (Fin k × Fin n) => ℂ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (groupSplit k n))

theorem consEquiv_apply {n k : ℕ} (p : (Fin n → ℂ) × (Fin k × Fin n → ℂ)) :
    consEquiv k p = consGroup p.1 p.2 := by
  funext ⟨i, j⟩
  cases i using Fin.cases with
  | zero =>
    have e : ((0 : Fin (k + 1)), j) = groupSplit k n (Sum.inl j) := rfl
    rw [e]
    simp [consEquiv, consGroup, MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi,
      Equiv.piCongrLeft_apply_apply]
    rfl
  | succ i =>
    have e : (i.succ, j) = groupSplit k n (Sum.inr (i, j)) := rfl
    rw [e]
    simp [consEquiv, consGroup, MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi,
      Equiv.piCongrLeft_apply_apply]
    rfl

theorem measurePreserving_consEquiv {n : ℕ} (k : ℕ) :
    MeasurePreserving (consEquiv (n := n) k) volume volume :=
  (measurePreserving_piCongrLeft (fun _ : Fin (k + 1) × Fin n => (volume : Measure ℂ))
    (groupSplit k n)).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ (Fin k × Fin n) => (volume : Measure ℂ)))

theorem preimage_ballProd {n : ℕ} (h : HermNorm n) (k : ℕ) :
    consEquiv k ⁻¹' ballProd h (k + 1) = ballH h ×ˢ ballProd h k := by
  ext p
  simp only [mem_preimage, consEquiv_apply, ballProd, mem_ofPred_eq, mem_prod, ballH,
    Fin.forall_fin_succ, consGroup, Fin.cases_zero, Fin.cases_succ]

theorem nrmGroups_consGroup {n : ℕ} (h : HermNorm n) (k : ℕ) (v : Fin n → ℂ) (w : Fin k × Fin n → ℂ) :
    nrmGroups h (k + 1) (consGroup v w) = consGroup (nrmv h v) (nrmGroups h k w) := by
  funext ⟨i, j⟩
  cases i using Fin.cases <;> simp [nrmGroups, consGroup, nrmv]

theorem proof : SphereMeanFubini.Statement := by
  intro n k h G hG
  have hmp := measurePreserving_consEquiv (n := n) k
  have hme := (consEquiv (n := n) k).measurableEmbedding
  have hpre := preimage_ballProd h k
  set H : (Fin n → ℂ) × (Fin k × Fin n → ℂ) → ℝ :=
    fun p => G (nrmGroups h (k + 1) (consEquiv k p)) with hH
  have hHi : IntegrableOn H (ballH h ×ˢ ballProd h k) (volume.prod volume) := by
    rw [← hpre]
    exact (hmp.integrableOn_comp_preimage hme (f := fun u => G (nrmGroups h (k + 1) u))).2 hG
  have hint : ∫ p in ballH h ×ˢ ballProd h k, H p ∂(volume.prod volume) =
      ∫ u in ballProd h (k + 1), G (nrmGroups h (k + 1) u) := by
    rw [← hpre]
    exact hmp.setIntegral_preimage_emb hme (fun u => G (nrmGroups h (k + 1) u)) _
  have hvol : volume (ballProd h (k + 1)) = volume (ballH h) * volume (ballProd h k) := by
    rw [← hmp.measure_preimage_equiv, hpre, Measure.volume_eq_prod, Measure.prod_prod]
  rw [IntegrableOn, ← Measure.prod_restrict] at hHi
  rw [← Measure.prod_restrict, integral_prod _ hHi] at hint
  have hB0 : (volume (ballProd h k)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨(volume_ballProd_pos h k).ne', (volume_ballProd_lt_top h k).ne⟩
  have hinner : ∀ v, sphereMean h k (fun w => G (consGroup (nrmv h v) w)) =
      (volume (ballProd h k)).toReal⁻¹ * ∫ w in ballProd h k, H (v, w) := by
    intro v
    simp only [hH, consEquiv_apply, nrmGroups_consGroup]
    rw [sphereMean, setAverage_eq, smul_eq_mul, measureReal_def]
    rfl
  have hfun : (fun v => sphereMean h k (fun w => G (consGroup (nrmv h v) w))) =
      fun v => (volume (ballProd h k)).toReal⁻¹ * ∫ w in ballProd h k, H (v, w) :=
    funext hinner
  have hlhs : sphereMean h (k + 1) G = (volume (ballProd h (k + 1))).toReal⁻¹ *
      ∫ u in ballProd h (k + 1), G (nrmGroups h (k + 1) u) := by
    rw [sphereMean, setAverage_eq, smul_eq_mul, measureReal_def]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hHi.integral_prod_left.const_mul _
  · rw [hlhs, ← hint, hvol, setAverage_eq, smul_eq_mul, measureReal_def, hfun, integral_const_mul,
      ENNReal.toReal_mul, mul_inv]
    ring

end SphereMeanFubini

end

end GroundTheory.Heights₂.Heights
