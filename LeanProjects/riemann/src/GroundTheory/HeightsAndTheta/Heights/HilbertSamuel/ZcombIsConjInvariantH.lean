import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionProduct
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturbSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefAmpleGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefAmpleFibre
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsZCombLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem HermLine.zcomb_isConjInvariantH {A B : HermLine ι} (hA : IsConjInvariantH A) (hB : IsConjInvariantH B)
    (p q : ℤ) : IsConjInvariantH (HermLine.zcomb A B p q) := fun z => by
  show A.h _ ^ p * B.h _ ^ q = A.h z ^ p * B.h z ^ q
  rw [hA z, hB z]

theorem fsH_isConjInvariantH (ι : K → Type) [∀ k, Fintype (ι k)] : IsConjInvariantH (fsH ι) := fun z => by
  show ∏ k, (fsMetric (ι k)).ρ (fun i => (starRingEnd ℂ) (z ⟨k, i⟩)) ^ (1 : K → ℤ) k =
    ∏ k, (fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩) ^ (1 : K → ℤ) k
  exact Finset.prod_congr rfl fun k _ => by rw [ProjLine.isConjInvariant_fs (fun i => z ⟨k, i⟩)]

theorem zcomb_metric_identity {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (q k p n : ℕ) :
    a ^ (q * n) = (a ^ ((q : ℤ) - k * p) * b ^ (p : ℤ)) ^ n * (a ^ (k : ℤ) * b ^ (-1 : ℤ)) ^ (p * n) := by
  rw [← zpow_natCast a, ← zpow_natCast (_ * _) n, ← zpow_natCast (_ * _) (p * n), mul_zpow, mul_zpow,
    ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, mul_mul_mul_comm, ← zpow_add₀ ha, ← zpow_add₀ hb]
  have e1 : ((q : ℤ) - k * p) * (n : ℤ) + (k : ℤ) * ((p * n : ℕ) : ℤ) = ((q * n : ℕ) : ℤ) := by push_cast; ring
  have e2 : (p : ℤ) * (n : ℤ) + (-1 : ℤ) * ((p * n : ℕ) : ℤ) = 0 := by push_cast; ring
  rw [e1, e2, zpow_zero, mul_one]

theorem G2.proof (hK : KodairaSection.Statement) (hS : SectionProduct.Statement)
    (hP : PerturbSemipos.Statement) (hG : NefAmpleGeneric.Statement) (hF : NefAmpleFibre.Statement)
    (hL : ZCombLimit.Statement) : G2.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D M P0 II hD hII har hb hM
  obtain ⟨k, e, C, hk, hC, he0, he, heb⟩ := hK K ι Ω y D M P0 hD har hb hM
  have hHs : IsSmoothHerm (fsH ι) := by
    have h := (hP K ι P0 (mCoordIdeal y) M 0 1 hM.semipos le_rfl zero_le_one).1
    have h' : (HermLine.zcomb M (fsH ι) 0 1).h = (fsH ι).h := by
      funext z
      simp [HermLine.zcomb]
    unfold IsSmoothHerm at h ⊢
    rwa [h'] at h
  refine ⟨k, e, C, hk, hC, he0, he, heb, fun p q hp hpq => ?_,
    hL K ι Ω y D M (fsH ι) II k hII har hM.semipos.1 hHs⟩
  have hkq : k * p ≤ q := hpq.le
  have ha : (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p).a =
      ((q - k * p : ℕ) : ℤ) • M.a + fun _ => ((p : ℕ) : ℤ) := by
    funext i
    simp [HermLine.zcomb, fsH, HermLine.ofMetrics, Nat.cast_sub hkq]
  have hb0 : (0 : ℤ) ≤ (q : ℤ) - k * p := by
    have : ((k * p : ℕ) : ℤ) ≤ q := by exact_mod_cast hkq
    push_cast at this
    linarith
  refine ⟨hP K ι P0 (mCoordIdeal y) M _ _ hM.semipos hb0 (Nat.cast_nonneg p),
    HermLine.zcomb_isConjInvariantH hM.conjInv (fsH_isConjInvariantH ι) _ _, ?_, fun ℓ hℓ => ?_, ?_⟩
  · rw [ha]
    exact hG K ι Ω y D M P0 (q - k * p) p har hM.normalForm_baseLattice_le_dualSpan_sup_line hM.semipos (by omega) hp
  · rw [ha]
    exact hF K ι Ω y D M.a (q - k * p) p ℓ har hM.nef (by omega) hp hℓ
  intro n s hs
  have hB : e ∈ chartLat y (HermLine.zcomb M (fsH ι) k (-1)).a 1 := by
    have h' : (HermLine.zcomb M (fsH ι) k (-1)).a = (k : ℤ) • M.a - 1 := by
      funext i
      simp [HermLine.zcomb, fsH, HermLine.ofMetrics]
      ring
    rw [h']
    exact he
  have hdeg : ((q * n : ℕ) : ℤ) • M.a = (n : ℤ) • (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p).a +
      ((p * n : ℕ) : ℤ) • (HermLine.zcomb M (fsH ι) k (-1)).a := by
    funext i
    simp [HermLine.zcomb, fsH, HermLine.ofMetrics]
    ring
  have hmet : ∀ z ∈ mcPts (mCoordIdeal y), M.h z ^ (q * n) =
      (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p).h z ^ n *
        (HermLine.zcomb M (fsH ι) k (-1)).h z ^ (p * n) := fun z hz =>
    zcomb_metric_identity (M.pos z hz.1).ne' ((fsH ι).pos z hz.1).ne' q k p n
  obtain ⟨hmem, hbd⟩ := hS K ι Ω y (HermLine.zcomb M (fsH ι) ((q : ℤ) - k * p) p)
    (HermLine.zcomb M (fsH ι) k (-1)) M n (p * n) (q * n) s e hdeg hmet hs hB
  refine ⟨hmem, fun c hc => ?_⟩
  have h := hbd c (Real.exp C) hc heb
  rwa [← Real.exp_nat_mul] at h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
