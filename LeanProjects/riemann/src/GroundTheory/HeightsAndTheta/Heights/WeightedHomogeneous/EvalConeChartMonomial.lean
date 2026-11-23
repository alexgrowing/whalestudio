import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace SectionNorm

omit [DecidableEq ι] in

theorem evalCone_chartMonomial (z : Cone n ℂ) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) :
    evalCone z (chartMonomial c d) = ∏ k, z k (c k) ^ d k := by
  simp [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]

theorem evalCone_liftOld {P : ArithVariety n} (D : AddBlockData P) (w : Cone D.extSizes ℂ)
    (f : MvPolynomial (Coord n) ℤ) : evalCone w (D.liftOld f) = evalCone (D.basePart₂ w) f := by
  simp only [evalCone, AddBlockData.liftOld, eval₂_rename]
  rfl

theorem chartMonomial_ne_zero {P : ArithVariety n} (D : AddBlockData P) {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) (c : (k : ι) → Fin (n k + 1))
    (j : Fin (D.size + 1)) (hgz : evalCone z (g c j) ≠ 0) :
    evalCone z (chartMonomial c d) ≠ 0 := by
  intro hm
  have hc : P.IsLive c := by
    by_contra hc
    exact hgz (by rw [hg.dead c hc j]; simp [evalCone])
  have hex : ∀ k, ∃ i, z k i ≠ 0 := fun k ↦ Function.ne_iff.mp (hz.1 k)
  choose c' hc' using hex
  have hlive : P.IsLive c' := by
    intro k hk
    apply hc' k
    have := hz.2 _ hk
    simpa [evalCone, eval₂_X] using this
  have hmem : chartMonomial c' d * g c j - chartMonomial c d * g c' j ∈ P.ideal := by
    rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, hg.value c hc j, hg.value c' hlive j]
    ring
  have h0 := hz.2 _ hmem
  have hsub : evalCone z (chartMonomial c' d * g c j - chartMonomial c d * g c' j) =
      evalCone z (chartMonomial c' d) * evalCone z (g c j) -
        evalCone z (chartMonomial c d) * evalCone z (g c' j) := by
    simp [evalCone, eval₂_sub, eval₂_mul]
  rw [hsub, hm, zero_mul, sub_zero] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · rw [evalCone_chartMonomial] at h
    exact Finset.prod_ne_zero_iff.mpr (fun k _ ↦ pow_ne_zero _ (hc' k)) h
  · exact hgz h

end SectionNorm

theorem SectionNorm.proof (hP : ConePoints.Statement) (hM : ChartMetric.Statement) :
    SectionNorm.Statement := by
  intro ι _ _ n P D N hN d g hg r G δ hG c j _ w hw hgz
  obtain ⟨hz, la, hla, hform⟩ := (hP ι n P D d g hg).2 w hw
  have hm := SectionNorm.chartMonomial_ne_zero D hg hz c j hgz
  have hmet := (hM ι n P D N hN d g hg r G δ hG).2 w hw c la hm (hform c hm)
  have hNpos : 0 < N.metric (D.basePart₂ w) := N.metric_pos _ hz.1
  have heval : evalCone w (X (D.newCoord j) * D.liftOld (chartMonomial c d)) =
      D.newPart w j * evalCone (D.basePart₂ w) (chartMonomial c d) := by
    rw [show evalCone w (X (D.newCoord j) * D.liftOld (chartMonomial c d)) =
        evalCone w (X (D.newCoord j)) * evalCone w (D.liftOld (chartMonomial c d)) by
      simp [evalCone, eval₂_mul], SectionNorm.evalCone_liftOld]
    simp [evalCone, eval₂_X, AddBlockData.newCoord, AddBlockData.newPart]
  rw [heval, SectionNorm.evalCone_liftOld, hmet, hform c hm j, div_mul_cancel₀ _ hm,
    mul_div_assoc, div_self hNpos.ne', mul_one, norm_mul]
  have h1 : ‖la‖ ≠ 0 := norm_ne_zero_iff.mpr hla
  have h2 : ‖evalCone (D.basePart₂ w) (g c j)‖ ≠ 0 := norm_ne_zero_iff.mpr hgz
  field_simp

end

end GroundTheory.Heights₂.Heights
