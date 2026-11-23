import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsAmpleCountAlongMultiplesAmple
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftCountAlongMultiples
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

theorem charZero_of_isArithVar_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : ((n : ℤ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]
    simp only [mConeMap, map_natCast]
    rw [← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [h.2.2.1] at hmem
  exact_mod_cast (Ideal.mem_bot).1 hmem

theorem AmpleCountAlongMultiples.proofAmple (hL : LiftModel.Statement) (hC : LiftCountAlongMultiples.Statement) :
    AmpleCountAlongMultiples.StatementAmple := by
  intro K _ _ ι _ _ Ω _ y D N P0 II hD hII har hb hP0 hs hcj hgen hc hfib ε hε
  have : CharZero Ω := charZero_of_isArithVar_mCoordIdeal har
  obtain ⟨a, ι', _, x', ha, hmem, hgo, hbir⟩ := hL K ι Ω y D N.a har hb hgen hc hfib
  refine ⟨a, ha, ?_⟩
  have hapos : (0 : ℝ) < (a : ℝ) ^ (D + 1) := pow_pos (by exact_mod_cast ha) _
  filter_upwards [hC K ι Ω y D N P0 II a ι' x' hD hII har hb hP0 hs hcj ha hmem hgo hbir
    (ε * (a : ℝ) ^ (D + 1)) (mul_pos hε hapos)] with k hk
  have key : (II K ι (mCoordIdeal y) (D + 1) (fun _ => N) - ε) *
        (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =
      ((a : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => N) - ε * (a : ℝ) ^ (D + 1)) *
        ((k : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
    push_cast
    ring
  rw [key]
  exact hk

end

end GroundTheory.Heights₂.Heights.Targets
