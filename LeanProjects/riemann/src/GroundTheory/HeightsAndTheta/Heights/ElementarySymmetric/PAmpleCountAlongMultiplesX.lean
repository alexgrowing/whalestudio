import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsAmpleCountAlongMultiples
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PNefCountAlongMultiples
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StatementsNefBigCountAlongMultiples
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StatementsAmpleVNefOnFibres
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

theorem AmpleCountAlongMultiples.statementB (hBig : NefBigCountAlongMultiples.Statement) (hPk : PackingStatement) :
    G6.StatementB := by
  intro K _ ι _ Ω _ _ y D M P0 II hD hII har hb hM
  obtain ⟨-, Cp, hCp⟩ := hPk K ι Ω y D M (chartLat y M.a) har hb hM.semipos.1
    (fun τ _ hs' c hc' => isIntegral_algebraMap (x := (⟨_, hs' c hc'⟩ : chartRingZ y c)))
  exact NefCountAlongMultiples.le_arithmeticVolume_of_alongMultiples hCp fun ε hε => hBig K ι Ω y D M P0 II hD hII har hb hM ε hε

theorem AmpleCountAlongMultiples.top_nonpos (hBig : NefBigCountAlongMultiples.Statement) (hPk : PackingStatement)
    (hN : ShiftNefBig.Statement) (hV : ShiftVolumeBound.Statement) (hI : ShiftIntersectionPolynomial.Statement)
    (hG : ShiftDegreePolynomial.Statement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {D : ℕ} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {P0 : Ideal (MRing ι)}
    {II : IntersectionSystem} (hD : 1 ≤ D) (hII : IsIntersectionSystem II)
    (har : IsArithVar (mCoordIdeal y) (D + 1)) (hb : Birational y) (hP0 : P0 ≤ mCoordIdeal y)
    (hs : IsSemipositiveRel P0 (mCoordIdeal y) A) (hnef : NefOnFibres (mCoordIdeal y) A.a)
    (hc : IsConjInvariantH A) (hdeg : genDeg (mCoordIdeal y) D A.a ≤ 0) :
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A) ≤ 0 := by
  have : CharZero Ω := ArithmeticVolumeDegreeZero.charZero_of_horizontal y har.2.2.1
  have hB := AmpleCountAlongMultiples.statementB hBig hPk
  obtain ⟨C, hC0, hC⟩ := hV K ι Ω y D A P0 hD har hb hP0 hs hnef hc
  obtain ⟨p, hpdeg, hpc, hp⟩ := hI K ι II (mCoordIdeal y) (D + 1) A (fsH ι) hII har hs.1
    (GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1)
  obtain ⟨r, hrdeg, hrc, hr⟩ := hG K ι (mCoordIdeal y) D A.a ((1 : ℤ) • (fsH ι).a) har
  have hbound : ∀ q : ℕ, 1 ≤ q → p.eval (q : ℝ) ≤ C * ((q : ℝ) + 1) * r.eval (q : ℝ) := by
    intro q hq
    rw [← hp q, ← hr q]
    exact (hB K ι Ω y D _ P0 II hD hII har hb (hN K ι Ω y D A P0 hD har hb hP0 hs hnef hc q hq)).trans (hC q hq)
  rw [← hpc]
  exact ArithmeticVolumeDegreeZero.coeff_le_of_eval_le_mul p r hC0 hpdeg hrdeg (by rw [hrc]; exact_mod_cast hdeg) hbound

theorem AmpleCountAlongMultiples.proof (hBig : NefBigCountAlongMultiples.Statement)
    (hF : AmpleVNefOnFibres.Statement) (hPk : PackingStatement) (hN : ShiftNefBig.Statement)
    (hV : ShiftVolumeBound.Statement) (hI : ShiftIntersectionPolynomial.Statement)
    (hG : ShiftDegreePolynomial.Statement) : AmpleCountAlongMultiples.Statement := by
  intro K _ _ ι _ _ Ω _ y D N P0 II hD hII har hb hP0 hs hcj _ hfib ε hε
  have hnef : NefOnFibres (mCoordIdeal y) N.a := hF K ι Ω y N.a hfib
  by_cases hT : II K ι (mCoordIdeal y) (D + 1) (fun _ => N) - ε ≤ 0
  · exact ⟨1, le_rfl, Eventually.of_forall fun n =>
      (mul_nonpos_of_nonpos_of_nonneg hT (by positivity)).trans (Real.log_natCast_nonneg _)⟩
  by_cases hg : genDeg (mCoordIdeal y) D N.a ≤ 0
  · exact absurd (AmpleCountAlongMultiples.top_nonpos hBig hPk hN hV hI hG hD hII har hb hP0 hs hnef hcj hg)
      (by linarith)
  exact hBig K ι Ω y D N P0 II hD hII har hb ⟨hP0, hs, hcj, hnef, by omega⟩ ε hε

end

end GroundTheory.Heights₂.Heights.Targets
