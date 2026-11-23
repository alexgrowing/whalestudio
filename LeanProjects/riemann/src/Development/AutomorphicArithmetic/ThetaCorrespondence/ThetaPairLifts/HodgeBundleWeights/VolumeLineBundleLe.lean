import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.WeilBound.CoreStatements.NefModelVolumes.VolLLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeEstimateHypotheses
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsNefModelOfImage

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
namespace SelfIntersectionVolumeEstimates.VolUpG
theorem volume_line_bundle_le : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (abelian₂ t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) w abelian₂ → Real.log abelian₂ ≤ t → volL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict 8 Z (wtOf (T.Q.Dw j) u 0) t ≤ ENNReal.ofReal (Y.dg u Z * (Y.ht u Z + t)) := by
  intro hX hP D T j Y e o hG hE Z u n w abelian₂ t hGood hBir hNo hdg hShort hLam
  obtain ⟨k, _, X, _, p, L, A, hV, hN, hS, hA, hinj⟩ :=
    _root_.SelfIntersectionVolumeEstimates.ImageNefG.exists_nef_model_of_image hX hP D T j Y e o hG hE Z u n w abelian₂ t hGood hBir hNo hdg hShort hLam
  have hd : 0 < Module.finrank ℚ Y.d.c₂.F := Module.finrank_pos
  have h2 := GlobalTheory.T.countingVolume_le_selfIntersection_nefHermitianBundle k X p (dimFlag (T.Q.Dw j)) (Module.finrank ℚ Y.d.c₂.F) 8 L A
    (fun τ => (smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) τ t).encard)
    hP.q9 hV hN hS hd (by norm_num) hinj
  refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
  have hpos : (0 : ℝ) < (Module.finrank ℚ Y.d.c₂.F : ℝ) * ((dimFlag (T.Q.Dw j) : ℝ) + 1) := by positivity
  rw [div_le_iff₀ hpos]
  linarith [hA]
end SelfIntersectionVolumeEstimates.VolUpG
end
