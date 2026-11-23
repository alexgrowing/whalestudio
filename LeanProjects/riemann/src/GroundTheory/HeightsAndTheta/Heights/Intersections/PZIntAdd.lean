import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.Intersections.StZIntAdd
import GroundTheory.HeightsAndTheta.Heights.Intersections.FourierIntegralBound
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open ReciprocityTheory.AnForm.M Topology
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

theorem locDens_congr_germ {n : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas n X)
    (Φ Ψ : Fin n → LocPot X) (j : Fin A.n) (y : Fin n → ℂ)
    (h : ∀ k, (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
      (fun y' => (Ψ k).φ ((A.chart j).symm y) ((A.chart j).symm y'))) :
    locDens A Φ j y = locDens A Ψ j y := by
  unfold locDens ReciprocityTheory.AnForm.maDens
  congr 3
  funext k
  exact ReciprocityTheory.AnForm.M.PLAux.hessC_congr_eventuallyEq (h k)

theorem ZIntAdd.proof : ZIntAdd.Statement := by
  intro K _ _ ι _ P e L A B hP hR hL hA hB
  unfold zInt
  rw [dif_pos hR, dif_pos hR, dif_pos hR]
  set R := hR.some
  unfold Res.int
  have hpA := R.isPotential_pot (isSmoothPot_logH hA)
  have hpB := R.isPotential_pot (isSmoothPot_logH hB)
  have hpL : ∀ j, IsPotential R.atlas (R.pot (logH (L j))) :=
    fun j => R.isPotential_pot (isSmoothPot_logH (hL j))
  have hcons : ∀ Q : LocPot R.R.M, IsPotential R.atlas Q →
      ∀ i, IsPotential R.atlas ((Fin.cons Q fun j => R.pot (logH (L j)) :
        Fin (e + 1) → LocPot R.R.M) i) := by
    intro Q hQ i
    cases i using Fin.cases
    · exact hQ
    · exact hpL _
  have e1 : ∀ φ0 : MCone ι → ℝ,
      mInt R.atlas (fun j => R.pot ((Fin.cons φ0 fun j => logH (L j) : Fin (e + 1) → MCone ι → ℝ) j))
        (fun x => (fun _ => (1 : ℝ)) (R.pt x)) =
      mInt R.atlas (Fin.cons (R.pot φ0) fun j => R.pot (logH (L j))) (fun _ => 1) := by
    intro φ0
    refine ReciprocityTheory.AnForm.M.PLC.mInt_congr_phi _ _ _ (fun i a b => ?_) _
    cases i using Fin.cases <;> rfl
  rw [e1, e1, e1, ← mIntAdd R.atlas (R.pot (logH A)) (R.pot (logH B)) _ hpA hpB hpL _
    (mIntegrableCont _ _ (hcons _ hpA) _ continuous_const)
    (mIntegrableCont _ _ (hcons _ hpB) _ continuous_const)]
  refine ReciprocityTheory.AnForm.M.PLAux.mInt_congr fun j y hy => ?_
  congr 1
  refine locDens_congr_germ _ _ _ j y fun k => ?_
  cases k using Fin.cases
  · set x0 := (R.atlas.chart j).symm y
    have hopen : (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x0) ∈ 𝓝 y :=
      ((R.atlas.chart j).continuousOn_symm.isOpen_inter_preimage (R.atlas.chart j).open_target
        (R.R.isOpen_alt_bis _)).mem_nhds ⟨hy, R.mem_src_idx x0⟩
    filter_upwards [hopen] with y' hy'
    have hz : ∀ k, ∃ i, R.liftAt x0 ((R.atlas.chart j).symm y') ⟨k, i⟩ ≠ 0 := (R.liftAt_mem hy'.2).1
    show Real.log (A.h _ * B.h _) = Real.log (A.h _) + Real.log (B.h _)
    exact Real.log_mul (A.pos _ hz).ne' (B.pos _ hz).ne'
  · rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
