import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseLatLineOffT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedP
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatZeroLineStatement

set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory
theorem baseLat_line_offT_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (hr : 1 ≤ D.R.rS) u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, PP.under (𝓞 D.host.F) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → ∀ u'' : D.what₂.Word, (((D.mem u'').A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = v) ↔ c ∈ GlobalTheory.FinPl.intAt D (· = v)) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u f B hP x hxg hxt u'' hxu c hc
  obtain ⟨k, _, _, _, _, ι, v', o, n, G, pl, hc0, hv0, hvt, hso, hgp, hgr, hbt, hpt⟩ := hP
  have hm : 0 < D.R.m := by unfold Ranks.rS at hr; omega
  have hxg' : x ∉ v'.gP := by
    intro h
    obtain ⟨PP, hPP, hPx⟩ := (hvt.gP x).1 h
    exact hxg PP hPP hPx.symm
  have hmv := hvt.moves 0 hm (· = x) (by rintro p rfl; exact hxg')
  set b : GA D (D.sp.Y 0) := f.g.b 0 with hb
  set w : Fin (D.sp.Y 0).rank → AE D := fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))) with hw
  have hy : ∀ i, (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹) w) i ∈ idAt D (· = x) := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ?_
    exact Ideal.mul_mem_right _ _ hc
  have key : (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹) w ∈ latV (D.sp.Y 0) ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) (· = x) ↔
      Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b) (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹) w) ∈ latV (D.sp.Y 0) (v'.N 0) (· = x)) :=
    hmv _ hy
  have hinv : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b) (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹) w) = w := by
    rw [Matrix.mulVec_mulVec]
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  rw [hinv] at key
  refine key.trans ?_
  exact _root_.GlobalTheory.T.smul_frameVector_mem_latV_iff_mem_intAt W hW hr u f B k ι v' o n G pl hc0 hv0 hvt hso hgp hgr hbt hpt x hxg'
    (fun h => hxt ((hvt.tP x).1 h)) u'' hxu c hc
end GlobalTheory
end
