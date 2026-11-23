import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLocalComponentDataStatement
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory

theorem baseLat_line_offT : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ (hr : 1 ≤ D.R.rS) u (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → ∀ u'' : D.what₂.Word, (((D.mem u'').A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((pk W).ΛY 0) (· = v) ↔ c ∈ GlobalTheory.FinPl.intAt D (· = v)) := by

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
  have key : (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹) w ∈ latV (D.sp.Y 0) ((pk W).ΛY 0) (· = x) ↔
      Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b) (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹) w) ∈ latV (D.sp.Y 0) (v'.N 0) (· = x)) :=
    hmv _ hy
  have hinv : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b) (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹) w) = w := by
    rw [Matrix.mulVec_mulVec]
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  rw [hinv] at key
  refine key.trans ?_

  exact GlobalTheory.T.bessel_local_component_data W hW hr u f B k ι v' o n G pl hc0 hv0 hvt hso hgp hgr hbt hpt x hxg'
    (fun h => hxt ((hvt.tP x).1 h)) u'' hxu c hc

end GlobalTheory
