import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToTWsmallZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicCuspFormsHermitianSpaceSignTwist
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DnLiftAut

theorem isAutFunSm_lift_dn : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → IsAutFunSm R.θ (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ hint
  have hθ : IsInfFam R.θ := hR.inf
  have hW := (hG.arrows.dn i hi).weil
  have hκ := GlobalTheory.Mem.Lift.isKerSys_thKer hθ hW.std (GlobalTheory.Ker.isWeak_of_datum hW) hW.om_cont
  have hm := hG.meas.P (i + 1) hi
  have hq0 : (G.mP (i + 1)).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.P (i + 1)).V) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := by
    by_cases hd : i + 1 = D.R.m
    · exact ⟨(hm.1 hd).1.1, (hm.1 hd).2⟩
    · exact ⟨(hm.2 hd).1.1, (hm.2 hd).2⟩
  obtain ⟨ν₁, hH, hF, hI⟩ := (GlobalTheory.SgnIdent.sgnLaw_holds D R.θ hθ true (G.P (i + 1)).V).meas _ _ hq0.1 hq0.2
  have hL' := GlobalTheory.SgnIdent.sgnLaw_holds D R.θ hθ true (G.P (i + 1)).V
  have hc : GlobalTheory.Mem.Th.IsCuspForm R.θ (GlobalTheory.Grid.sgn true (G.P (i + 1)).V) (fun g => φ (GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V g)) :=
    ⟨(GlobalTheory.SgnFun.isAutFunSm_sgn_true hL' φ).2 hφ.1, (GlobalTheory.SgnFun.isCuspFun_sgn_true hL' φ).2 hφ.2.1⟩
  have key := hκ.lift hP.cuspRapidDecay hθ ⟨hH, hF⟩ hc ⟨Φ, hΦ⟩
  have e : (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) =
      fun h => ∫ g in GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V ⁻¹' (G.mP (i + 1)).fd,
        GlobalTheory.Mem.Lift.thKer R.ψ (GlobalTheory.Grid.sgn true (G.P (i + 1)).V) (G.P i).V ((G.dn i).ω.toSgn true) ⟨Φ, hΦ⟩ g h *
          φ (GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V g) ∂ν₁ :=
    funext fun h => ((hI fun g => thetaKO (G.dn i).ω g h Φ * φ g).2).symm
  rw [e]
  exact key.2

end GlobalTheory.DnLiftAut

end
