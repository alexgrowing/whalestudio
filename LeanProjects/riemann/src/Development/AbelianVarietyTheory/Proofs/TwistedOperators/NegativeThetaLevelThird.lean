import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqZeroOfForallApprox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftLowerTowerVanishing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelSixthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.XArrowCusp

theorem lift_isCuspFun : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → IsCuspFun (G.V (i + 1) j).V (fun h => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) := by
  intro hLC hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ hint
  refine GlobalTheory.CuspLocApprox.isCuspFun_of_locApprox fun C hC ε hε => ?_
  obtain ⟨n, f, p, F, v, hf, hF, happ⟩ :=
    GlobalTheory.T.negative_theta_level_sixth hLC hP D hS G₀ Pl0 T A Ks R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC ε hε
  have hX := (hLC D hS G₀ Pl0 T A Ks R G hRB hG).X t i j hi hj
  choose F' hF' hE using fun l => hX (f l) (hf l) (F l) (hF l)
  refine ⟨n, fun l => F' l ((G.X i j).It (p l) (v l)), fun l => ?_, fun x hx => ?_⟩
  · obtain ⟨h1, h2⟩ := GlobalTheory.LowVanishObj.multT_apply_cusp R.θ _ _ _ (F' l) (hF' l) ((G.X i j).It (p l) (v l))
    exact ⟨h1.toIsAutFun.cont, h1.toIsAutFun.left, h2⟩
  · have e : ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω x g
          (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l) (p l)) * F l (v l) g ∂(G.meas t i j).ν =
        ∑ l, F' l ((G.X i j).It (p l) (v l)) x :=
      Finset.sum_congr rfl fun l _ => (hE l (p l) (v l) x).2
    rw [← e]
    exact happ x hx

end GlobalTheory.XArrowCusp

end
