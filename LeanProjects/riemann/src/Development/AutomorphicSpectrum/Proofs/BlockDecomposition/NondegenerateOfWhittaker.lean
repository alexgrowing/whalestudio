import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitNDgOfLocalOfSteps
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SWGlue

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

variable {D : D7} {n : ℕ}

theorem weil_cell_zero {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) {w u : G D n} (hw : mat w = blk4 0 1 (-1) 0) (b : hermA D n)
    (hu : mat u = blk4 1 b.1 0 1) (Φ : schwartzA θ V.rank n) (g : G D n) :
    (ω (w * u * g) Φ).1 0 = Jt ψ V μ (ω g Φ).1 b := by
  have e : ω (w * u * g) Φ = ω w (ω u (ω g Φ)) := by
    simp only [map_mul, Module.End.mul_apply]
  rw [e, hω.weyl w hw _ 0]
  unfold Jt
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have h0 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
    simp [GlobalTheory.StdUnn.inner, GlobalTheory.MixModel.adj]
  simp only [h0, Matrix.trace_zero, map_zero, AddChar.map_zero_eq_one, mul_one]
  rw [hω.unip u b.1 hu (ω g Φ) y, mul_comm]

theorem ndOfWhit : PositivityTheory.PfSWUS.NDOfWhit := by
  intro hU hT hW D n V ψ χ θ μ ω H l s ν Φ hS hR nb lam 𝓖 hC β hβ g
  obtain ⟨w, hw⟩ := GlobalTheory.StdUnn.Model.exists_weyl (D := D) (n := n)
  have h1 := hW D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ g
  rw [hT D n V ψ χ θ μ ω H l s ν Φ hS hR nb lam 𝓖 hC β hβ g]
  refine h1.congr ⟨(n : ℝ) / 2, fun z hz => ?_⟩
  show _ = fc ψ lam 𝓖 nb (fun x => eis ω H Φ x z) β g
  rw [(hU D n V ψ χ θ μ ω H l s ν Φ hS hR nb lam 𝓖 hC w hw β hβ z hz g).2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  show _ * _ = sect ω H Φ z (w * nb b * g) * _
  rw [sect, weil_cell_zero hS.hω hw b (hC.1 b) Φ g]

end GlobalTheory.CompanionTheory.SWGlue

end
