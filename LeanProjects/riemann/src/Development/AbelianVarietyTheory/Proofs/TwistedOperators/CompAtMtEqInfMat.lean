import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilDeriv

theorem compAt_mt_eq_infMat {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) :
    compAt θ τ (mt V g) = infMat D.sp.cm.sig V.gram (θ τ) g := by
  ext i j
  simp only [compAt, Formalism.L2.Theta.mt, infMat, matHom, Matrix.map_apply]
  rfl

theorem om_dRho_infMat : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (g : GA D S) (h : GA D T) τ z f, IsThetaFunO ψ S T f → om (g, h) (Datum.dRho (heisO ψ S T) θ τ z f) = Datum.dRho (heisO ψ S T) θ τ (infMat D.sp.cm.sig T.gram (θ τ) h * z * infMat D.sp.cm.sig S.gram (θ τ) g⁻¹) (om (g, h) f) := by
  intro D ψ S T χS χT om hW θ hθ g h τ z f hf
  rw [← compAt_mt_eq_infMat θ τ T h, ← compAt_mt_eq_infMat θ τ S g⁻¹]
  exact GlobalTheory.WeilVacMove.om_dRho hW hθ g h τ z hf

end GlobalTheory.WeilDeriv
