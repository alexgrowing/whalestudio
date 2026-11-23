import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnitaryAdelicVolumeMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSetPosFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.VolMeasure

theorem existsUnique_isVolMeasG : ∀ (D : D7) (V : HSp D), V.SigOK →
    ∃! μ, IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) μ := by
  intro D V hV
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (tauE D) := GlobalTheory.CMTypePlaces.mk_tauE_bijective D
  obtain ⟨μ, hμ⟩ := GlobalTheory.Mem.VolExists.exists_isVolMeasF _ _ D.sp.cm _ (tauE D) D.cd V hτ hV
  exact ⟨μ, hμ, fun ν hν =>
    GlobalTheory.Mem.VolUnique.volMeas_unique _ _ D.sp.cm _ (tauE D) D.cd V hτ hV ν μ hν hμ⟩

end GlobalTheory.Mem.VolMeasure
