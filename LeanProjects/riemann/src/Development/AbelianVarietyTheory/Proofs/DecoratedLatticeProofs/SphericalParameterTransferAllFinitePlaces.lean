import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalTransferWeilPairingInertPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterTransferSplitPlaceStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem transferOn_all : GlobalTheory.Hk3.HoweUnram → ∀ D : D7, TransferOn D fun _ => True := by
  intro hH D ψ S T χS χT om hW t ht v _
  by_cases hv : IsSplit (E := D.host.E) v
  · exact GlobalTheory.T.sphericalParameterTransfer_splitPlace D ψ S T χS χT om hW t ht v hv
  · exact GlobalTheory.T.sphericalTransfer_weilPairing_inertPlaces hH D ψ S T χS χT om hW t ht v hv

end GlobalTheory.ChainOnto

end
