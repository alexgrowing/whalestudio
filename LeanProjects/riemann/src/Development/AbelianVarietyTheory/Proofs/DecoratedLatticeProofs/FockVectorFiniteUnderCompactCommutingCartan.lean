import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimensionalThetaFunctionsLevelFockDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepPreservesFockDegreeOfCommuteCartanStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelCompactTranslatesThetaFunctionStatement

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem isKFinVec_of_isFockVec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T) (sS : RealMat S) (sT : RealMat T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ K : Subgroup (GA D S), IsCompact (K : Set (GA D S)) → (∀ k ∈ K, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k)) → ∀ f, IsFockVec ψ θ S T sS sT f → IsKFinVec om K f := by
  intro D ψ θ S T χS χT om sS sT hW hθ hS hT K hK hc f hf
  obtain ⟨hth, N, hN⟩ := hf
  obtain ⟨U, hU, hUK⟩ := GlobalTheory.T.exists_common_level_compact_translates_thetaFunction D ψ S T χS χT om hW (K : Set (GA D S)) hK f hth
  have hfd := GlobalTheory.T.finiteDimensional_thetaFunctions_level_fockDegree D ψ θ S T sS sT hW.std hθ hS hT U hU N
  refine @Submodule.finiteDimensional_of_le _ _ _ _ _ _ _ hfd (Submodule.span_mono ?_)
  rintro g ⟨k, hk, rfl⟩
  exact ⟨hW.om_pres _ f hth, hUK k hk,
    GlobalTheory.T.weilRep_preserves_fockDegree_of_commute_cartan D ψ θ S T χS χT om sS sT hW hθ k (hc k hk) N f hth hN⟩

end GlobalTheory.Core.Rk.IP
