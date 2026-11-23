import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupLiftExists
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.SelfDualBaseFrame

theorem exists_baseFrame_frameLat : ∀ (D : D7) (V : HSp D), ∃ β₀ : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D), IsSDFrame V β₀ (frameLat V) 1 ∧ IsBaseFrame V β₀ (frameLat V) 1 := by
  intro D V
  have hl : frameLat V = GlobalTheory.Member.latC V :=
    SetLike.coe_injective ((GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice V).symm.trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq V).symm)
  have hd : Formalism.L2.Herm.dualL D.sp.cm V (frameLat V) = frameLat V := by
    rw [hl]; exact Formalism.L2.Herm.coordinate_lattice_self_dual D.sp.cm V
  obtain ⟨β, c, hc⟩ := GlobalTheory.AdelicFrame.exists_isSDFrame D V (frameLat V) (GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice V).symm hd
  rw [one_pow] at hc
  exact ⟨β, ⟨0, by rwa [pow_zero]⟩, hc⟩

end GlobalTheory.SelfDualBaseFrame
