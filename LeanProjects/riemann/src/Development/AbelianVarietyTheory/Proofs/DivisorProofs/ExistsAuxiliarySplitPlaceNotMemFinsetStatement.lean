import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAuxiliarySplitPlaceNotMemFinsetAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlaceHermitianSpace_notMem_finset : ∀ (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∃ U : AuxiliaryPlaceHermitianSpace V, U.u ∉ S := by
  first | exact @GlobalTheory.AuxiliarySplitPlace.exists_auxiliarySplitPlace_notMem_finset | exact GlobalTheory.AuxiliarySplitPlace.exists_auxiliarySplitPlace_notMem_finset | (intros; apply GlobalTheory.AuxiliarySplitPlace.exists_auxiliarySplitPlace_notMem_finset <;> assumption)
