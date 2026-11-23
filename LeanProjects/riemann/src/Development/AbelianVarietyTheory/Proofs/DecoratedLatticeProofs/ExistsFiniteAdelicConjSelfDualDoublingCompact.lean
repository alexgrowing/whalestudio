import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryFiniteAdelicMapSelfDualCompletionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLocalLatticeIffOfFiniteAdelicCompletionMapStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCompactSubgroupConjHermitianSpaceStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.LatMove

theorem exists_conj_KAd_of_selfDual : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' →
    ∃ k ∈ GfC A, ∀ (a : GL (Fin A.rank) (AE D)) (x : GA D (dblSp A)),
      x ∈ KAd D.sp.cm.sig (dblSp A).gram L' a ↔ (io A (k, k))⁻¹ * x * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a := by
  intro D A L L' hL hL'
  obtain ⟨b, hb, hbL⟩ := GlobalTheory.T.exists_unitary_finiteAdelic_map_selfDual_completions D A L L' hL hL'
  let y : GFin D.sp.cm.sig A.gram := ⟨b, hb⟩
  have hk : ofFin D.sp.cm.sig A.gram y ∈ GfC A := by
    show infHom A (ofFin D.sp.cm.sig A.gram y) = 1
    have := projInf_ofFin D.sp.cm.sig A.gram y
    exact congrArg (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig A.gram) this
  refine ⟨ofFin D.sp.cm.sig A.gram y, hk, GlobalTheory.T.doubledCompactSubgroup_conj_hermitianSpace D A L L' _ hk ?_⟩
  intro v z
  rw [proj_ofFin]
  exact GlobalTheory.T.mem_localLattice_iff_of_finiteAdelic_completion_map D.host.F D.host.E A.rank L L' hL.1.fg hL'.1.fg b hbL v z

end GlobalTheory.Core.Rk.LatMove
