import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrableSmoothSubmoduleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleDiscreteSpaces

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.FinDiscOrth

theorem exists_compact_open_level_le (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (S : Subgroup (GL (Fin N) (Af E))) (hS : IsOpen (S : Set (GL (Fin N) (Af E)))) :
    ∃ L : Subgroup (GL (Fin N) (Af E)), L ≤ S ∧ IsOpen (L : Set (GL (Fin N) (Af E))) ∧
      IsCompact (L : Set (GL (Fin N) (Af E))) := by
  let K : Subgroup (GL (Fin N) (Af E)) := GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E N
  have hKo : IsOpen (K : Set (GL (Fin N) (Af E))) :=
    GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E N
  have hKc : IsCompact (K : Set (GL (Fin N) (Af E))) :=
    GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E N
  have hSc : IsClosed (S : Set (GL (Fin N) (Af E))) := Subgroup.isClosed_of_isOpen S hS
  refine ⟨S ⊓ K, inf_le_left, ?_, ?_⟩
  · simpa using hS.inter hKo
  · have : ((S ⊓ K : Subgroup _) : Set (GL (Fin N) (Af E))) =
        (K : Set (GL (Fin N) (Af E))) ∩ (S : Set (GL (Fin N) (Af E))) := by
      ext x; simp [and_comm]
    rw [this]
    exact hKc.inter_right hSc

end GlobalTheory.CompanionTheory.FinDiscOrth
