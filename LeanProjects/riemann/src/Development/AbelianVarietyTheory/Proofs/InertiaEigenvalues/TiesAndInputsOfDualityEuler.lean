import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SurjectiveHalf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeNhds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompletionPhiSubOneBijective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDeRhamFiltrationQuotientInvariants
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalExactSequenceContinuityAllTheories
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualDeRhamAndFilZeroDimAllStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.LocInputs

open TensorProduct in

theorem _root_.GlobalTheory.LocInputs.ties_and_inputs_of_duality_euler :
    _root_.Formalism.GaloisCohomology.LocalTateDualityK → _root_.Formalism.GaloisCohomology.LocalEulerCharK →
      ∀ (D : _root_.Formalism.BasicNotions.D7) (HW : _root_.Formalism.BasicNotions.HWOf D.loc) (F : _root_.Formalism.BasicNotions.FonOf D.loc D.locA HW),
        ∃ _J : _root_.Formalism.MainNotions.LocalSituation.Ties D.loc D.locA HW F, _root_.Formalism.MainNotions.LocalSituation.admitted D HW F := by
  intro hduality heuler D HW F
  refine ⟨⟨fun l _ => (_root_.GlobalTheory.ThetaTie.nonempty_thetaL D l).some⟩, ?_⟩
  refine ⟨?_, hduality, _root_.GlobalTheory.TateTop.tate_h2_of_local_duality hduality D, heuler,
    _root_.GlobalTheory.TateFilQuot.tate_fil_quot D, _root_.GlobalTheory.FundCont.fundamentalExactSequence_continuity_all_theories D,
    _root_.GlobalTheory.Per.FontaineAll.fontaine_bounds D, _root_.GlobalTheory.TateDualFil.main D, ?_⟩
  · refine _root_.GlobalTheory.FundSeq.surjective_half_of_onto (fun l _ => ?_) D
    obtain ⟨C⟩ := _root_.GlobalTheory.MemLoc.nonempty_core l
    exact _root_.GlobalTheory.FundSeq.ontoAt_of_core C
      (_root_.GlobalTheory.MemLoc.one_sub_phi_onto l C) (_root_.GlobalTheory.MemLoc.FundOnto.fundOnto l C)
  · intro l _ K s LL h
    exact ⟨_root_.GlobalTheory.Cyc.FontW.main D HW F l K s LL h,
      _root_.GlobalTheory.Decompl.decompletion D HW F l K s LL h⟩

end GlobalTheory.LocInputs
