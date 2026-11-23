import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticesLevelOneGenusStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedColumnLatticeHasLevelAndDualGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnLatticeEqSpanPartTransportedFrameStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryDatumLevelPrimeSplitDegreeGramFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepLevelTLat

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

theorem genusMatch_holds : ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), GenusMatch D F := by
  intro D F X u wt ιA hW hA
  obtain ⟨hT, -, -, hdeg, -, hH, hdet⟩ := record_facts D u
  have hM := (GlobalTheory.T.transported_column_lattice_has_level_and_dual_generator D X u wt hW).1
  have hL := stepLevel_tLat (S := (F u).cls0.lev)
  have hE := (GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hA).1
  obtain ⟨h, hh⟩ := GlobalTheory.T.hermitianLattices_level_one_genus D.host.F D.host.E D.sp.cm (D.R.N 0) _ hH hdet (D.mem u).A.T D.R.f
    (F u).cls0.lev.Lb (Mq wt) (D.mem u).A.T_prime hT hdeg hL hM
  exact ⟨h, fun x => (hh x).trans (hE x)⟩

end GlobalTheory.St.G
