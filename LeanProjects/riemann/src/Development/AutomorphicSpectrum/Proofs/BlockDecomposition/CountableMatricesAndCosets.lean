import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem countable_mat_cosets : ∀ (D : D7) (a b : ℕ), Countable (Matrix (Fin a) (Fin b) D.host.E) ∧ Countable (GlobalTheory.Eis.Cosets (P D b) (GF D b)) := by
  intro D a b
  have hE : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  refine ⟨inferInstanceAs (Countable (Fin a → Fin b → D.host.E)), ?_⟩
  have hM : Countable (Matrix (Fin (b + b)) (Fin (b + b)) D.host.E) :=
    inferInstanceAs (Countable (Fin (b + b) → Fin (b + b) → D.host.E))
  have hGL : Countable (GL (Fin (b + b)) D.host.E) :=
    (Units.val_injective (α := Matrix (Fin (b + b)) (Fin (b + b)) D.host.E)).countable
  have hG : Countable (GF D b) := by
    have hR : Countable (GRat D.sp.cm.sig (Jst D b)) := by
      unfold GRat
      exact Subtype.val_injective.countable
    show Countable (ratPts D.sp.cm.sig (Jst D b))
    rw [← range_ratEmb]
    exact (Set.countable_range (ratEmb D.sp.cm.sig (Jst D b))).to_subtype
  exact Quotient.countable

end GlobalTheory.CompanionTheory.FJE
