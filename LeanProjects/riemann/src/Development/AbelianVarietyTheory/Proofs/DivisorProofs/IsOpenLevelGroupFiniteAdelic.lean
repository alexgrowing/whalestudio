import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFiniteOfHcFinite
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.LevelOpen

theorem isOpen_levG : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank), IsOpen {g : GfC V | (g : GA D V) ∈ levG V β L} := by
  intro D V β L
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨U, hU, hle⟩ := GlobalTheory.GoodFiniteDim.exists_open_subgroup V β L
  have h1 : IsOpen ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) := hU.preimage continuous_subtype_val
  exact Subgroup.isOpen_mono (H₂ := (levG V β L).subgroupOf (GfC V)) (fun g hg => (hle g.1 hg g.2).1) h1

end GlobalTheory.LevelOpen
