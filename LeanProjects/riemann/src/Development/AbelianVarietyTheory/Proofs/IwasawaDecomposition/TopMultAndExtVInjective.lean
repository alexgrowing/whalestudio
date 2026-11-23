import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteMult

theorem topMult_and_extV_injective : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Formalism.IndefR.RecTie.TopMultH R ∧ ∀ i t, Function.Injective (R.extV i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F h
  refine ⟨?_, fun i t => extV_injective R h.models.HV i t⟩
  intro t
  exact range_top R h.models.inf h.models.cX h.models.prX h.models.HX t

end GlobalTheory.DefiniteMult
