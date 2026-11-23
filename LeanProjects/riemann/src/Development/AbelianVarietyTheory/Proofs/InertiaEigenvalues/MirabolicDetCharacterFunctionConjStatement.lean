import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicDetCharacterFunctionConj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOAdd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolicDetCharacterFunction_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ) (x : G), ∃ a' : Fin D.R.r → kP PP.1, a' ≠ 0 ∧ ∀ g, mirC R i PP a tr ε (x * g * x⁻¹) = mirC R i PP a' tr ε g := by
  first | exact @GlobalTheory.DownLift.GenFinite.mirC_conj | exact GlobalTheory.DownLift.GenFinite.mirC_conj | (intros; apply GlobalTheory.DownLift.GenFinite.mirC_conj <;> assumption)
