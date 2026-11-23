import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeLocalGlobalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneAboveStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.Pass.stepType_proof : StepType := by
  intro D P hDZ h0 h1 h2 h5
  exact GlobalTheory.T.type_local_global D P hDZ h0 (GlobalTheory.T.weil_deligne_above D h0 h1 h2 h5)
