import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ConjugateLevelCongruenceOf

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped TensorProduct

theorem tens_repr {F E : Type} [Field F] [Field E] [Algebra F E] {R R' : Type} [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] {ι : Type} (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (x : R ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis R' b).repr (tensMap (E := E) φ x) i =
      φ ((Algebra.TensorProduct.basis R b).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [tensMap, Algebra.TensorProduct.map_tmul, Finsupp.mapRange_apply, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem tensInj_holds : TensInj := by
  intro D X x y h
  let b := Module.Basis.ofVectorSpace X.B.I.F X.B.I.E
  apply (Algebra.TensorProduct.basis (Af X.B.I.F) b).repr.injective
  refine Finsupp.ext (fun i => FiniteAdeleRing.ext _ (fun v => ?_))
  have e := congrArg (fun z => (Algebra.TensorProduct.basis (Fv X.B.I.F v) b).repr z i) (h v)
  simp only [tens_repr] at e
  exact e

end MassDataLevelSSteps
