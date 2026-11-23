import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.SumSig

section Change
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem gram_family (S : HSpace E) {ι : Type} [Fintype ι] (v : ι → S.V) :
    (Matrix.of fun k l => S.hT (v k) (v l)) =
      (Matrix.of fun i k => S.frame.repr (v k) i)ᴴ * S.gram * Matrix.of fun i k => S.frame.repr (v k) i := by
  ext k l
  have hk := S.frame.sum_repr (v k)
  have hl := S.frame.sum_repr (v l)
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, HSpace.gram]
  conv_lhs => rw [← hk, ← hl]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
    Finset.sum_mul, Finset.mul_sum, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end Change

end GlobalTheory.SumSig
