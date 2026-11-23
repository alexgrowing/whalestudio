import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NormAtPlace

theorem evFin_norm_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (x : AE F E),
    evFin F v (Algebra.norm (AF F) x) = Algebra.norm (Fv F v) (compFin F E v x) := by
  intro F E _ _ _ _ _ v x
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let e := Module.finBasis F E
  let b := Algebra.TensorProduct.basis (AF F) e
  let b' := Algebra.TensorProduct.basis (Fv F v) e
  have hrepr : ∀ (z : AF F ⊗[F] E) i, b'.repr (compFin F E v z) i = evFin F v (b.repr z i) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      simp only [compFin, b, b', AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul, map_mul, AlgHom.commutes]
    | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]
  have hb : ∀ j, compFin F E v (b j) = b' j := by
    intro j
    simp [compFin, b, b', Algebra.TensorProduct.basis_apply]
  have hmat : Algebra.leftMulMatrix b' (compFin F E v x) = (Algebra.leftMulMatrix b x).map (evFin F v) := by
    ext i j
    rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
      ← hb j, ← map_mul, hrepr]
  rw [Algebra.norm_eq_matrix_det b', Algebra.norm_eq_matrix_det b, hmat]
  exact AlgHom.map_det (evFin F v) (Algebra.leftMulMatrix b x)

end GlobalTheory.NormAtPlace
