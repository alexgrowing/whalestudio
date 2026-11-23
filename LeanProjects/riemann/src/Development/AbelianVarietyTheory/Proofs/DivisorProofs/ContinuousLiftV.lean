import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftECompFinOfAt

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal

theorem continuous_liftV {F : Type} [Field F] [NumberField F] (v : Pl F) :
    Continuous (GlobalTheory.LatVac.liftV v) := by
  change Continuous (fun a : Fv F v => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a))
  exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)

theorem continuous_liftE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : Pl F) : Continuous (liftE (E := E) v) := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  let bA := Algebra.TensorProduct.basis (Fv F v) b
  have hsum : ∀ z : Fv F v ⊗[F] E,
      liftE v z = ∑ i, GlobalTheory.LatVac.liftV v (bA.repr z i) • ((1 : AF F) ⊗ₜ[F] b i) := by
    intro z
    conv_lhs => rw [← bA.sum_repr z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp only [liftE, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
  have hfun : (liftE (E := E) v : Fv F v ⊗[F] E → AE F E) =
      fun z => ∑ i, GlobalTheory.LatVac.liftV v (bA.repr z i) • ((1 : AF F) ⊗ₜ[F] b i) := funext hsum
  rw [hfun]
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  refine continuous_finset_sum _ fun i _ => ?_
  have hl : Continuous ((Finsupp.lapply i).comp bA.repr.toLinearMap : Fv F v ⊗[F] E →ₗ[Fv F v] Fv F v) :=
    IsModuleTopology.continuous_of_linearMap _
  exact Continuous.smul ((continuous_liftV v).comp hl)
    (continuous_const : Continuous fun _ : Fv F v ⊗[F] E => ((1 : AF F) ⊗ₜ[F] b i : AE F E))

theorem continuous_liftU (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) :
    Continuous (GlobalTheory.HoweLocal.liftU (F := F) (E := E) v) := by
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  haveI : IsTopologicalAddGroup (Fv F v ⊗[F] E) := IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  rw [Units.continuous_iff]
  constructor
  · change Continuous (fun z : (Fv F v ⊗[F] E)ˣ => 1 + liftE v ((z : Fv F v ⊗[F] E) - 1))
    exact continuous_const.add ((continuous_liftE v).comp (Units.continuous_val.sub continuous_const))
  · change Continuous (fun z : (Fv F v ⊗[F] E)ˣ => 1 + liftE v (((z⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) - 1))
    exact continuous_const.add ((continuous_liftE v).comp (Units.continuous_coe_inv.sub continuous_const))

end GlobalTheory.HoweLocal
