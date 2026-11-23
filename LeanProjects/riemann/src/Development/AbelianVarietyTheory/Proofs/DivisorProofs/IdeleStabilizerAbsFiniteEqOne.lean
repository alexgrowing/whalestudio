import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsInfEqOne

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.IdeleTate

open GlobalTheory.Doubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evFin_norm_mem_of_mem_stab {u : (AE F E)ˣ} (hu : u ∈ stab F E) (v : HeightOneSpectrum (𝓞 F)) :
    evFin F v (Algebra.norm (AF F) (u : AE F E)) ∈ v.adicCompletionIntegers F := by
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  have hcoord : ∀ x i, GlobalTheory.IdeleDecay.coord F E x i = b.repr x i := fun x i => rfl
  have hlat : ∀ j, b j ∈ lat F E := by
    intro j i w
    rw [hcoord, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · rw [map_one]; exact one_mem _
    · rw [map_zero]; exact zero_mem _
  have hent : ∀ i j, evFin F v (Algebra.leftMulMatrix b (u : AE F E) i j) ∈ v.adicCompletionIntegers F := by
    intro i j
    have := ((hu (b j)).1 (hlat j)) i v
    rwa [hcoord, ← Algebra.leftMulMatrix_eq_repr_mul] at this
  rw [Algebra.norm_eq_matrix_det b, AlgHom.map_det, Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem (prod_mem fun i _ => ?_) _
  exact hent _ _

end GlobalTheory.IdeleTate

theorem GlobalTheory.IdeleTate.absFin_eq_one_of_mem_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∀ u ∈ GlobalTheory.IdeleTate.stab F E, GlobalTheory.IdeleTate.absFin F E u = 1 := by
  intro F E _ _ _ _ _ u hu
  exact finprod_eq_one_of_forall_eq_one fun v =>
    GlobalTheory.Doubling.absEv_unitFin_eq_one (GlobalTheory.IdeleTate.evFin_norm_mem_of_mem_stab hu v)
      (GlobalTheory.IdeleTate.evFin_norm_mem_of_mem_stab (inv_mem hu) v)
