import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsInfEqOne

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
namespace GlobalTheory.IdeleSizeUnit

theorem coord_inf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : InfinitePlace F) (x : AE F E) (i : Fin (Module.finrank F E)) :
    haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    GlobalTheory.AdelicU.evInf F w (GlobalTheory.IdeleDecay.coord F E x i) =
      (Algebra.TensorProduct.basis w.Completion (Module.finBasis F E)).repr (GlobalTheory.AdelicU.compInf F E w x) i := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  unfold GlobalTheory.IdeleDecay.coord GlobalTheory.AdelicU.compInf
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, Finsupp.add_apply, hx, hy]

end GlobalTheory.IdeleSizeUnit

theorem GlobalTheory.IdeleSizeUnit.size_mul_of_unitInf_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (b h : (AE F E)ˣ),
    (∀ w, GlobalTheory.Doubling.unitInf F E w b = 1) → GlobalTheory.IdeleDecay.size F E (b * h : (AE F E)ˣ).1 = GlobalTheory.IdeleDecay.size F E h.1 := by
  intro F E _ _ _ _ _ b h hb
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hc : ∀ w, GlobalTheory.AdelicU.compInf F E w (b * h : (AE F E)ˣ).1 = GlobalTheory.AdelicU.compInf F E w h.1 := by
    intro w
    have := congrArg Units.val (hb w)
    simp only [GlobalTheory.Doubling.unitInf, Units.coe_map, Units.val_one] at this
    rw [Units.val_mul, map_mul]
    erw [this, one_mul]
  have hi : ∀ i, (GlobalTheory.IdeleDecay.coord F E (b * h : (AE F E)ˣ).1 i).1 = (GlobalTheory.IdeleDecay.coord F E h.1 i).1 := by
    intro i
    funext w
    have := GlobalTheory.IdeleSizeUnit.coord_inf F E w (b * h : (AE F E)ˣ).1 i
    rw [hc w, ← GlobalTheory.IdeleSizeUnit.coord_inf F E w h.1 i] at this
    exact this
  unfold GlobalTheory.IdeleDecay.size
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold evI
  rw [hi i]
