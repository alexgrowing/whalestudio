import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IdeleDecay

open scoped Classical

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def coord (x : AE F E) : Fin (Module.finrank F E) → AF F :=
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun x

def size (x : AE F E) : ℝ := ∑ i, ‖evI F (coord F E x i)‖

def decay (N m : ℕ) (l : (AE F E)ˣ) : ℝ :=
  if ∀ i v, evFin F v ((m : AF F) * coord F E l.1 i) ∈ v.adicCompletionIntegers F then
    ((1 + size F E l.1) ^ N)⁻¹ else 0

variable {F E}

theorem size_nonneg (x : AE F E) : 0 ≤ size F E x := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem decay_nonneg (N m : ℕ) (l : (AE F E)ˣ) : 0 ≤ decay F E N m l := by
  unfold decay
  split_ifs
  · exact inv_nonneg.mpr (pow_nonneg (add_nonneg zero_le_one (size_nonneg _)) _)
  · exact le_rfl

theorem decay_mono {N m m' : ℕ} (h : m ∣ m') (l : (AE F E)ˣ) : decay F E N m l ≤ decay F E N m' l := by
  obtain ⟨c, rfl⟩ := h
  unfold decay
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso
    apply h2
    intro i v
    have := h1 i v
    rw [Nat.cast_mul, mul_comm (m : AF F) (c : AF F), mul_assoc, map_mul]
    refine mul_mem ?_ this
    rw [map_natCast]
    exact natCast_mem (v.adicCompletionIntegers F) c
  · exact inv_nonneg.mpr (pow_nonneg (add_nonneg zero_le_one (size_nonneg _)) _)
  · exact le_rfl

end GlobalTheory.IdeleDecay
