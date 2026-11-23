import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IdeleTate

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def lat : Set (AE F E) :=
  {x | ∀ i v, evFin F v (GlobalTheory.IdeleDecay.coord F E x i) ∈ v.adicCompletionIntegers F}

def stab : Subgroup (AE F E)ˣ where
  carrier := {u | ∀ x, x ∈ lat F E ↔ (u : AE F E) * x ∈ lat F E}
  one_mem' := fun x => by simp
  mul_mem' := fun {a b} ha hb x => by
    show x ∈ lat F E ↔ ((a * b : (AE F E)ˣ) : AE F E) * x ∈ lat F E
    rw [Units.val_mul, mul_assoc, hb x, ha]
  inv_mem' := fun {a} ha x => by
    have := ha (((a⁻¹ : (AE F E)ˣ) : AE F E) * x)
    rw [← mul_assoc, Units.mul_inv, one_mul] at this
    exact this.symm

def absInf (l : (AE F E)ˣ) : ℝ≥0 := ∏ w, GlobalTheory.Doubling.absEw F E w (GlobalTheory.Doubling.unitInf F E w l)

def absFin (l : (AE F E)ˣ) : ℝ≥0 := ∏ᶠ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v l)

variable {F E}

theorem absE_eq (l : (AE F E)ˣ) : absE F E l = absInf F E l * absFin F E l := rfl

theorem absInf_eq_one {b : (AE F E)ˣ} (h : ∀ w, GlobalTheory.Doubling.unitInf F E w b = 1) : absInf F E b = 1 := by
  simp [absInf, h]

end GlobalTheory.IdeleTate
