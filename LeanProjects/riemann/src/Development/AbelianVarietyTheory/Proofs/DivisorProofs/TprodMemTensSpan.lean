import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.RealLift

namespace GlobalTheory.KFixIrr

def chiOne (P Q R S : ℕ) (x : ℚ) : Submodule ℂ (Formalism.BasicNotions.TH.Pol P Q R S) :=
  ⨅ X : {X : Mat P Q // IsKC X}, LinearMap.ker (fockAct1 P Q R S X.1 - ((x : ℂ) * X.1.trace) • 1)

theorem mem_chiOne {P Q R S : ℕ} (x : ℚ) (f : Formalism.BasicNotions.TH.Pol P Q R S) :
    f ∈ chiOne P Q R S x ↔ ∀ X : Mat P Q, IsKC X → fockAct1 P Q R S X f = ((x : ℂ) * X.trace) • f := by
  simp only [chiOne, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero, Subtype.forall]

def lowOne (P Q R S : ℕ) (x : ℚ) (d : ℕ) : Submodule ℂ (Formalism.BasicNotions.TH.Pol P Q R S) :=
  chiOne P Q R S x ⊓ MvPolynomial.restrictTotalDegree (Ln P Q R S) ℂ d

theorem mem_lowOne {P Q R S : ℕ} (x : ℚ) (d : ℕ) (f : Formalism.BasicNotions.TH.Pol P Q R S) :
    f ∈ lowOne P Q R S x d ↔ f ∈ chiOne P Q R S x ∧ f.totalDegree ≤ d := by
  rw [lowOne, Submodule.mem_inf, MvPolynomial.mem_restrictTotalDegree]

def tensSpan {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (H : ι → Submodule ℂ V) :
    Submodule ℂ (⨂[ℂ] _ : ι, V) :=
  Submodule.span ℂ {T | ∃ f : ι → V, (∀ w, f w ∈ H w) ∧ T = PiTensorProduct.tprod ℂ f}

theorem tprod_mem_tensSpan {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (H : ι → Submodule ℂ V)
    (f : ι → V) (hf : ∀ w, f w ∈ H w) : PiTensorProduct.tprod ℂ f ∈ tensSpan H :=
  Submodule.subset_span ⟨f, hf, rfl⟩

end GlobalTheory.KFixIrr

end
