import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar

noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCF

def solStep (c : ℂ) (V : Submodule ℂ (ℝ → ℂ)) : Submodule ℂ (ℝ → ℂ) :=
    { carrier := {f | Differentiable ℝ f ∧ (deriv f - c • f) ∈ V}
      add_mem' := fun {f g} hf hg => by
        refine ⟨hf.1.add hg.1, ?_⟩
        have e : deriv (f + g) - c • (f + g) = (deriv f - c • f) + (deriv g - c • g) := by
          funext x
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          rw [deriv_add (hf.1 x) (hg.1 x)]; ring
        rw [e]; exact add_mem hf.2 hg.2
      zero_mem' := ⟨differentiable_const 0, by
        have e : deriv (0 : ℝ → ℂ) - c • (0 : ℝ → ℂ) = 0 := by
          funext x; simp
        rw [e]; exact zero_mem _⟩
      smul_mem' := fun k f hf => by
        refine ⟨hf.1.const_smul k, ?_⟩
        have e : deriv (k • f) - c • (k • f) = k • (deriv f - c • f) := by
          funext x
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          rw [deriv_const_smul k (hf.1 x)]; simp only [smul_eq_mul]; ring
        rw [e]; exact Submodule.smul_mem _ _ hf.2 }

def expSol (l : List ℂ) : Submodule ℂ (ℝ → ℂ) := l.foldr solStep ⊥

theorem mem_expSol_nil {f : ℝ → ℂ} : f ∈ expSol [] ↔ f = 0 := Submodule.mem_bot ℂ

theorem mem_expSol_cons {c : ℂ} {l : List ℂ} {f : ℝ → ℂ} :
    f ∈ expSol (c :: l) ↔ Differentiable ℝ f ∧ (deriv f - c • f) ∈ expSol l := Iff.rfl

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)

def expCurve (t : ℝ) : GA E a :=
  Matrix.GeneralLinearGroup.scalar (Fin a) (infId E (expU (t • (1 : Cinf E))))

abbrev scalD : Module.End ℂ (Sm E a) := lie E a (Central.scL a 1)

variable {E a}

theorem expCurve_add (s t : ℝ) : expCurve E a (s + t) = expCurve E a s * expCurve E a t := by
  unfold expCurve
  rw [add_smul, expU_add, map_mul, map_mul]

theorem expCurve_zero : expCurve E a 0 = 1 := by
  unfold expCurve
  rw [zero_smul, expU_zero, map_one, map_one]

end GlobalTheory.HCF

end
