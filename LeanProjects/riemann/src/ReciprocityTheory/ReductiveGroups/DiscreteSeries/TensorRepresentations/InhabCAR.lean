import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CarSumSqZeroOfAnti

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

abbrev Fock (n : ℕ) := ExteriorAlgebra ℂ (Fin n × Fin n → ℂ)

def cpFock (i a : Fin n) : Module.End ℂ (Fock n) :=
  LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ (Pi.single (i, a) (1 : ℂ)))

def cmFock (i a : Fin n) : Module.End ℂ (Fock n) :=
  CliffordAlgebra.contractLeft (LinearMap.proj (R := ℂ) (φ := fun _ : Fin n × Fin n => ℂ) (i, a))

theorem isCAR_fock : IsCAR (cpFock (n := n)) cmFock := by
  intro i a j b
  refine ⟨?_, ?_, ?_⟩
  · refine LinearMap.ext fun z => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, cpFock, LinearMap.mulLeft_apply,
      LinearMap.zero_apply]
    rw [← mul_assoc, ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul]
  · refine LinearMap.ext fun z => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, cmFock, LinearMap.zero_apply]
    rw [CliffordAlgebra.contractLeft_comm, neg_add_cancel]
  · refine LinearMap.ext fun z => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, cmFock, cpFock, LinearMap.mulLeft_apply]
    rw [CliffordAlgebra.contractLeft_ι_mul, sub_add_cancel]
    by_cases h : i = j ∧ a = b
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [if_neg h]
      have hne : (i, a) ≠ (j, b) := fun e => h ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
      simp [LinearMap.proj_apply, Pi.single_apply, hne]

theorem car_setting_inhabited :
    IsGlRep (0 : Fin n → Fin n → Module.End ℂ (Fock n)) ∧ IsCAR (cpFock (n := n)) cmFock ∧
      CommutesCAR (0 : Fin n → Fin n → Module.End ℂ (Fock n)) cpFock cmFock := by
  refine ⟨fun a b c d => ?_, isCAR_fock, fun a b i j => ?_⟩
  · simp
  · simp

def cpOne : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) := Matrix.toEuclideanLin !![0, 0; 1, 0]

def cmOne : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) := Matrix.toEuclideanLin !![0, 1; 0, 0]

theorem car_one_mode :
    IsCAR (fun _ _ : Fin 1 => cpOne) (fun _ _ : Fin 1 => cmOne) ∧
      ∀ x y : EuclideanSpace ℂ (Fin 2), inner ℂ (cpOne x) y = inner ℂ x (cmOne y) := by
  refine ⟨fun i a j b => ?_, fun x y => ?_⟩
  · have hi : i = j := Subsingleton.elim _ _
    have ha : a = b := Subsingleton.elim _ _
    subst hi; subst ha
    refine ⟨?_, ?_, ?_⟩ <;> refine LinearMap.ext fun x => ?_ <;> ext k <;> fin_cases k <;>
      simp [cpOne, cmOne, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [cpOne, cmOne, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      PiLp.inner_apply, mul_comm]

end ReciprocityTheory.ChartRestriction.DS
