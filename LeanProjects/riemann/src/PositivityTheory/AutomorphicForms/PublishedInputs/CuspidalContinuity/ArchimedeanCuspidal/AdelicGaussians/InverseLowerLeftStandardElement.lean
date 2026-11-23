import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair)
open scoped NumberField.AdeleRing

namespace Ad3.GA.YVp

def g0 (b : ℚˣ) (u : ℚ) : GL (Fin 2) ℚ :=
  ⟨!![0, 1; (b : ℚ), b * u], !![-u, ((b⁻¹ : ℚˣ) : ℚ); 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

instance countable_matrix2_number_field : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))

instance countable_GL2_number_field : Countable (GL (Fin 2) ℚ) := Units.val_injective.countable

instance countable_principal : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) :=
  Set.Countable.to_subtype ((Set.countable_range (algebraMap ℚ 𝔸[ℚ])).mono fun _ hx => hx)

section W

variable {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) {W : G3 → ℂ} (hW : W ∈ V)
include hV hW

end W

def gq (p : ℚˣ × ℚ) : NQ := Quotient.mk (QuotientGroup.rightRel nU) (g0 p.1 p.2)

section Main

variable {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) {W : G3 → ℂ} (hW : W ∈ V)
include hV hW

end Main

instance nontrivial_adele : Nontrivial 𝔸[ℚ] := by
  refine nontrivial_of_ne (0 : 𝔸[ℚ]) 1 fun h => adelicChar_ne_one (K := ℚ) (DFunLike.ext _ _ fun x => ?_)
  have hx : x = 0 := by rw [← mul_one x, ← h, mul_zero]
  rw [hx, AddChar.map_zero_eq_one, AddChar.one_apply]

section Main2

variable {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) {W : G3 → ℂ} (hW : W ∈ V)
include hV hW

end Main2

end Ad3.GA.YVp

namespace Ad3.GA

open YVp

end Ad3.GA
