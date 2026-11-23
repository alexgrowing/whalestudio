import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair)
open scoped NumberField.AdeleRing

namespace Ad3.K.GA.YVp

variable {K : Type} [Field K] [NumberField K]

def g0 (b : Kˣ) (u : K) : GL (Fin 2) K :=
  ⟨!![0, 1; (b : K), b * u], !![-u, ((b⁻¹ : Kˣ) : K); 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

instance countable_field : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable

instance countable_matrix2_number_field : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))

instance countable_GL2_number_field : Countable (GL (Fin 2) K) := Units.val_injective.countable

instance countable_principal : Countable (AdeleRing.principalSubgroup (𝓞 K) K) :=
  Set.Countable.to_subtype ((Set.countable_range (algebraMap K 𝔸[K])).mono fun _ hx => hx)

section W

variable {V : Submodule ℂ (G3K K → ℂ)} (hV : WhAK V) {W : G3K K → ℂ} (hW : W ∈ V)
include hV hW

end W

def gq (p : Kˣ × K) : NQ K := Quotient.mk (QuotientGroup.rightRel (nU K)) (g0 p.1 p.2)

section Main

variable {V : Submodule ℂ (G3K K → ℂ)} (hV : WhAK V) {W : G3K K → ℂ} (hW : W ∈ V)
include hV hW

end Main

instance nontrivial_adele : Nontrivial 𝔸[K] := by
  refine nontrivial_of_ne (0 : 𝔸[K]) 1 fun h => adelicChar_ne_one (K := K) (DFunLike.ext _ _ fun x => ?_)
  have hx : x = 0 := by rw [← mul_one x, ← h, mul_zero]
  rw [hx, AddChar.map_zero_eq_one, AddChar.one_apply]

section Main2

variable {V : Submodule ℂ (G3K K → ℂ)} (hV : WhAK V) {W : G3K K → ℂ} (hW : W ∈ V)
include hV hW

end Main2

end Ad3.K.GA.YVp

namespace Ad3.K.GA

variable {K : Type} [Field K] [NumberField K]

open YVp

end Ad3.K.GA
