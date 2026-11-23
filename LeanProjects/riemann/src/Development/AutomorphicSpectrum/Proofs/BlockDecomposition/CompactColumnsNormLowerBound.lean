import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.GA
open scoped NumberField.AdeleRing Classical

namespace GlobalTheory.CompanionTheory.AdelicColumnK

def trGL {n : ℕ} {R : Type*} [CommRing R] (m : GL (Fin n) R) : GL (Fin n) R :=
  ⟨(m : Matrix (Fin n) (Fin n) R)ᵀ, ((m⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ,
    by rw [← transpose_mul, Units.inv_mul, transpose_one],
    by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩

theorem continuous_trGL {n : ℕ} {R : Type*} [CommRing R] [TopologicalSpace R] :
    Continuous (trGL : GL (Fin n) R → GL (Fin n) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val (M := Matrix (Fin n) (Fin n) R)).matrix_transpose
  · exact (Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) R)).matrix_transpose

theorem single_vecMul_trGL {n : ℕ} {R : Type*} [CommRing R] (m : GL (Fin n) R) (j : Fin n) :
    (Pi.single j (1 : R) : Fin n → R) ᵥ* ((trGL m : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      fun i => (m : Matrix (Fin n) (Fin n) R) i j := by
  ext i
  simp [trGL]

theorem column_bound :
    ∀ (K : Type) [Field K] [NumberField K] (C : Set (AdelicGLn.AdelicGL K 3)), IsCompact C →
      ∃ ε : ℝ, 0 < ε ∧ ∀ m ∈ C, ∀ j : Fin 3,
        Reduction.HasFiniteContent (fun i => (m : Matrix (Fin 3) (Fin 3) 𝔸[K]) i j) ∧
          ε ≤ Reduction.adelicNorm (fun i => (m : Matrix (Fin 3) (Fin 3) 𝔸[K]) i j) := by
  intro K _ _ C hC
  obtain ⟨ε, hε, h⟩ := Reduction.exists_pos_le_height (hC.image continuous_trGL)
  refine ⟨ε, hε, fun m hm j => ?_⟩
  have hcol := single_vecMul_trGL m j
  constructor
  · rw [← hcol]
    exact (Reduction.hasFiniteContent_single_one j).vecMul (trGL m)
  · have hx : (Pi.single j (1 : K) : Fin 3 → K) ≠ 0 := by
      intro h0
      simpa using congrFun h0 j
    have := h (trGL m) ⟨m, hm, rfl⟩ _ hx
    rw [Reduction.height, Reduction.ratVec_single_one] at this
    rwa [← hcol]

end GlobalTheory.CompanionTheory.AdelicColumnK
