import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Adapted

variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem facts (eqv : n ≃ m) (I : Matrix m m ℂ) (hI : I * I = 1) (G : Matrix n n ℂ) (e : ℂ) (he : e * e = 1)
    (A : Matrix n m ℂ) (hA : Aᴴ * (e • G) * A = I) (c : Matrix m n ℂ) (hc : c = I * Aᴴ * (e • G)) :
    c * A = 1 ∧ A * c = 1 ∧ (cᴴ * c).PosDef ∧ (cᴴ * c) * G⁻¹ * (cᴴ * c) = G ∧
    (∀ a ai : Matrix n n ℂ, a * ai = 1 → aᴴ * G * a = G →
      (a * A)ᴴ * (e • G) * (a * A) = I ∧ I * (a * A)ᴴ * (e • G) = c * ai ∧
      (c * (a * A))ᴴ * I * (c * (a * A)) = I ∧
      ((c * (a * A))ᴴ * (c * (a * A)) = 1 ↔ aᴴ * (cᴴ * c) * a = cᴴ * c)) ∧
    ∀ A' : Matrix n m ℂ, A'ᴴ * (e • G) * A' = I → (A' * c)ᴴ * G * (A' * c) = G := by
  have hee : ∀ X : Matrix n n ℂ, e • e • X = X := fun X => by rw [smul_smul, he, one_smul]
  have h1 : c * A = 1 := by
    calc c * A = I * (Aᴴ * (e • G) * A) := by rw [hc]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA, hI]
  have h2 : A * c = 1 := (Matrix.mul_eq_one_comm_of_equiv eqv.symm).1 h1
  have h1h : Aᴴ * cᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have h2h : cᴴ * Aᴴ = 1 := by rw [← conjTranspose_mul, h2, conjTranspose_one]
  have hS : cᴴ * I * c = e • G := by
    calc cᴴ * I * c = cᴴ * (Aᴴ * (e • G) * A) * c := by rw [hA]
      _ = (cᴴ * Aᴴ) * (e • G) * (A * c) := by simp only [Matrix.mul_assoc]
      _ = e • G := by rw [h2h, h2, Matrix.one_mul, Matrix.mul_one]
  have hSX : (e • G) * (A * I * Aᴴ) = 1 := by
    calc (e • G) * (A * I * Aᴴ) = cᴴ * I * (c * A) * I * Aᴴ := by
          rw [← hS]; simp only [Matrix.mul_assoc]
      _ = cᴴ * (I * I) * Aᴴ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hI, Matrix.mul_one, h2h]
  have hGX : G * (e • (A * I * Aᴴ)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul]; exact hSX
  have hGinv : G⁻¹ = e • (A * I * Aᴴ) := Matrix.inv_eq_right_inv hGX
  have hc_inj : Function.Injective c.mulVec := by
    intro v w hvw
    have := congrArg A.mulVec hvw
    simpa [Matrix.mulVec_mulVec, h2] using this
  refine ⟨h1, h2, Matrix.PosDef.conjTranspose_mul_self c hc_inj, ?_, ?_, ?_⟩
  · calc (cᴴ * c) * G⁻¹ * (cᴴ * c) = e • (cᴴ * (c * A) * I * (Aᴴ * cᴴ) * c) := by
          rw [hGinv, Matrix.mul_smul, Matrix.smul_mul]; simp only [Matrix.mul_assoc]
      _ = e • (cᴴ * I * c) := by rw [h1, h1h, Matrix.mul_one, Matrix.mul_one]
      _ = G := by rw [hS, hee]
  · intro a ai hai ha
    have hia : ai * a = 1 := mul_eq_one_comm.1 hai
    have hSa : aᴴ * (e • G) * a = e • G := by rw [Matrix.mul_smul, Matrix.smul_mul, ha]
    have haS : aᴴ * (e • G) = (e • G) * ai := by
      calc aᴴ * (e • G) = aᴴ * (e • G) * (a * ai) := by rw [hai, Matrix.mul_one]
        _ = (aᴴ * (e • G) * a) * ai := by simp only [Matrix.mul_assoc]
        _ = (e • G) * ai := by rw [hSa]
    have hform : (a * A)ᴴ * (e • G) * (a * A) = I := by
      calc (a * A)ᴴ * (e • G) * (a * A) = Aᴴ * (aᴴ * (e • G) * a) * A := by
            rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = I := by rw [hSa, hA]
    refine ⟨hform, ?_, ?_, ?_⟩
    · calc I * (a * A)ᴴ * (e • G) = I * Aᴴ * (aᴴ * (e • G)) := by
            rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = c * ai := by rw [haS, hc]; simp only [Matrix.mul_assoc]
    · calc (c * (a * A))ᴴ * I * (c * (a * A)) = (a * A)ᴴ * (cᴴ * I * c) * (a * A) := by
            rw [conjTranspose_mul c]; simp only [Matrix.mul_assoc]
        _ = I := by rw [hS, hform]
    · have hu : (c * (a * A))ᴴ * (c * (a * A)) = Aᴴ * (aᴴ * (cᴴ * c) * a) * A := by
        rw [conjTranspose_mul c, conjTranspose_mul a]; simp only [Matrix.mul_assoc]
      rw [hu]
      constructor
      · intro h
        calc aᴴ * (cᴴ * c) * a = (cᴴ * Aᴴ) * (aᴴ * (cᴴ * c) * a) * (A * c) := by
              rw [h2h, h2, Matrix.one_mul, Matrix.mul_one]
          _ = cᴴ * (Aᴴ * (aᴴ * (cᴴ * c) * a) * A) * c := by simp only [Matrix.mul_assoc]
          _ = cᴴ * c := by rw [h, Matrix.mul_one]
      · intro h
        calc Aᴴ * (aᴴ * (cᴴ * c) * a) * A = (Aᴴ * cᴴ) * (c * A) := by
              rw [h]; simp only [Matrix.mul_assoc]
          _ = 1 := by rw [h1h, h1, Matrix.one_mul]
  · intro A' hA'
    have hX : e • ((A' * c)ᴴ * G * (A' * c)) = e • G := by
      calc e • ((A' * c)ᴴ * G * (A' * c)) = cᴴ * (A'ᴴ * (e • G) * A') * c := by
            rw [conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul]
            simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
        _ = e • G := by rw [hA', hS]
    calc (A' * c)ᴴ * G * (A' * c) = e • e • ((A' * c)ᴴ * G * (A' * c)) := (hee _).symm
      _ = G := by rw [hX, hee]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Adapted

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem sgI_mul_self (j j' : ℕ) : sgI j j' * sgI j j' = 1 := by
  simp [sgI, Matrix.fromBlocks_multiply]

theorem cinv_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (τ : Ψ) (A : Matrix (Fin (j + j')) (Sg j j') ℂ), Aᴴ * C.sgr τ * A = sgI j j' → C.cinv A τ * A = 1 ∧ A * C.cinv A τ = 1 ∧ ((C.cinv A τ)ᴴ * C.cinv A τ).PosDef ∧ ((C.cinv A τ)ᴴ * C.cinv A τ) * (C.gr τ)⁻¹ * ((C.cinv A τ)ᴴ * C.cinv A τ) = C.gr τ ∧ (∀ a ai : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, a * ai = 1 → aᴴ * C.gr τ * a = C.gr τ → (a * A)ᴴ * C.sgr τ * (a * A) = sgI j j' ∧ C.cinv (a * A) τ = C.cinv A τ * ai ∧ IsSgU (C.cinv A τ * (a * A)) ∧ ((C.cinv A τ * (a * A))ᴴ * (C.cinv A τ * (a * A)) = 1 ↔ aᴴ * ((C.cinv A τ)ᴴ * C.cinv A τ) * a = (C.cinv A τ)ᴴ * C.cinv A τ)) ∧ ∀ A' : Matrix (Fin (j + j')) (Sg j j') ℂ, A'ᴴ * C.sgr τ * A' = sgI j j' → (A' * C.cinv A τ)ᴴ * C.gr τ * (A' * C.cinv A τ) = C.gr τ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C τ A hA
  have he : ((C.eps τ : ℝ) : ℂ) * ((C.eps τ : ℝ) : ℂ) = 1 := by
    have h := C.eps_sq τ
    rw [← Complex.ofReal_mul, ← pow_two, h, Complex.ofReal_one]
  exact Adapted.facts finSumFinEquiv.symm (sgI j j') (sgI_mul_self j j') (C.gr τ) ((C.eps τ : ℝ) : ℂ) he A hA
    (C.cinv A τ) rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
