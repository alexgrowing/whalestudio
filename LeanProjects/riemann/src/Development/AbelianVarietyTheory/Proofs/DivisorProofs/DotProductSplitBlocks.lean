import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictionAndProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntAddConjEqOneOfBaseGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosHomApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.AdaptEv
open scoped GlobalTheory.VacAny

namespace GlobalTheory.ThK.AdaptEv

theorem dotProduct_split_blocks {κ ι κ₁ R : Type} [Fintype κ] [Fintype ι] [Fintype κ₁] [CommRing R]
    (eq : κ ≃ ι ⊕ κ₁) (u v : κ → R) :
    u ⬝ᵥ v = (fun i => u (eq.symm (Sum.inl i))) ⬝ᵥ (fun i => v (eq.symm (Sum.inl i))) +
      (fun j => u (eq.symm (Sum.inr j))) ⬝ᵥ (fun j => v (eq.symm (Sum.inr j))) := by
  simp only [dotProduct]
  rw [← eq.symm.sum_comp, Fintype.sum_sum_type]

theorem schroedinger_ext_zero_product_vacuum {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ ι κ₁ : Type} [Fintype κ] [Fintype ι] [Fintype κ₁]
    (eq : κ ≃ ι ⊕ κ₁) (α β : κ → R) (a b : κ₁ → R) (A : (ι → R) → ℂ) (φ : (κ₁ → R) → ℂ) :
    (∀ j, α (eq.symm (Sum.inr j)) = 0) → (∀ j, β (eq.symm (Sum.inr j)) = 0) →
    schr ψ (α + ext0 eq a, β + ext0 eq b) (prodVac eq A φ) =
      prodVac eq (schr ψ (fun i => α (eq.symm (Sum.inl i)), fun i => β (eq.symm (Sum.inl i))) A) (schr ψ (a, b) φ) := by
  intro hα hβ
  funext x
  simp only [schr, prodVac]
  rw [dotProduct_split_blocks eq x, dotProduct_split_blocks eq (α + ext0 eq a)]
  simp only [Pi.add_apply, ext0_inl, ext0_inr, hα, hβ, add_zero, zero_add]
  have h1 : (fun i => x (eq.symm (Sum.inl i)) + α (eq.symm (Sum.inl i))) =
      (fun i => x (eq.symm (Sum.inl i))) + (fun i => α (eq.symm (Sum.inl i))) := rfl
  have h2 : (fun j => x (eq.symm (Sum.inr j)) + a j) = (fun j => x (eq.symm (Sum.inr j))) + a := rfl
  have e : (fun i => x (eq.symm (Sum.inl i))) ⬝ᵥ (fun i => β (eq.symm (Sum.inl i))) +
      (fun j => x (eq.symm (Sum.inr j))) ⬝ᵥ b +
      ⅟(2 : R) * ((fun i => α (eq.symm (Sum.inl i))) ⬝ᵥ (fun i => β (eq.symm (Sum.inl i))) + a ⬝ᵥ b) =
      ((fun i => x (eq.symm (Sum.inl i))) ⬝ᵥ (fun i => β (eq.symm (Sum.inl i))) +
        ⅟(2 : R) * ((fun i => α (eq.symm (Sum.inl i))) ⬝ᵥ (fun i => β (eq.symm (Sum.inl i))))) +
      ((fun j => x (eq.symm (Sum.inr j))) ⬝ᵥ b + ⅟(2 : R) * (a ⬝ᵥ b)) := by ring
  rw [h1, h2, e, AddChar.map_add_eq_mul]
  ring

end GlobalTheory.ThK.AdaptEv
