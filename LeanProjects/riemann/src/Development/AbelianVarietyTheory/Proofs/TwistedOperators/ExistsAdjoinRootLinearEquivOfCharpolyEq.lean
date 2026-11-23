import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll

theorem exists_linearEquiv_mulVec_of_charpoly (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (P : PPol σ n) (A : Matrix (Fin n) (Fin n) E) (hA : A.charpoly = P.1) :
    ∃ φ : Fld P ≃ₗ[E] (Fin n → E), ∀ y, A *ᵥ φ y = φ (alpha P * y) := by

  let ψ : Fld P →ₐ[E] Matrix (Fin n) (Fin n) E :=
    Ideal.Quotient.liftₐ (Ideal.span {P.1}) (Polynomial.aeval A) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, ← hA, Matrix.aeval_self_charpoly, mul_zero])
  have hψα : ψ (alpha P) = A := by
    change Polynomial.aeval A Polynomial.X = A
    exact Polynomial.aeval_X A

  have hdim : Module.finrank E (Fld P) = n := by
    have h1 := (AdjoinRoot.powerBasis P.2.2.1.ne_zero).finrank
    rw [AdjoinRoot.powerBasis_dim] at h1
    exact h1.trans P.2.2.2.1
  have hpos : 0 < n := hdim ▸ Module.finrank_pos
  haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → E)
  let f : Fld P →ₗ[E] (Fin n → E) :=
    { toFun := fun y => ψ y *ᵥ v
      map_add' := fun y z => by simp [Matrix.add_mulVec]
      map_smul' := fun c y => by simp [Matrix.smul_mulVec] }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    by_contra hne
    apply hv
    have h1 : ψ y⁻¹ * ψ y = 1 := by rw [← map_mul, inv_mul_cancel₀ hne, map_one]
    have h2 : ψ y *ᵥ v = 0 := hy
    calc v = (ψ y⁻¹ * ψ y) *ᵥ v := by rw [h1, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero]
  refine ⟨LinearMap.linearEquivOfInjective f hinj (by rw [hdim, Module.finrank_fin_fun]), fun y => ?_⟩
  simp only [LinearMap.linearEquivOfInjective_apply]
  change A *ᵥ (ψ y *ᵥ v) = ψ (alpha P * y) *ᵥ v
  rw [map_mul, hψα, Matrix.mulVec_mulVec]

end GlobalTheory.TrEll
