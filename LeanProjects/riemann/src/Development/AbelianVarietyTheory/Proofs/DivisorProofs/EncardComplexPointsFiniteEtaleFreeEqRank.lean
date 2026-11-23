import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCover
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
open scoped TensorProduct

namespace GlobalTheory.EtaleComplexPoints

theorem encard_complexPoints_eq_rank : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (δ : ℕ), f.Etale → f.Finite → (letI := f.toAlgebra; Module.Free A B ∧ Module.finrank A B = δ) → ∀ φ : A →+* ℂ, {ψ : B →+* ℂ | ψ.comp f = φ}.encard = (δ : ℕ∞) := by
  intro A B _ _ f δ hf hfin hfree φ
  letI := f.toAlgebra
  letI := φ.toAlgebra
  obtain ⟨hF, hrk⟩ := hfree
  have hEt : Algebra.Etale A B := RingHom.etale_algebraMap.1 hf
  have hMF : Module.Finite A B := hfin
  have hFE : Algebra.FormallyEtale ℂ (ℂ ⊗[A] B) := inferInstance
  have hcard := GlobalTheory.natCard_algHom_eq_finrank_of_etale_baseChange A B ℂ
  have hto (ψ : {ψ : B →+* ℂ | ψ.comp f = φ}) (a : A) : ψ.1 (algebraMap A B a) = algebraMap A ℂ a := by
    have := congrArg (fun g : A →+* ℂ => g a) ψ.2
    simpa [RingHom.algebraMap_toAlgebra] using this
  have hinv (g : B →ₐ[A] ℂ) : (g : B →+* ℂ).comp f = φ := by
    ext a
    simpa [RingHom.algebraMap_toAlgebra] using g.commutes a
  let e : {ψ : B →+* ℂ | ψ.comp f = φ} ≃ (B →ₐ[A] ℂ) :=
    { toFun := fun ψ => { ψ.1 with commutes' := hto ψ }
      invFun := fun g => ⟨g.toRingHom, hinv g⟩
      left_inv := fun ψ => rfl
      right_inv := fun g => rfl }
  have hfinite : Finite (B →ₐ[A] ℂ) :=
    Finite.of_equiv _ (AlgHom.liftEquiv A ℂ B ℂ).symm
  rw [Set.encard, ENat.card_congr e, ENat.card_eq_coe_natCard, hcard, hrk]

end GlobalTheory.EtaleComplexPoints
