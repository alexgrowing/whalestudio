import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem sig_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) (ρ : B →ₐ[R] B') (φ : B₀ →ₐ[R₀] B₀'), (∀ b, p' (ρ b) = φ (p b)) → ∀ (σ : R₁ ⊗[R₀] B₀ →+ B) (σ' : R₁ ⊗[R₀] B₀' →+ B'), α.IsSig p σ → α.IsSig p' σ' → (∀ y, ρ (σ y) = σ' (extHom R₁ φ y)) ∧ ∀ y, α.KerQ y → α.KerQ (extHom R₁ φ y) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker B' B₀' _ _ _ _ p' hs' hp' hker' ρ φ hρ σ σ' hσ hσ'
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r b₀ =>
      obtain ⟨b, rfl⟩ := hp b₀
      rw [hσ r b]
      simp only [extHom, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [← hρ b, hσ' r (ρ b), map_smul]
    | add x z hx hz => simp only [map_add, hx, hz]
  · have key : ∀ y : R₁ ⊗[R₀] B₀,
        Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀') (extHom R₁ φ y) =
          Algebra.TensorProduct.map (AlgHom.id R₀ R₀) φ (Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r b₀ => simp [extHom]
      | add x z hx hz => simp only [map_add, hx, hz]
    unfold Aug.KerQ at hy ⊢
    rw [key, hy, map_zero]

end GlobalTheory.Obs
