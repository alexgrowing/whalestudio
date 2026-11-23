import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLinearLiftOfAbelianEndomorphismStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.ExpLin

theorem exists_ringHom_matrix_lift : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ) (O : Type) [Ring O] (act : O → (G ⟶ G)), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsExp y e → ∃ ρ' : O →+* Matrix (Fin g) (Fin g) ℂ, ∀ a z, e (ρ' a *ᵥ z) = e z ≫ act a := by
  intro X G _ _ g O _ act hab hsm hhom h1 hmul hadd y e he
  have H := fun a => GlobalTheory.T.existsUnique_linear_lift_of_abelianEndomorphism X G g hab hsm y e e (act a) he he (hhom a)
  let M : O → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun a => (H a).exists.choose
  have hM : ∀ a z, e (M a z) = e z ≫ act a := fun a => (H a).exists.choose_spec
  have key : ∀ a (N : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ z, e (N z) = e z ≫ act a) → N = M a :=
    fun a N hN => (H a).unique hN (hM a)
  have M1 : M 1 = LinearMap.id := (key 1 LinearMap.id (fun z => by simp [h1])).symm
  have Mmul : ∀ a b, M (a * b) = M a ∘ₗ M b := fun a b =>
    (key (a * b) (M a ∘ₗ M b) (fun z => by
      simp only [LinearMap.comp_apply, hM, hmul, Category.assoc])).symm
  have Madd : ∀ a b, M (a + b) = M a + M b := fun a b =>
    (key (a + b) (M a + M b) (fun z => by
      rw [LinearMap.add_apply, he.1, hM, hM, hadd, MonObj.comp_mul])).symm
  let f : O →* Matrix (Fin g) (Fin g) ℂ :=
    { toFun := fun a => LinearMap.toMatrix' (M a)
      map_one' := by simp only [M1, LinearMap.toMatrix'_id]
      map_mul' := fun a b => by simp only [Mmul, LinearMap.toMatrix'_comp] }
  refine ⟨RingHom.mk' f (fun a b => by simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Madd, map_add]), ?_⟩
  intro a z
  show e (LinearMap.toMatrix' (M a) *ᵥ z) = _
  rw [LinearMap.toMatrix'_mulVec, hM]

end GlobalTheory.ExpLin
