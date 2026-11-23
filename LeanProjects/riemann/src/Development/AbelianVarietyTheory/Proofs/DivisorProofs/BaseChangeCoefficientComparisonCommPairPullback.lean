import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensHomTmul
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open Opposite
namespace GlobalTheory.Obs.BC

theorem tensPair_extMap_pairPull : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ Y₀ Y₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (w' : pr' ≫ t₀ = t₁ ≫ spMap (algebraMap R₀ R₁)) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) (e : f₁ ≫ pr = pr' ≫ f₀) (p : (Pair f₀)ᵒᵖ) (b : (ext R₁ (OAff s₀)).obj ((pairSnd f₀).obj p)), (GlobalTheory.Obs.BC.tensPair w' e).α p ((extMap R₁ (pairPull h₀)).α p b) = (pairPull h₁).α ((GlobalTheory.Obs.BC.pairBC pr pr' e).obj p) ((GlobalTheory.Obs.BC.tensCoef w).α ((pairSnd f₀).obj p) b) := by
  intro R₀ R₁ _ _ _ X₀ X₁ Y₀ Y₁ s₀ s₁ pr t₀ t₁ pr' _ _ w w' f₀ f₁ h₀ h₁ e p b
  have key : ∀ (g g' : Y₁ ⟶ X₀) (_ : g = g') (U : X₀.Opens) (V : Y₁.Opens) (k : V ≤ g ⁻¹ᵁ U) (k' : V ≤ g' ⁻¹ᵁ U),
      g.appLE U V k = g'.appLE U V k' := by
    rintro g _ rfl U V k k'; rfl
  change tensHom w' (unop ((pairFst f₀).obj p)) _ (extHom R₁ (coefHom (pairPull h₀) p) b) =
    GlobalTheory.CechDR.secPull s₁ t₁ (pairBCObj pr pr' e p.unop) (tensHom w (unop ((pairSnd f₀).obj p)) _ b)
  induction b using TensorProduct.induction_on with
  | zero => repeat erw [map_zero]
            all_goals exact rfl
  | add x y hx hy => erw [map_add, map_add, map_add, map_add, hx, hy]; exact rfl
  | tmul r x =>
    refine (congrArg (tensHom w' _ _) (Algebra.TensorProduct.map_tmul _ _ r x)).trans ?_
    refine (tensHom_tmul w' _ _ r _).trans ?_
    have h2 := congrArg (GlobalTheory.CechDR.secPull s₁ t₁ (pairBCObj pr pr' e p.unop))
      (tensHom_tmul w (unop ((pairSnd f₀).obj p)) ((isAffine_aff _).preimage pr) r x)
    refine Eq.trans ?_ h2.symm
    refine Eq.trans ?_ (map_mul _ _ _).symm
    congr 1
    · exact ((semiHom_secPull h₁ (pairBCObj pr pr' e p.unop)).map_algebraMap r).symm
    · change (pr'.appLE _ _ _).hom ((f₀.appLE _ _ _).hom x) = (f₁.appLE _ _ _).hom ((pr.appLE _ _ _).hom x)
      have c1 := Scheme.Hom.appLE_comp_appLE pr' f₀ p.unop.1.2.1 p.unop.1.1.1 (pr' ⁻¹ᵁ p.unop.1.1.1) p.unop.2 le_rfl
      have c2 := Scheme.Hom.appLE_comp_appLE f₁ pr p.unop.1.2.1 (pr ⁻¹ᵁ p.unop.1.2.1) (pr' ⁻¹ᵁ p.unop.1.1.1) le_rfl
        (pairBCObj pr pr' e p.unop).2
      rw [key (pr' ≫ f₀) (f₁ ≫ pr) e.symm _ _ _ (by rw [e]; exact pr'.preimage_mono p.unop.2)] at c1
      exact (congrArg (fun t ↦ t.hom x) c1).trans (congrArg (fun t ↦ t.hom x) c2).symm

end GlobalTheory.Obs.BC
