import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HodgeCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.HodgeCoh
variable {k : Type} [CommRing k] {X X' X'' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k}
  {s'' : X'' ⟶ Sp k} {f : X' ⟶ X} {g : X'' ⟶ X'}

theorem formPull_formPull (hf : f ≫ s = s') (hg : g ≫ s' = s'') (hgf : (g ≫ f) ≫ s = s'')
    (U : X.Opens) (j : ℕ) (x : OmU s U j) :
    formPull hg (f ⁻¹ᵁ U) j (formPull hf U j x) = formPull hgf U j x := by
  refine SemiHom.mOm_mOm (semiHom_appSec hf U) (semiHom_appSec hg (f ⁻¹ᵁ U))
    (semiHom_appSec hgf U) (fun b ↦ ?_) x
  change (f.app U ≫ g.app (f ⁻¹ᵁ U)).hom b = ((g ≫ f).app U).hom b
  rw [Scheme.Hom.comp_app]
  rfl

theorem omega_hom_ext {j : ℕ} {M : X.Modules} (φ ψ : Omega s j ⟶ M)
    (h : ∀ (U : X.Opens) (x : OmU s U j), φ.val.app (op U) ((toOmega s j).app (op U) x) =
      ψ.val.app (op U) ((toOmega s j).app (op U) x)) : φ = ψ := by
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).injective
  have e₁ := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_unit
    (formsPre s j) M φ
  have e₂ := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_unit
    (formsPre s j) M ψ
  refine e₁.trans (Eq.trans ?_ e₂.symm)
  ext U x
  exact h U.unop x

theorem omegaPull_comp (hf : f ≫ s = s') (hg : g ≫ s' = s'') (hgf : (g ≫ f) ≫ s = s'')
    (j : ℕ) :
    omegaPull hgf j = omegaPull hf j ≫ (Scheme.Modules.pushforward f).map (omegaPull hg j) := by
  refine omega_hom_ext _ _ fun U x ↦ ?_
  rw [omegaPull_toOmega]
  change _ = (omegaPull hg j).val.app (op (f ⁻¹ᵁ U)) ((omegaPull hf j).val.app (op U) ((toOmega s j).app (op U) x))
  rw [omegaPull_toOmega, omegaPull_toOmega, formPull_formPull hf hg hgf]
  rfl

theorem hodgePull_comp (hf : f ≫ s = s') (hg : g ≫ s' = s'') (hgf : (g ≫ f) ≫ s = s'')
    (j q : ℕ) (x : hodgeH s j q) :
    hodgePull hg j q (hodgePull hf j q x) = hodgePull hgf j q x := by
  letI := algΓ s; letI := algΓ s'; letI := algΓ s''
  apply (cohOn.toH' (Omega s'' j) ⊤ q).injective
  have e₁ := cohOn.toH'_pull (σ := RingHom.id k) (appTop_algebraMap hg) (omegaPull hg j)
    (le_refl (g ⁻¹ᵁ ⊤)) (hodgePull hf j q x)
  have e₂ := cohOn.toH'_pull (σ := RingHom.id k) (appTop_algebraMap hf) (omegaPull hf j)
    (le_refl (f ⁻¹ᵁ ⊤)) x
  have e₃ := cohOn.toH'_pull (σ := RingHom.id k) (appTop_algebraMap hgf) (omegaPull hgf j)
    (le_refl ((g ≫ f) ⁻¹ᵁ ⊤)) x
  refine e₁.trans (Eq.trans ?_ e₃.symm)
  refine (congrArg (SheafPull.pull.{0, 0} g.base (toAbSheafPush (omegaPull hg j)) q _) e₂).trans ?_
  refine (SheafPull.pull_pull.{0, 0, 0} f.base g.base _ _ q _ _ _).trans ?_
  rw [omegaPull_comp hf hg hgf]
  rfl

theorem hodgePull_hodgePull {X X' X'' : Scheme.{0}} (s : X ⟶ Sp k) (f : X' ⟶ X)
    (g : X'' ⟶ X') (j q : ℕ) (x : hodgeH s j q) :
    hodgePull (s' := g ≫ f ≫ s) rfl j q (hodgePull (s' := f ≫ s) rfl j q x) =
      hodgePull (f := g ≫ f) (s' := g ≫ f ≫ s) (Category.assoc g f s) j q x :=
  hodgePull_comp rfl rfl (Category.assoc g f s) j q x

end GlobalTheory.HodgeCoh

example : ∀ {k : Type} [CommRing k] {X X' X'' : Scheme.{0}} (s : X ⟶ Sp k) (f : X' ⟶ X) (g : X'' ⟶ X') (j q : ℕ) (x : hodgeH s j q), hodgePull (s' := g ≫ f ≫ s) rfl j q (hodgePull (s' := f ≫ s) rfl j q x) = hodgePull (f := g ≫ f) (s' := g ≫ f ≫ s) (Category.assoc g f s) j q x :=
  fun s f g j q x ↦ hodgePull_hodgePull s f g j q x
