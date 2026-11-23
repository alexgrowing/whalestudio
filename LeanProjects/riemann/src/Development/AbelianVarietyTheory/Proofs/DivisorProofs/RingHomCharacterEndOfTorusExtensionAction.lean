import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisAltTail
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusMapOfCharHom
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory
namespace TorusActRing

theorem chV_id_eq {k : Type} [Field k] (X : Type) [AddCommGroup X] (χ : X) :
    chV (𝟙 (splitTorus (Sp k) X)) χ = charUnit (Sp k) X χ := by
  ext1
  rw [chV_val]
  simp

theorem charUnit_add' {k : Type} [Field k] (X : Type) [AddCommGroup X] (χ ψ : X) :
    charUnit (Sp k) X (χ + ψ) = charUnit (Sp k) X χ * charUnit (Sp k) X ψ := by
  rw [← chV_id_eq, ← chV_id_eq, ← chV_id_eq, chV_add]

end TorusActRing

theorem ringHom_charEnd_of_torusExtension : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (E : TorusExtension G) (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → letI := E.addCommGroup; ∃ ρ : O →+* Module.End ℤ E.X, ∀ a, ∃ τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X, τ ≫ E.i = E.i ≫ act a ∧ ∀ χ, chV τ χ = charUnit (Sp k) E.X (ρ a χ) := by
  intro k _ G _ _ E O _ act hmon h1 hmul hadd
  letI := E.addCommGroup
  have hex := fun a => GlobalTheory.TorusEndChar.main k G E (act a) (hmon a)
  choose ρ₀ hρ₀ using fun a => (hex a).exists
  have uniq : ∀ a (σ : E.X →+ E.X) (τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X),
      τ ≫ E.i = E.i ≫ act a → (∀ χ, chV τ χ = charUnit (Sp k) E.X (σ χ)) → σ = ρ₀ a :=
    fun a σ τ e₁ e₂ => (hex a).unique ⟨τ, e₁, e₂⟩ (hρ₀ a)
  have compχ : ∀ (σ : E.X →+ E.X) (τ : splitTorus (Sp k) E.X ⟶ splitTorus (Sp k) E.X),
      (∀ χ, chV τ χ = charUnit (Sp k) E.X (σ χ)) → ∀ (Z : Over (Sp k)) (s : Z ⟶ splitTorus (Sp k) E.X) χ,
      chV (s ≫ τ) χ = chV s (σ χ) :=
    fun σ τ hτ Z s χ => ((splitTorus_map_of_charHom (Sp k) E.X E.X σ).2 τ hτ).2.2 Z s χ
  have one : ρ₀ 1 = AddMonoidHom.id _ := by
    refine (uniq 1 (AddMonoidHom.id _) (𝟙 _) ?_ (fun χ => ?_)).symm
    swap
    · rw [AddMonoidHom.id_apply]; exact TorusActRing.chV_id_eq E.X χ
    rw [h1, Category.id_comp, Category.comp_id]
  have mul : ∀ a b, ρ₀ (a * b) = (ρ₀ a).comp (ρ₀ b) := by
    intro a b
    obtain ⟨τa, ha1, ha2⟩ := hρ₀ a
    obtain ⟨τb, hb1, hb2⟩ := hρ₀ b
    refine (uniq (a * b) _ (τa ≫ τb) ?_ ?_).symm
    · rw [Category.assoc, hb1, ← Category.assoc, ha1, Category.assoc, hmul]
    · intro χ
      rw [compχ _ τb hb2, ha2]
      rfl
  have add : ∀ a b, ρ₀ (a + b) = ρ₀ a + ρ₀ b := by
    intro a b
    obtain ⟨τa, ha1, ha2⟩ := hρ₀ a
    obtain ⟨τb, hb1, hb2⟩ := hρ₀ b
    haveI := E.i_hom
    refine (uniq (a + b) _ (τa * τb) ?_ ?_).symm
    · rw [MonObj.mul_comp, ha1, hb1, hadd, Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]
    · intro χ
      rw [chV_mul, ha2, hb2, AddMonoidHom.add_apply, TorusActRing.charUnit_add']
  have zero : ρ₀ 0 = 0 := by
    have := add 0 0
    rw [add_zero] at this
    simpa using this
  refine ⟨{ toFun := fun a => (ρ₀ a).toIntLinearMap
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun a => ?_⟩
  · ext x; simp [one]
  · intro a b; ext x; simp [mul]
  · ext x; simp [zero]
  · intro a b; ext x; simp [add]
  · obtain ⟨τ, e₁, e₂⟩ := hρ₀ a
    exact ⟨τ, e₁, fun χ => e₂ χ⟩

end GlobalTheory
