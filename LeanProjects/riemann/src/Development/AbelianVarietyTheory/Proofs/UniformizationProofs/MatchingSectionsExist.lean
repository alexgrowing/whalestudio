import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.SameB

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UnitSec

section Gen
variable {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_pull {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (h : Y' ⟶ Y)
    (hφ : ∀ k, φ' k = h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  exact ⟨_, fun Z r z J hJ => DVR.SectionScalarValuation.sval_pullSec φ ε s h r z hJ⟩

theorem exists_push {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (h : Y' ⟶ Y) (g : Y ⟶ Y')
    (h₁ : g ≫ h = 𝟙 Y) (h₂ : h ≫ g = 𝟙 Y')
    (hφ : ∀ k, φ' k = h ≫ φ k) (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain ⟨s, hs⟩ := exists_pull (φ' := φ) g
    (fun k => by rw [hφ k, ← Category.assoc, h₁, Category.id_comp]) s'
  refine ⟨s, fun Z r z J hJ => ?_⟩
  rw [hs Z _ z J hJ, Category.assoc, h₂, Category.comp_id]

end Gen

theorem unit_inv_snd {S : Scheme.{0}} (G : Over S) :
    (λ_ G).inv.left ≫ (snd (𝟙_ (Over S)) G).left = 𝟙 G.left := by
  rw [← Over.comp_left, leftUnitor_inv_snd, Over.id_left]

theorem snd_unit_inv {S : Scheme.{0}} (G : Over S) :
    (snd (𝟙_ (Over S)) G).left ≫ (λ_ G).inv.left = 𝟙 (𝟙_ (Over S) ⊗ G).left := by
  rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]

theorem famφT_eq {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (α : D.X) (k : Fin 4) : famφT D T α k = (snd T D.P.A).left ≫ D.famφB α k := by
  fin_cases k
  · change (snd T D.P.A).left = (snd T D.P.A).left ≫ 𝟙 _
    rw [Category.comp_id]
  · change (padd D.P.A (snd T D.P.A) (toUnit _ ≫ D.c α)).left =
      (snd T D.P.A).left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left
    rw [← Over.comp_left]; congr 1
    simp only [padd]
    rw [← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
  · change (toUnit (T ⊗ D.P.A) ≫ D.c α).left = (snd T D.P.A).left ≫ (toUnit D.P.A ≫ D.c α).left
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  · change (toUnit (T ⊗ D.P.A) ≫ η[D.P.A]).left = (snd T D.P.A).left ≫ (toUnit D.P.A ≫ η[D.P.A]).left
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]

theorem same_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (G : Over (Spec (CommRingCat.of R))) (L : LB G.left), L.IsLB → ∀ k : ℕ, (∀ σ : H0 L k, ∃ σ', SameG σ σ') ∧ (∀ σ', ∃ σ : H0 L k, SameG σ σ') ∧ (∀ f : ∀ α, D.SecB k α, ∃ f', SameB f f') ∧ ∀ f', ∃ f : ∀ α, D.SecB k α, SameB f f' := by
  intro R _ _ D G L _ k
  refine ⟨fun σ => ?_, fun σ' => ?_, fun f => ?_, fun f' => ?_⟩
  · exact exists_pull (snd _ G).left (fun _ => (Category.comp_id _).symm) σ
  · exact exists_push (φ := fun _ : Fin 1 => 𝟙 G.left) (snd _ G).left (λ_ G).inv.left (unit_inv_snd G)
      (snd_unit_inv G) (fun _ => (Category.comp_id _).symm) σ'
  · choose f' hf' using fun α => exists_pull (snd _ D.P.A).left (famφT_eq D (𝟙_ _) α) (f α)
    exact ⟨f', hf'⟩
  · choose f hf using fun α => exists_push (snd _ D.P.A).left (λ_ D.P.A).inv.left (unit_inv_snd _)
      (snd_unit_inv _) (famφT_eq D (𝟙_ _) α) (f' α)
    exact ⟨f, hf⟩

end GlobalTheory.UnitSec
end
