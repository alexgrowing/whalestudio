import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OActLift

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
set_option autoImplicit false in

theorem _root_.GlobalTheory.OActLift.isMonHom_mul_of_comm {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (f g : G ⟶ G) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) := by
  rw [Hom.mul_def]
  infer_instance

theorem exists_oAct_lift : GlobalTheory.Published.GrothendieckDeformation → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I),
    IsNilDP κ → ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
      (h : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (O : Type) [CommRing O] (a₀ : OAct O A₀), (∀ (x : O), ∀ d ∈ liftFil κ h, act κ (spMap π) a₀ x d ∈ liftFil κ h) →
      ∃ a : OAct O A, ∀ x, (a₀.act x).left ≫ i = i ≫ (a.act x).left := by
  intro GD R R₀ _ _ I κ hκ π hπ hI g A₀ _ A _ i h hA hg O _ a₀ hfil
  have HL := (GD R I κ hκ R₀ π hπ hI).2.2
  haveI : IsCommMonObj A := hA.comm
  have key : ∀ x : O, ∃! f : A ⟶ A, IsMonHom f ∧ i ≫ f.left = (a₀.act x).left ≫ i := fun x ↦ by
    haveI := a₀.hom x
    exact HL g A₀ A i h hA hg g A₀ A i h hA hg (a₀.act x) (fun d hd ↦ hfil x d hd)
  choose f hf huniq using key
  refine ⟨⟨f, fun x ↦ (hf x).1, ?_, ?_, ?_⟩, fun x ↦ (hf x).2.symm⟩
  · refine (huniq 1 (𝟙 _) ⟨inferInstance, ?_⟩).symm
    rw [a₀.one]
    simp
  · intro x y
    haveI := (hf x).1
    haveI := (hf y).1
    refine (huniq (x * y) (f x ≫ f y) ⟨inferInstance, ?_⟩).symm
    rw [a₀.mul, Over.comp_left, Over.comp_left, ← Category.assoc, (hf x).2, Category.assoc, (hf y).2,
      Category.assoc]
  · intro x y
    haveI := (hf x).1
    haveI := (hf y).1
    refine (huniq (x + y) (f x * f y) ⟨isMonHom_mul_of_comm _ _, ?_⟩).symm
    rw [a₀.add]
    let j : Over.mk (A₀.hom ≫ spMap π) ⟶ A := Over.homMk i h.1.w
    have e := h.2 A₀ (a₀.act x) (a₀.act y) (j ≫ f x) (j ≫ f y) (hf x).2 (hf y).2
    rw [← MonObj.comp_mul] at e
    exact e

end GlobalTheory.OActLift
