import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckDeformationOfLifting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedSquareZeroAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilpotentDividedPowersStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTDeform

theorem connectedSpace_sp_of_local (C : Type) [CommRing C] [IsLocalRing C] : ConnectedSpace (Sp C) := by
  have : PreconnectedSpace (PrimeSpectrum C) := by
    refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint C) fun y _ ↦
      ⟨closure {y}, Set.subset_univ _, ?_, subset_closure rfl, isPreconnected_singleton.closure⟩⟩
    exact (IsLocalRing.specializes_closedPoint y).mem_closure
  have : ConnectedSpace (PrimeSpectrum C) := ⟨inferInstance⟩
  exact this

theorem exists_lift_oAct : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) → (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) → (∀ (c : D.O), ∀ d ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ E) → ∃ (A : Over (Sp C)) (_ : GrpObj A) (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i) (act : GlobalTheory.UPel.HT.OActN D.O A), IsAbelianScheme A ∧ liftFil (divided₂ hsq) h = E ∧ ∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ E hE hFil hstab
  have GD := GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.T.abelianScheme_firstDeRham_structure GlobalTheory.T.print_abelianLifting
  have hκ := isDPNilpotent_squareZero hsq
  obtain ⟨A₁, _, i₁, h₁, hA₁⟩ := GlobalTheory.T.abelianScheme_unobstructed_squareZero_affine C (RingHom.ker π) hsq C₀ π hπ rfl o₀.A o₀.ab
  haveI := hA₁.smooth
  haveI := hA₁.geomConnected
  haveI := connectedSpace_sp_of_local C
  haveI : ConnectedSpace A₁.left := GeometricallyConnected.connectedSpace A₁.hom A₁.hom.isOpenMap
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected A₁.hom (Classical.arbitrary _)
  obtain ⟨A, _, i, h, hA, hgA, hE'⟩ :=
    GlobalTheory.RMDeform.exists_lift_abelian GD GlobalTheory.T.abelianScheme_firstDeRham_structure (divided₂ hsq) hκ π hπ rfl h₁ hA₁ hg E hE hFil
  haveI : IsCommMonObj A := hA.comm
  have HL := (GD C _ (divided₂ hsq) hκ C₀ π hπ rfl).2.2
  have key : ∀ c : D.O, ∃! f : A ⟶ A, IsMonHom f ∧ i ≫ f.left = (o₀.act.act c).left ≫ i := fun c ↦ by
    haveI := o₀.act.hom c
    exact HL g o₀.A A i h hA hgA g o₀.A A i h hA hgA (o₀.act.act c) (fun d hd ↦ by
      rw [hE'] at hd ⊢; exact hstab c d hd)
  choose f hf huniq using key
  refine ⟨A, inferInstance, i, h, ⟨f, fun c ↦ (hf c).1, ?_, ?_, ?_⟩, hA, hE', fun c ↦ (hf c).2.symm⟩
  · refine (huniq 1 (𝟙 _) ⟨inferInstance, ?_⟩).symm
    rw [o₀.act.one]
    simp
  · intro x y
    haveI := (hf x).1
    haveI := (hf y).1
    refine (huniq (x * y) (f y ≫ f x) ⟨inferInstance, ?_⟩).symm
    rw [o₀.act.mul, Over.comp_left, Over.comp_left, ← Category.assoc, (hf y).2, Category.assoc, (hf x).2,
      Category.assoc]
  · intro x y
    haveI := (hf x).1
    haveI := (hf y).1
    refine (huniq (x + y) (f x * f y) ⟨GlobalTheory.OActLift.isMonHom_mul_of_comm _ _, ?_⟩).symm
    rw [o₀.act.add]
    let j : Over.mk (o₀.A.hom ≫ spMap π) ⟶ A := Over.homMk i h.1.w
    have e := h.2 o₀.A (o₀.act.act x) (o₀.act.act y) (j ≫ f x) (j ≫ f y) (hf x).2 (hf y).2
    rw [← MonObj.comp_mul] at e
    exact e

end GlobalTheory.HTDeform
