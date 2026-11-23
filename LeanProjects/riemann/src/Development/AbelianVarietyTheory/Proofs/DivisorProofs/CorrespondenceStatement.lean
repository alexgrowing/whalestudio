import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Side
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfBijectiveGeomPointsSmoothProjCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SideGenericPointLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SideGenericPointRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuativeLiftUniqueClosedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendGenericPointMorphismOfStalksStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointRelationOfMorphismStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option autoImplicit false

namespace GlobalTheory.ShFam.GalCarry.Corr

theorem side_exists {F : Type} [Field F] [CharZero F] {I I' : Type} {Y : I → Var F} {Y' : I' → Var F}
    (Rel : ∀ (K : Type) [Field K] (i : I) (i' : I'), (Sp K ⟶ (Y i).X) → (Sp K ⟶ (Y' i').X) → Prop) (h : Side Y Y' Rel) (i : I) :
    ∃ (i' : I') (φ : (Y i).X ⟶ (Y' i').X), φ ≫ (Y' i').str = (Y i).str ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (p : Sp K ⟶ (Y i).X), Rel K i i' p (p ≫ φ) := by
  obtain ⟨i', p', hp's, hrel⟩ := GlobalTheory.T.side_generic_point_lift F I I' Y Y' Rel h i
  have hloc : ∀ y : (Y i).X, ∃ l : Sp ((Y i).X.presheaf.stalk y) ⟶ (Y' i').X,
      spMap (algebraMap ((Y i).X.presheaf.stalk y) (Y i).Fn) ≫ l = p' := fun y =>
    GlobalTheory.T.valuative_lift_unique_closed_point F (Y i) (Y' i') p' hp's y (GlobalTheory.T.side_generic_point_relation F I I' Y Y' Rel h i i' p' hrel y)
  obtain ⟨φ, hφ, hφs⟩ := GlobalTheory.T.extend_generic_point_morphism_of_stalks F (Y i) (Y' i') p' hp's hloc
  subst hφ
  exact ⟨i', φ, hφs, GlobalTheory.T.generic_point_relation_of_morphism F I I' Y Y' Rel h i i' φ hφs hrel⟩

end GlobalTheory.ShFam.GalCarry.Corr

namespace GlobalTheory.ShFam.GalCarry

open GlobalTheory.ShFam.GalCarry.Corr in

theorem corrSt : CorrSt := by
  intro F _ _ I I' Y Y' Rel hs hb hu hu' hv
  have h1 : Side Y Y' Rel := ⟨hs, hb, hu, hv⟩
  have h2 : Side Y' Y (fun (K : Type) [Field K] i' i p' p => Rel K i i' p p') :=
    ⟨fun K _ i' i p' p h => (hs K i i' p p' h).symm, fun K K' _ _ ν i' i p' p h => hb K K' ν i i' p p' h,
      fun K _ _ i' p' => hu' K i' p',
      fun V _ _ _ L _ ν k _ r i' i q' q hν hr h => hv V L ν k r i i' q q' hν hr h⟩
  choose f φ hφs hφ using side_exists Rel h1
  choose g ψ hψs hψ using side_exists _ h2
  have gf : ∀ i, g (f i) = i := by
    intro i
    let p : Sp (AlgebraicClosure (Y i).Fn) ⟶ (Y i).X :=
      spMap (algebraMap (Y i).Fn (AlgebraicClosure (Y i).Fn)) ≫ genericPt (Y i)
    obtain ⟨_, _, huq⟩ := hu' _ (f i) (p ≫ φ i)
    have e := (huq ⟨i, p⟩ (hφ i _ p)).trans (huq ⟨g (f i), _⟩ (hψ (f i) _ (p ≫ φ i))).symm
    exact (congrArg Sigma.fst e).symm
  have fg : ∀ i', f (g i') = i' := by
    intro i'
    let p' : Sp (AlgebraicClosure (Y' i').Fn) ⟶ (Y' i').X :=
      spMap (algebraMap (Y' i').Fn (AlgebraicClosure (Y' i').Fn)) ≫ genericPt (Y' i')
    obtain ⟨_, _, huq⟩ := hu _ (g i') (p' ≫ ψ i')
    have e := (huq ⟨f (g i'), _⟩ (hφ (g i') _ (p' ≫ ψ i'))).trans (huq ⟨i', p'⟩ (hψ i' _ p')).symm
    exact congrArg Sigma.fst e
  refine ⟨⟨f, g, gf, fg⟩, fun i => ?_⟩
  have hbij : ∀ (K : Type) [Field K] [IsAlgClosed K],
      Function.Bijective (fun p : Sp K ⟶ (Y i).X => p ≫ φ i) := by
    intro K _ _
    refine ⟨fun p₁ p₂ (e : p₁ ≫ φ i = p₂ ≫ φ i) => ?_, fun p' => ?_⟩
    · obtain ⟨_, _, huq⟩ := hu' K (f i) (p₁ ≫ φ i)
      have r2 := hφ i K p₂
      rw [← e] at r2
      have e' := (huq ⟨i, p₁⟩ (hφ i K p₁)).trans (huq ⟨i, p₂⟩ r2).symm
      exact eq_of_heq (Sigma.mk.inj_iff.1 e').2
    · obtain ⟨⟨j, p⟩, hr, -⟩ := hu' K (f i) p'
      obtain ⟨_, _, huq⟩ := hu K j p
      have e' := (huq ⟨f i, p'⟩ hr).trans (huq ⟨f j, p ≫ φ j⟩ (hφ j K p)).symm
      have hij : j = i := by
        have := congrArg g (congrArg Sigma.fst e')
        rw [gf, gf] at this
        exact this.symm
      subst hij
      exact ⟨p, (eq_of_heq (Sigma.mk.inj_iff.1 e').2).symm⟩
  have := GlobalTheory.BijPointsIso.isIso_of_bijective_points F (Y i) (Y' (f i)) (φ i) (hφs i) hbij
  exact ⟨asIso (φ i), fun K _ _ p => hφ i K p⟩

end GlobalTheory.ShFam.GalCarry
