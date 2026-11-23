import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftThetaSetupModelAfterExtension

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

open GlobalTheory.Poinc.TraitLift in

theorem exists_uTrait_lift_setup (hExt : UTraitExtSt) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), IsClopen (Set.range X₁.π) → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ C.Z), T.y ≫ C.i = jK T.V ≫ ξ → ξ (closedPoint T.V) ∈ Set.range X₁.π → ∃ (T' : UTrait Xo c) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V) (ξ₁ : Sp T'.V ⟶ X₁.M.Z), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) ∧ T'.y = spMap fK ≫ T.y ∧ spMap f ≫ ξ = ξ₁ ≫ X₁.π ∧ T'.y ≫ C.i = jK T'.V ≫ ξ₁ ≫ X₁.π := by
  intro E _ _ _ H Dw l Xo c C X₁ hcl T ξ hξ hc
  haveI : IsFinite X₁.π := X₁.fin
  obtain ⟨hdvr, hcpl, hch⟩ := T.cdvr
  haveI := hdvr
  haveI := hcpl
  haveI := hch
  have hgen : (jK T.V ≫ ξ) (closedPoint (FractionRing T.V)) ∈ Set.range X₁.π :=
    mem_of_closedPoint _ hcl.isOpen T.V ξ hc _
  obtain ⟨L, _, _, _, η, hη⟩ := exists_finite_point X₁.π (FractionRing T.V) (jK T.V ≫ ξ) hgen
  obtain ⟨V₂, _, _, _, j, e, hB, hD, hj, hjl, he⟩ := exists_closure T.V L
  have hring : (algebraMap V₂ (FractionRing V₂)).comp j =
      (e.comp (algebraMap (FractionRing T.V) L)).comp (algebraMap T.V (FractionRing T.V)) :=
    RingHom.ext fun a => (he a).symm
  haveI : ValuationRing V₂ := inferInstance
  have hsq : (spMap e ≫ η) ≫ X₁.π = jK V₂ ≫ (spMap j ≫ ξ) := by
    rw [Category.assoc, hη, ← Category.assoc, spMap_comp', ← Category.assoc, ← Category.assoc, spMap_comp',
      show jK V₂ = spMap (algebraMap V₂ (FractionRing V₂)) from rfl, spMap_comp', hring]
  obtain ⟨l₁, hl1, -⟩ := exists_lift_of_isFinite X₁.π V₂ (spMap e ≫ η) (spMap j ≫ ξ) hsq
  obtain ⟨T', f'', fK'', hinj'', hloc'', -, hc'', hy''⟩ := hExt E H Dw l Xo c V₂ hB hD
    (spMap (e.comp (algebraMap (FractionRing T.V) L)) ≫ T.y)
  have hring2 : (algebraMap T'.V (FractionRing T'.V)).comp (f''.comp j) =
      (fK''.comp (e.comp (algebraMap (FractionRing T.V) L))).comp (algebraMap T.V (FractionRing T.V)) := by
    ext a
    simp only [RingHom.comp_apply]
    rw [← hc'', ← he]
  have key : jK T'.V ≫ spMap (f''.comp j) = spMap (fK''.comp (e.comp (algebraMap (FractionRing T.V) L))) ≫ jK T.V := by
    rw [show jK T'.V = spMap (algebraMap T'.V (FractionRing T'.V)) from rfl,
      show jK T.V = spMap (algebraMap T.V (FractionRing T.V)) from rfl, spMap_comp', spMap_comp', hring2]
  haveI := hloc''
  refine ⟨T', f''.comp j, fK''.comp (e.comp (algebraMap (FractionRing T.V) L)), spMap f'' ≫ l₁, hinj''.comp hj,
    inferInstance, fun a => (RingHom.congr_fun hring2 a).symm, ?_, ?_, ?_⟩
  · rw [hy'', ← Category.assoc, spMap_comp']
  · rw [Category.assoc, hl1, ← Category.assoc, spMap_comp']
  · symm
    calc jK T'.V ≫ (spMap f'' ≫ l₁) ≫ X₁.π = jK T'.V ≫ spMap (f''.comp j) ≫ ξ := by
          rw [Category.assoc, hl1, ← spMap_comp', Category.assoc]
      _ = spMap (fK''.comp (e.comp (algebraMap (FractionRing T.V) L))) ≫ jK T.V ≫ ξ := by
          rw [← Category.assoc, key, Category.assoc]
      _ = T'.y ≫ C.i := by
          rw [← hξ, hy'', ← spMap_comp']
          simp only [Category.assoc]

theorem uTraitLift_setup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), IsClopen (Set.range X₁.π) → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ C.Z), T.y ≫ C.i = jK T.V ≫ ξ → ξ (closedPoint T.V) ∈ Set.range X₁.π → ∃ (T' : UTrait Xo c) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V) (ξ₁ : Sp T'.V ⟶ X₁.M.Z), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) ∧ T'.y = spMap fK ≫ T.y ∧ spMap f ≫ ξ = ξ₁ ≫ X₁.π ∧ T'.y ≫ C.i = jK T'.V ≫ ξ₁ ≫ X₁.π :=
  exists_uTrait_lift_setup GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint

end GlobalTheory.UPoinc
