import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CurveBaseChange

variable {R F : Type} [CommRing R] [Field F] (ψ : R →+* F) (P₁ : Polynomial R)

def locMap : Localization.Away P₁ →+* Localization.Away (P₁.map ψ) :=
  IsLocalization.Away.map (Localization.Away P₁) (Localization.Away (Polynomial.mapRingHom ψ P₁)) (Polynomial.mapRingHom ψ) P₁

theorem locMap_algebraMap (p : Polynomial R) :
    locMap ψ P₁ (algebraMap (Polynomial R) _ p) = algebraMap (Polynomial F) _ (p.map ψ) := by
  unfold locMap IsLocalization.Away.map
  erw [IsLocalization.map_eq]
  rfl

theorem eval_map_apply' (a : R) (p : Polynomial R) : (p.map ψ).eval (ψ a) = ψ (p.eval a) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

theorem isUnit_eval (a : R) (ha : IsUnit (Polynomial.evalRingHom a P₁)) :
    IsUnit (Polynomial.evalRingHom (ψ a) (P₁.map ψ)) := by
  simpa [eval_map_apply'] using ha.map ψ

def evalAt (a : R) (ha : IsUnit (Polynomial.evalRingHom a P₁)) :
    Localization.Away (P₁.map ψ) →ₐ[F] F where
  toRingHom := IsLocalization.Away.lift (S := Localization.Away (P₁.map ψ)) (P₁.map ψ) (isUnit_eval ψ P₁ a ha)
  commutes' c := by
    rw [IsScalarTower.algebraMap_apply F (Polynomial F) (Localization.Away (P₁.map ψ))]
    simp [IsLocalization.Away.lift, IsLocalization.lift_eq]

theorem evalAt_comp (a : R) (ha : IsUnit (Polynomial.evalRingHom a P₁)) :
    (evalAt ψ P₁ a ha).toRingHom.comp (locMap ψ P₁) =
      ψ.comp (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ ha) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers P₁)
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply, locMap_algebraMap]
  simp [evalAt, IsLocalization.Away.lift, IsLocalization.lift_eq, eval_map_apply']

theorem locMap_comp_algebraMap :
    (locMap ψ P₁).comp (algebraMap R (Localization.Away P₁)) =
      (algebraMap F (Localization.Away (P₁.map ψ))).comp ψ := by
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R (Polynomial R) (Localization.Away P₁), locMap_algebraMap,
    RingHom.comp_apply, IsScalarTower.algebraMap_apply F (Polynomial F) (Localization.Away (P₁.map ψ))]
  simp [Polynomial.algebraMap_apply]

end GlobalTheory.CurveBaseChange

namespace GlobalTheory

open GlobalTheory.CurveBaseChange in

theorem curve_baseChange_two_points : ∀ (R F : Type) [CommRing R] [Field F] (ψ : R →+* F) (X : Over (Sp R)) (P₁ : Polynomial R) (u₁ : Sp (Localization.Away P₁) ⟶ X.left) (α β : R) (hα : IsUnit (Polynomial.evalRingHom α P₁)) (hβ : IsUnit (Polynomial.evalRingHom β P₁)), u₁ ≫ X.hom = spMap (algebraMap R (Localization.Away P₁)) → IsUnit (ψ P₁.leadingCoeff) → spMap ψ ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁ ≠ spMap ψ ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁ → ∃ (P' : Polynomial F) (_ : P' ≠ 0) (u' : Sp (Localization.Away P') ⟶ ((Over.pullback (spMap ψ)).obj X).left) (a' b' : Localization.Away P' →ₐ[F] F), u' ≫ ((Over.pullback (spMap ψ)).obj X).hom = spMap (algebraMap F (Localization.Away P')) ∧ spMap a'.toRingHom ≫ u' ≠ spMap b'.toRingHom ≫ u' := by
  intro R F _ _ ψ X P₁ u₁ α β hα hβ hu hlc hne
  have hP : P₁.map ψ ≠ 0 := by
    intro h
    have h' := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero ψ hlc.ne_zero
    rw [h, Polynomial.leadingCoeff_zero] at h'
    exact hlc.ne_zero h'.symm
  have hcomm : (spMap (locMap ψ P₁) ≫ u₁) ≫ X.hom =
      spMap (algebraMap F (Localization.Away (P₁.map ψ))) ≫ spMap ψ := by
    rw [Category.assoc, hu, ← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, locMap_comp_algebraMap]
  refine ⟨P₁.map ψ, hP, pullback.lift _ _ hcomm, evalAt ψ P₁ α hα, evalAt ψ P₁ β hβ, ?_, ?_⟩
  · exact pullback.lift_snd _ _ _
  · intro h
    apply hne
    have h2 := congrArg (· ≫ pullback.fst X.hom (spMap ψ)) h
    simp only [Category.assoc] at h2
    erw [pullback.lift_fst] at h2
    rw [← Category.assoc, ← Category.assoc, ← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, ← evalAt_comp,
      ← evalAt_comp, Geo.Tor.spMap_comp, Geo.Tor.spMap_comp, Category.assoc, Category.assoc]
    exact h2

end GlobalTheory
