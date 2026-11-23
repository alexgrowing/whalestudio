import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem isHolTo_comp_hom {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y : Scheme.{0}} {B : Set V}
    {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (φ : X ⟶ Y) : IsHolTo B (fun b => y b ≫ φ) := by
  intro U s
  have hfun : (fun b => valAt' (y b ≫ φ) U s) = fun b => valAt' (y b) (φ ⁻¹ᵁ U) ((φ.app U).hom s) :=
    funext fun b => (valAt'_comp _ φ U s).symm
  rw [hfun]
  exact h (φ ⁻¹ᵁ U) _

theorem exists_isExp_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (σ : R →+* ℂ) (T : PAT H (Sp R)) (T' : PAT H (Sp ℂ)) (m : SABMap T'.t T.t (spMap σ)) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ)) (e' : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ T'.t.G)), IsExp T' (RingHom.id ℂ) D ty Pe e' → ∃ e : (Fin g → ℂ) → (Over.mk (spMap σ) ⟶ T.t.G), IsExp T σ D ty Pe e ∧ ∀ z, (e z).left = (e' z).left ≫ m.φ := by
  intro E _ _ _ H R _ σ T T' m D g ty Pe e' ⟨hP, hol, hadd, hon, hker, hlin, hw⟩
  have hL : LBIso T'.t.PP.L (T.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have hT : (Over.mk (spMap (RingHom.id ℂ))).hom ≫ spMap σ = spMap σ := by
    show spMap (RingHom.id ℂ) ≫ spMap σ = spMap σ
    rw [hid, Category.id_comp]
  obtain ⟨p, hp⟩ := LiePull.exists_pushEquiv m.cart (Over.mk (spMap (RingHom.id ℂ))) (spMap σ) hT.symm
  refine ⟨fun z => p (e' z), ⟨hP, ?_, fun z w => (congrArg p (hadd z w)).trans (map_mul p _ _),
    p.surjective.comp hon, fun z => ?_, fun a z => ?_, fun k a b c hk hc => ?_⟩, fun z => hp _⟩
  · have h : (fun z => (p (e' z)).left) = fun z => (e' z).left ≫ m.φ := funext fun z => hp _
    exact h ▸ isHolTo_comp_hom hol m.φ
  · exact (map_eq_one_iff p p.injective).trans (hker z)
  · apply Over.OverMorphism.ext
    beta_reduce
    rw [Over.comp_left, hp, hp, hlin, Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg _ (m.act a)
  · have key : ∀ (y : Sp ℂ ⟶ Sp R) (_ : y = (Over.mk (spMap (RingHom.id ℂ))).hom ≫ spMap σ)
        (x₀ y₀ : Over.mk y ⟶ T.t.G) (x x' : Over.mk (spMap (RingHom.id ℂ)) ⟶ T'.t.G),
        x₀.left = x.left ≫ m.φ → y₀.left = x'.left ≫ m.φ →
        Out.WeilIs T'.t.G T'.t.PP.L k x x' (unitOn c) → Out.WeilIs T.t.G T.t.PP.L k x₀ y₀ (unitOn c) := by
      rintro y rfl x₀ y₀ x x' h₁ h₂ h₃
      exact (weilIs_grpPullback_of_comm _ _ _ _ _ m.φ _ _ T.t.PP.isLB T'.t.PP.isLB m.cart hL _ k x x' x₀ y₀ _
        h₁ h₂).1 h₃
    exact key _ hT.symm _ _ _ _ (hp _) (hp _) (hw k a b c hk hc)

end GlobalTheory.CM
