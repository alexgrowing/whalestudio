import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaleInvOfFamMap
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LineConst

noncomputable section

namespace GlobalTheory.LineConst
open Polynomial

variable {k : Type} [Field k]

private theorem scaleX_isUnit (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    IsUnit ((algebraMap (Polynomial R) (Localization.Away (X : Polynomial R))).comp (scaleHom k R u) X) := by
  simp only [RingHom.comp_apply, scaleHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_mul]
  refine IsUnit.mul ?_ (IsLocalization.Away.algebraMap_isUnit _)
  exact ((isUnit_iff_exists_inv.mpr ⟨v, huv⟩).map Polynomial.C).map _

private def psiHom (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    Localization.Away (X : Polynomial k) →+* Localization.Away (X : Polynomial R) :=
  IsLocalization.Away.lift (X : Polynomial k) (scaleX_isUnit R huv)

private theorem psi_loc (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    (algebraMap (Polynomial R) (Localization.Away (X : Polynomial R))).comp (scaleHom k R u) =
      (psiHom R huv).comp (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k))) :=
  RingHom.ext fun a => by simp only [RingHom.comp_apply, psiHom, IsLocalization.Away.lift_eq]

private theorem psi_inv (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial R) :
        Localization.Away (X : Polynomial R))).toRingHom.comp (scaleHom k R v) =
      (psiHom R huv).comp (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial k) :
        Localization.Away (X : Polynomial k))).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    have e : (algebraMap k (Localization.Away (X : Polynomial k))) a =
        algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) (Polynomial.C a) := by
      rw [IsScalarTower.algebraMap_apply k (Polynomial k) (Localization.Away (X : Polynomial k))]
      rfl
    have e2 : (algebraMap R (Localization.Away (X : Polynomial R))) (algebraMap k R a) =
        algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C (algebraMap k R a)) := by
      rw [IsScalarTower.algebraMap_apply R (Polynomial R) (Localization.Away (X : Polynomial R))]
      rfl
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C, e, psiHom,
      IsLocalization.Away.lift_eq]
    simp [scaleHom, e2]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]
    have hb : psiHom R huv (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X) =
        algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C u) *
          algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) X := by
      simp [psiHom, IsLocalization.Away.lift_eq, scaleHom]
    have hc : psiHom R huv (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X) *
        psiHom R huv (IsLocalization.Away.invSelf (X : Polynomial k) : Localization.Away (X : Polynomial k)) = 1 := by
      rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    have hl : (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial R) :
        Localization.Away (X : Polynomial R))) (scaleHom k R v X) *
        psiHom R huv (algebraMap (Polynomial k) (Localization.Away (X : Polynomial k)) X) = 1 := by
      rw [hb]
      have hv : (Polynomial.aeval (IsLocalization.Away.invSelf (X : Polynomial R) :
          Localization.Away (X : Polynomial R))) (scaleHom k R v X) =
          algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C v) *
            IsLocalization.Away.invSelf (X : Polynomial R) := by
        simp [scaleHom, Polynomial.aeval_def, Polynomial.eval₂_mul]
        congr 1
      rw [hv]
      calc _ = algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) (Polynomial.C (v * u)) *
            (algebraMap (Polynomial R) (Localization.Away (X : Polynomial R)) X *
              IsLocalization.Away.invSelf (X : Polynomial R)) := by rw [map_mul, map_mul]; ring
        _ = 1 := by rw [IsLocalization.Away.mul_invSelf, mul_comm v u, huv, map_one, map_one, _root_.one_mul]
    exact left_inv_eq_right_inv hl hc

private theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem scaled_loc (B : Over (Sp k)) (f₀ f₁ : Sp (Polynomial k) ⟶ B.left)
    (h0 : f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k)))
    (h1 : f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k)))
    (hyp : spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) :
        Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁)
    (R : Type) [CommRing R] [Algebra k R] {u v : R} (huv : u * v = 1) :
    spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ (scaled B f₀ h0 R u).left =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ (scaled B f₁ h1 R v).left := by
  change _ ≫ spMap (scaleHom k R u) ≫ f₀ = _ ≫ spMap (scaleHom k R v) ≫ f₁
  rw [← Category.assoc, ← Category.assoc, sp_comp, sp_comp, psi_loc R huv, psi_inv R huv,
    ← sp_comp (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) (psiHom R huv),
    Category.assoc, hyp, ← Category.assoc, sp_comp]

private def locOver (R : Type) [CommRing R] [Algebra k R] : Over (Sp k) :=
  Over.mk (spMap (algebraMap k (Localization.Away (Polynomial.X : Polynomial R))))

private def locIncl (R : Type) [CommRing R] [Algebra k R] : locOver (k := k) R ⟶ lineOver k R :=
  Over.homMk (spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R)))) (by
    change spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫
      spMap (algebraMap k (Polynomial R)) = spMap (algebraMap k (Localization.Away (Polynomial.X : Polynomial R)))
    rw [sp_comp, ← IsScalarTower.algebraMap_eq])

private def locInv (R : Type) [CommRing R] [Algebra k R] : locOver (k := k) R ⟶ lineOver k R :=
  Over.homMk (spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
      Localization.Away (Polynomial.X : Polynomial R))).toRingHom) (by
    change spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
      Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫
      spMap (algebraMap k (Polynomial R)) = spMap (algebraMap k (Localization.Away (Polynomial.X : Polynomial R)))
    have e : (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :
        Localization.Away (Polynomial.X : Polynomial R))).toRingHom.comp (algebraMap k (Polynomial R)) =
        algebraMap k (Localization.Away (Polynomial.X : Polynomial R)) := by
      refine RingHom.ext fun a => ?_
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.algebraMap_apply,
        Polynomial.aeval_C]
      exact (IsScalarTower.algebraMap_apply k R (Localization.Away (Polynomial.X : Polynomial R)) a).symm
    rw [sp_comp, e])

theorem famMap_loc_eq : ∀ {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f₀ f₁ : Sp (Polynomial k) ⟶ B.left) (h0 : f₀ ≫ B.hom = spMap (algebraMap k (Polynomial k))) (h1 : f₁ ≫ B.hom = spMap (algebraMap k (Polynomial k))), spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) : Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ → ∀ (R : Type) [CommRing R] [Algebra k R] (u v : R), u * v = 1 → spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ famMap B f₀ h0 R u = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) : Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ famMap B f₁ h1 R v := by
  intro k _ B _ f₀ f₁ h0 h1 hyp R _ _ u v huv
  have hs : ∀ {a b : R}, a * b = 1 → locIncl (k := k) R ≫ scaled B f₀ h0 R a = locInv R ≫ scaled B f₁ h1 R b := by
    intro a b hab
    ext1
    exact scaled_loc B f₀ f₁ h0 h1 hyp R hab
  have h := congrArg CommaMorphism.left
    (show locIncl (k := k) R ≫ (scaled B f₀ h0 R u * (scaled B f₀ h0 R 1)⁻¹) =
        locInv R ≫ (scaled B f₁ h1 R v * (scaled B f₁ h1 R 1)⁻¹) by
      rw [MonObj.comp_mul, GrpObj.comp_inv, MonObj.comp_mul, GrpObj.comp_inv, hs huv, hs (_root_.one_mul 1)])
  exact h

end GlobalTheory.LineConst
