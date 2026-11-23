import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem spMap_injective_divisor {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem ringHom_ext_Bt {S : Type} [CommRing S] {α β : Bt P' x0 hu →+* S}
    (h1 : α.comp (algebraMap O (Bt P' x0 hu)) = β.comp (algebraMap O (Bt P' x0 hu)))
    (h2 : α.comp (inB P' x0 hu) = β.comp (inB P' x0 hu)) : α = β := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o b =>
    have e : (o ⊗ₜ[Localization.Away P'.f] b : Bt P' x0 hu) =
        algebraMap O (Bt P' x0 hu) (show O from o) * inB P' x0 hu b := by
      change _ = (o ⊗ₜ[Localization.Away P'.f] (1 : P'.B)) * ((1 : OL P' x0 hu) ⊗ₜ b)
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    rw [e, map_mul, map_mul]
    exact congrArg₂ (· * ·) (RingHom.congr_fun h1 (show O from o)) (RingHom.congr_fun h2 b)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable {G' : Over (Sp O)} {π : G'.left ⟶ t.G.left}

theorem aH_cancel_aff (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) {S : Type} [CommRing S]
    (α β : Bt P' x0 hu →+* S)
    (h : spMap α ≫ (aH P' x0 hu hπ).left = spMap β ≫ (aH P' x0 hu hπ).left) : α = β := by
  have hO : α.comp (algebraMap O (Bt P' x0 hu)) = β.comp (algebraMap O (Bt P' x0 hu)) := by
    have e := congrArg (· ≫ G'.hom) h
    simp only [Category.assoc, Over.w (aH P' x0 hu hπ)] at e
    apply spMap_injective_divisor
    exact (GlobalTheory.HTMap.spc (algebraMap O (Bt P' x0 hu)) α).symm.trans (e.trans (GlobalTheory.HTMap.spc _ β))
  have hB : α.comp (inB P' x0 hu) = β.comp (inB P' x0 hu) := by
    have e := congrArg (· ≫ π) h
    simp only [Category.assoc, aH_left_π] at e
    have e2 : spMap (α.comp (inB P' x0 hu)) ≫ P'.u.left = spMap (β.comp (inB P' x0 hu)) ≫ P'.u.left :=
      (GlobalTheory.HTMap.spc_assoc _ _ _).symm.trans (e.trans (GlobalTheory.HTMap.spc_assoc _ _ _))
    refine P'.fin.mono S _ _ (GlobalTheory.HTMap.FP.alg_ext ?_) e2
    change α.comp ((inB P' x0 hu).comp P'.str) = β.comp ((inB P' x0 hu).comp P'.str)
    rw [inB_str, ← RingHom.comp_assoc, ← RingHom.comp_assoc, hO]
  exact ringHom_ext_Bt P' x0 hu hO hB

theorem aH_left_mono (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) : Mono (aH P' x0 hu hπ).left := by
  constructor
  intro T g h e
  refine Scheme.Cover.hom_ext T.affineCover _ _ fun i => ?_
  have ea := Spec.map_preimage (T.affineCover.f i ≫ g)
  have eb := Spec.map_preimage (T.affineCover.f i ≫ h)
  have key := aH_cancel_aff P' x0 hu hπ (Spec.preimage (T.affineCover.f i ≫ g)).hom
    (Spec.preimage (T.affineCover.f i ≫ h)).hom (by
      change Spec.map (Spec.preimage (T.affineCover.f i ≫ g)) ≫ _ = Spec.map (Spec.preimage (T.affineCover.f i ≫ h)) ≫ _
      rw [ea, eb]
      exact (Category.assoc _ _ _).trans ((congrArg (T.affineCover.f i ≫ ·) e).trans (Category.assoc _ _ _).symm))
  exact ea.symm.trans ((congrArg Spec.map (CommRingCat.hom_ext key)).trans eb)

end GlobalTheory.FinPartAt
