import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrderStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderInductionIdStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionEqZeroOfValuesStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT.FiniteIso

open GlobalTheory.CompanionTheory.Ar.BT.SubOrder

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem isFinOpenSub_top (Γ : QFGroup R T) (hfin : IsFinite Γ.G.hom) : Γ.IsFinOpenSub ⊤ where
  finite := by
    have := hfin
    have hi : IsIso (⊤ : Γ.G.left.Opens).ι := (Scheme.topIso Γ.G.left).isIso_hom
    infer_instance
  one _ := trivial
  mul _ _ _ _ _ _ := trivial
  inv _ _ _ _ := trivial

noncomputable def secMap {X : Scheme.{0}} {A : Type} [CommRing A] (j : X ⟶ Spec (CommRingCat.of A)) : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop).hom

theorem val_secMap (Γ : QFGroup R T) {A : Subalgebra R (T → R)} {j : Γ.G.left ⟶ Spec (CommRingCat.of A)}
    (hj : Γ.IsEmb A j) (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ (⊤ : Γ.G.left.Opens)) (a : A) :
    valAt (Γ.pt t).left ⊤ h (secMap j a) = algebraMap R (FractionRing R) ((a : T → R) t) := by
  have e0 : j.appLE ⊤ ⊤ (by simp) = j.appTop := Scheme.Hom.appLE_eq_app _
  have h2 : ⊤ ≤ ((Γ.pt t).left ≫ j) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A)).Opens) := by simp
  have h3 : ⊤ ≤ (Spec.map (CommRingCat.ofHom
    ((algebraMap R (FractionRing R)).comp ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom)))) ⁻¹ᵁ
      (⊤ : (Spec (CommRingCat.of A)).Opens) := by simp
  have e1 := valHom_appLE (Γ.pt t).left j (V := ⊤) (W := ⊤) (by simp) h h2
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
  rw [e0, valHom_congr (hj.pt t) _ h2 h3, valHom_spec_top] at e1
  exact e1

theorem isIso_of_secMap_bijective {X : Scheme.{0}} [IsAffine X] {A : Type} [CommRing A]
    (j : X ⟶ Spec (CommRingCat.of A)) (hb : Function.Bijective (secMap j)) : IsIso j := by
  have h1 : IsIso ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  have h2 : IsIso j.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of A)).inv j.appTop
  have e := Scheme.isoSpec_hom_naturality j
  have h3 : IsIso (j ≫ (Spec (CommRingCat.of A)).isoSpec.hom) := by
    rw [← e]; infer_instance
  exact IsIso.of_isIso_comp_right j (Spec (CommRingCat.of A)).isoSpec.hom

end GlobalTheory.CompanionTheory.Ar.BT.FiniteIso

namespace GlobalTheory.CompanionTheory.Ar.BT.FiniteIso

open GlobalTheory.CompanionTheory.Ar.BT.SubOrder

theorem isIso_of_finite : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsFinite Γ.G.hom → IsIso j := by
  intro R _ _ _ T _ _ Γ j hj hfin
  have hF := isFinOpenSub_top Γ hfin
  have hU := isAffineOpen_of_fin Γ hF
  have : IsAffine Γ.G.left := by
    have := hfin
    exact isAffine_of_isAffineHom Γ.G.hom
  obtain ⟨H, A', hH, hopf, hA'⟩ := GlobalTheory.T.finite_open_hopf_order R T Γ ⊤ hF
  have htop : ∀ t, ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ (⊤ : Γ.G.left.Opens) := fun t => by simp
  have hHt : ∀ t, t ∈ H := fun t => (hH t).2 (htop t)
  have inj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  letI : Algebra R Γ(Γ.G.left, ⊤) := (secRho Γ hU).toAlgebra
  have hρ : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, ⊤))) :=
    fromSpec_hom Γ hU
  have hfinite := sec_finite hρ hF
  have hval : ∀ (s : Γ(Γ.G.left, ⊤)) (t : T),
      ∃ r : R, algebraMap R (FractionRing R) r = valAt (Γ.pt t).left ⊤ (htop t) s := by
    intro s t
    have h1 : IsIntegral R s := Algebra.IsIntegral.isIntegral s
    exact IsIntegrallyClosed.isIntegral_iff.1 (h1.map (valAlg hρ t (htop t)))
  apply isIso_of_secMap_bijective
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    apply Subtype.ext
    funext t
    apply inj
    have e := val_secMap Γ hj t (htop t) a
    rw [ha, ← valHom_apply, map_zero] at e
    simpa using e.symm
  · intro s
    choose f hf using hval s
    let f' : H → R := fun h => f h
    have hf' : f' ∈ A' := (hA' f').2 ⟨s, fun t h => (hf t).symm⟩
    have hind : f' ∈ indOrder (MonoidHom.id H) A' := by
      rw [GlobalTheory.T.hopf_order_induction_id R H A' hopf]
      exact hf'
    have hmem : f ∈ Γ.btOrder ⊤ := by
      apply Algebra.subset_adjoin
      intro t g _
      obtain ⟨s', hs'⟩ := (hA' _).1 (hind ⟨t, hHt t⟩)
      exact ⟨⊤, trivial, s', fun u h => hs' ⟨u, hHt u⟩ h⟩
    refine ⟨⟨f, hmem⟩, ?_⟩
    rw [← sub_eq_zero]
    apply GlobalTheory.T.section_eq_zero_of_values R T Γ ⊤
    intro t h
    rw [← valHom_apply, map_sub, valHom_apply, valHom_apply, val_secMap Γ hj, hf, sub_self]

end GlobalTheory.CompanionTheory.Ar.BT.FiniteIso
