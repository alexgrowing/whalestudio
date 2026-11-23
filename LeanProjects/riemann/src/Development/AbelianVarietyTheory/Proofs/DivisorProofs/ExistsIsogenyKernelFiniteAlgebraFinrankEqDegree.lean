import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotKerIdealDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerPart

open CategoryTheory.Limits MonoidalCategory

theorem one_left_eq {k : Type} [Field k] {X : Over (Sp k)} [MonObj X] (T : Over (Sp k)) :
    (1 : T ⟶ X).left = T.hom ≫ (MonObj.one : 𝟙_ (Over (Sp k)) ⟶ X).left := by
  rw [CategoryTheory.Hom.one_def, Over.comp_left]
  rfl

theorem isoSpec_hom_comp_spec {X : Scheme.{0}} [IsAffine X] {R : CommRingCat.{0}} (g : X ⟶ Spec R) :
    X.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ g.appTop) = g := by
  rw [Spec.map_comp, Scheme.isoSpec_hom, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem exists_kerPow_zero_finrank_eq_deg : ∀ (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B), IsIsogeny f →
    ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X),
      KerPow f 0 H i ∧ Module.finrank k H = deg f := by
  intro k _ A B f hf
  obtain ⟨-, hflat, -, hrank⟩ := isogeny_flat_finrank k A B f hf
  haveI : IsFinite f.hom.left := hf.1
  haveI := hflat
  let e : Sp k ⟶ B.X.left := (MonObj.one : 𝟙_ (Over (Sp k)) ⟶ B.X).left
  have he : e ≫ B.X.hom = 𝟙 _ := Over.w (MonObj.one : 𝟙_ (Over (Sp k)) ⟶ B.X)
  let P := pullback f.hom.left e
  let g : P ⟶ Sp k := pullback.snd f.hom.left e
  haveI : IsAffine P := isAffine_of_isAffineHom g
  let H : Type := Γ(P, ⊤)
  letI : Algebra k H := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop).hom.toAlgebra
  have hg : P.isoSpec.hom ≫ spMap (algebraMap k H) = g := isoSpec_hom_comp_spec g
  have hig : P.isoSpec.inv ≫ g = spMap (algebraMap k H) := by rw [← hg, Iso.inv_hom_id_assoc]
  have hw : (P.isoSpec.inv ≫ pullback.fst f.hom.left e) ≫ A.X.hom = spMap (algebraMap k H) := by
    rw [← Over.w f.hom, Category.assoc, pullback.condition_assoc, he, Category.comp_id, hig]
  let i : ptOver k H ⟶ A.X := Over.homMk (P.isoSpec.inv ≫ pullback.fst f.hom.left e) hw
  have hi : i.left = P.isoSpec.inv ≫ pullback.fst f.hom.left e := rfl
  refine ⟨H, inferInstance, inferInstance, i, ⟨⟨?_, pow_zero i⟩, ?_⟩, ?_⟩
  · ext1
    rw [Over.comp_left, one_left_eq, hi, Category.assoc, pullback.condition, ← Category.assoc, hig]
    rfl
  · intro R _ _ x hx _
    have hx' : x.left ≫ f.hom.left = spMap (algebraMap k R) ≫ e := by
      have := congrArg Over.Hom.left hx
      rw [Over.comp_left, one_left_eq] at this
      exact this
    let l : Sp R ⟶ P := pullback.lift x.left (spMap (algebraMap k R)) hx'
    obtain ⟨φ0, hφ0⟩ := Spec.map_surjective (l ≫ P.isoSpec.hom)
    have hc : CommRingCat.ofHom (algebraMap k H) ≫ φ0 = CommRingCat.ofHom (algebraMap k R) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ0, Category.assoc, hg]
      exact pullback.lift_snd _ _ _
    let φ : H →ₐ[k] R :=
      { φ0.hom with commutes' := fun c => congrArg (fun u => u.hom c) hc }
    have hφ : spMap φ.toRingHom = l ≫ P.isoSpec.hom := hφ0
    refine ⟨φ, ?_, fun ψ hψ => ?_⟩
    · change spMap φ.toRingHom ≫ i.left = x.left
      rw [hφ, hi, Category.assoc, Iso.hom_inv_id_assoc]
      exact pullback.lift_fst _ _ _
    · have h1 : spMap ψ.toRingHom ≫ P.isoSpec.inv = l := by
        apply pullback.hom_ext
        · rw [Category.assoc, ← hi]
          exact hψ.trans (pullback.lift_fst _ _ _).symm
        · rw [Category.assoc, hig, pullback.lift_snd]
          change Spec.map _ ≫ Spec.map _ = Spec.map _
          rw [← Spec.map_comp]
          congr 1
          ext c
          exact ψ.commutes c
      have h2 : spMap ψ.toRingHom = spMap φ.toRingHom := by
        rw [hφ, ← h1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      have h3 := Spec.map_injective h2
      exact AlgHom.ext fun a => congrArg (fun u => u.hom a) h3
  · haveI : IsFinite (spMap (algebraMap k H)) := by rw [← hig]; infer_instance
    haveI : Flat (spMap (algebraMap k H)) := by rw [← hig]; infer_instance
    haveI : Module.Finite k H := by
      rw [← RingHom.finite_algebraMap]
      exact (IsFinite.SpecMap_iff _).1 ‹_›
    let pt : Sp k := IsLocalRing.closedPoint k
    have h1 := Scheme.Hom.finrank_pullback_snd f.hom.left e pt
    rw [hrank] at h1
    rw [← h1]
    change _ = Scheme.Hom.finrank g pt
    rw [← hg, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_algebraMap,
      Module.rankAtStalk_eq_finrank_of_free]
    rfl

end GlobalTheory.AV.KerPart
