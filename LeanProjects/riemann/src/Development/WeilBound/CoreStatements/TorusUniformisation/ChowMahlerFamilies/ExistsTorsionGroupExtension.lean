import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPointsStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TorsionGroupExtension

theorem epi_spec {K k : Type} [Field K] [Field k] (i : K →+* k) :
    Epi (Spec.map (CommRingCat.ofHom i)) := by
  have h1 : Flat (Spec.map (CommRingCat.ofHom i)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := i.toAlgebra
    exact (inferInstance : Module.Flat K k)
  have h2 : Surjective (Spec.map (CommRingCat.ofHom i)) :=
    ⟨fun y => ⟨IsLocalRing.closedPoint k, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

noncomputable def pre {X : Scheme.{0}} {A B : Over X} (u : A ⟶ B) (G : Over X) [GrpObj G] :
    (B ⟶ G) →* (A ⟶ G) where
  toFun g := u ≫ g
  map_one' := MonObj.comp_one u
  map_mul' g h := MonObj.comp_mul u g h

theorem pre_inj {X : Scheme.{0}} {A B : Over X} (u : A ⟶ B) (hu : Epi u.left) (G : Over X) [GrpObj G] :
    Function.Injective (pre u G) := fun g h e => by
  apply Over.OverMorphism.ext
  rw [← cancel_epi u.left]
  exact congrArg (fun m : A ⟶ G => m.left) e

theorem spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp, CommRingCat.ofHom_comp]

end PositivityTheory.Xgn.TorsionGroupExtension

open PositivityTheory.Xgn.TorsionGroupExtension in
theorem PositivityTheory.Xgn.exists_torsion_group_extension : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [CharZero R'] (Ω : Type) [Field Ω] [Algebra R' Ω] [IsFractionRing R' Ω] (T : Type) [CommGroup T] (X : Scheme.{0}) (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (x' : Spec (CommRingCat.of R') ⟶ X) (ξ : Spec (CommRingCat.of Ω) ⟶ X), Spec.map (CommRingCat.ofHom (algebraMap R' Ω)) ≫ x' = ξ → ∀ N : ℕ, 1 ≤ N → ∀ pt : T →* (Over.mk ξ ⟶ G), Function.Injective pt → (∀ g : Over.mk ξ ⟶ G, g ^ N = 1 ↔ ∃ t, pt t = g) → FullTorsion G ξ N → ∃ (Γ' : QFGroup R' T) (i' : Γ'.G.left ⟶ G.left), Γ'.IsTorsionAlong G x' N i' ∧ ∀ (a : FractionRing R' →+* Ω), a.comp (algebraMap R' (FractionRing R')) = algebraMap R' Ω → ∀ t, (pt t).left = Spec.map (CommRingCat.ofHom a) ≫ (Γ'.pt t).left ≫ i' := by
  intro R' _ _ _ _ Ω _ _ _ T _ X G _ hG x' ξ hξ N hN pt hinj htor hfull
  let e : FractionRing R' ≃+* Ω := (FractionRing.algEquiv R' Ω).toRingEquiv
  let b : Ω →+* FractionRing R' := e.symm.toRingHom
  let c : FractionRing R' →+* Ω := e.toRingHom
  have hc : c.comp (algebraMap R' (FractionRing R')) = algebraMap R' Ω :=
    RingHom.ext fun r => (FractionRing.algEquiv R' Ω).commutes r
  have hb : b.comp (algebraMap R' Ω) = algebraMap R' (FractionRing R') :=
    RingHom.ext fun r => (FractionRing.algEquiv R' Ω).symm.commutes r
  have hcb : c.comp b = RingHom.id Ω := RingHom.ext fun r => e.apply_symm_apply r
  have hu : Spec.map (CommRingCat.ofHom b) ≫ ξ =
      Spec.map (CommRingCat.ofHom (algebraMap R' (FractionRing R'))) ≫ x' := by
    rw [← hξ, ← Category.assoc, spec_comp, hb]
  let u : Over.mk ((BT.genPt R').hom ≫ x') ⟶ Over.mk ξ :=
    Over.homMk (Spec.map (CommRingCat.ofHom b)) hu
  let τ : T →* (Over.mk ((BT.genPt R').hom ≫ x') ⟶ G) := (pre u G).comp pt
  have hτ : ∀ t, (τ t).left = Spec.map (CommRingCat.ofHom b) ≫ (pt t).left := fun t => rfl
  obtain ⟨Γ, i, h1, h2⟩ := GlobalTheory.T.torsion_embedding_geometric_points R' T X G hG x' N hN τ
    ((pre_inj u (epi_spec b) G).comp hinj)
    (fun t => by
      change pre u G (pt t) ^ N = 1
      rw [← map_pow, (htor _).2 ⟨t, rfl⟩, map_one])
    (fun k _ _ a g hg => by
      have hv : spMap (a.comp b) ≫ ξ =
          Spec.map (CommRingCat.ofHom a) ≫ (BT.genPt R').hom ≫ x' := by
        change Spec.map (CommRingCat.ofHom (a.comp b)) ≫ ξ = Spec.map (CommRingCat.ofHom a) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R' (FractionRing R'))) ≫ x'
        rw [← hu, ← Category.assoc, spec_comp]
      let v : Over.mk (spMap (a.comp b) ≫ ξ) ⟶
          Over.mk (Spec.map (CommRingCat.ofHom a) ≫ (BT.genPt R').hom ≫ x') :=
        Over.homMk (𝟙 _) (by simpa using hv.symm)
      have hg' : (pre v G g) ^ N = 1 := by rw [← map_pow, hg, map_one]
      obtain ⟨x, hx⟩ := hfull k (a.comp b) (pre v G g) hg'
      let w : Over.mk (spMap (a.comp b) ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap (a.comp b)) rfl
      have hxw : pre w G x = pre v G g := Over.OverMorphism.ext hx.symm
      have hxN : x ^ N = 1 := by
        apply pre_inj w (epi_spec (a.comp b)) G
        rw [map_pow, map_one, hxw, hg']
      obtain ⟨t, rfl⟩ := (htor x).1 hxN
      refine ⟨t, ?_⟩
      have hx' : g.left = Spec.map (CommRingCat.ofHom (a.comp b)) ≫ (pt t).left :=
        (Category.id_comp _).symm.trans hx
      rw [hx', ← spec_comp, Category.assoc]
      rfl)
  refine ⟨Γ, i, h1, fun a ha t => ?_⟩
  have hac : a = c := IsLocalization.ringHom_ext (nonZeroDivisors R') (ha.trans hc.symm)
  have h3 : (Γ.pt t).left ≫ i = Spec.map (CommRingCat.ofHom b) ≫ (pt t).left := h2 t
  have h4 : Spec.map (CommRingCat.ofHom c) ≫ Spec.map (CommRingCat.ofHom b) ≫ (pt t).left = (pt t).left := by
    rw [← Category.assoc, spec_comp, hcb]
    erw [Spec.map_id]
    exact Category.id_comp _
  rw [hac]
  exact h4.symm.trans (congrArg (fun m => Spec.map (CommRingCat.ofHom c) ≫ m) h3.symm)
