import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeIntegralModelsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdealStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPointsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HTChartExistsHoldsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.FullTorsionPacking

noncomputable def preHom {X : Scheme.{0}} (G : Over X) [GrpObj G] {A B : Over X} (u : A ⟶ B) :
    (B ⟶ G) →* (A ⟶ G) where
  toFun g := u ≫ g
  map_one' := MonObj.comp_one u
  map_mul' g h := MonObj.comp_mul u g h

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem sp_id {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  rw [← Spec.map_id]; rfl

theorem isDominant_spMap {A B : Type} [Field A] [Field B] (i : A →+* B) : IsDominant (spMap i) := by
  refine ⟨Function.Surjective.denseRange fun y => ?_⟩
  haveI : Subsingleton (Spec (CommRingCat.of A)) := inferInstanceAs (Subsingleton (PrimeSpectrum A))
  exact ⟨(default : PrimeSpectrum B), Subsingleton.elim _ _⟩

theorem exists_inv {Ω : Type} [Field Ω] {O : Type} [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω)
    [IsFractionRing R Ω] : ∃ e' : Ω →+* FractionRing R, (fracToField R).comp e' = RingHom.id Ω ∧
      e'.comp (algebraMap R Ω) = algebraMap R (FractionRing R) := by
  have h : fracToField R = (FractionRing.algEquiv R Ω : FractionRing R →+* Ω) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    ext r
    have h1 : fracToField R (algebraMap R (FractionRing R) r) = algebraMap R Ω r :=
      IsFractionRing.lift_algebraMap _ r
    exact h1.trans ((FractionRing.algEquiv R Ω).commutes r).symm
  refine ⟨((FractionRing.algEquiv R Ω).symm : Ω →+* FractionRing R), ?_, ?_⟩
  · rw [h]; ext z; simp
  · ext r
    exact (FractionRing.algEquiv R Ω).symm.commutes r

end PositivityTheory.Xgn.FullTorsionPacking

open PositivityTheory.Xgn.FullTorsionPacking in
theorem PositivityTheory.Xgn.full_torsion_packing : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsNoetherianRing R] [CharZero R] [IsFractionRing R Ω] (x : Spec (CommRingCat.of R) ⟶ X), spMap (algebraMap R Ω) ≫ x = ξ → ∀ (T : Type) [CommGroup T] (pt : T →* (Over.mk ξ ⟶ G)) (N n : ℕ), 1 ≤ N → N ∣ n → FullTorsion G ξ n → Function.Injective pt → (∀ g : Over.mk ξ ⟶ G, g ^ N = 1 ↔ ∃ t, pt t = g) → ∃ (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i ∧ ∀ t, (pt t).left = spMap (fracToField R) ≫ (Γ.pt t).left ≫ i := by
  intro X G _ hG Ω _ ξ O _ _ R _ _ _ x hx T _ pt N n hN hNn hFT hinj honto
  obtain ⟨e', he, he'⟩ := exists_inv R
  have hu : spMap e' ≫ ξ = (genPt R).hom ≫ x := by
    have h0 : spMap e' ≫ spMap (algebraMap R Ω) = spMap (algebraMap R (FractionRing R)) := by
      rw [sp_comp, he']
    subst hx
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) h0)
  have hee : spMap (fracToField R) ≫ spMap e' = 𝟙 _ := by
    rw [sp_comp, he, sp_id]
  let u : Over.mk ((genPt R).hom ≫ x) ⟶ Over.mk ξ := Over.homMk (spMap e') hu
  let τ : T →* (Over.mk ((genPt R).hom ≫ x) ⟶ G) := (preHom G u).comp pt
  have hτ : ∀ t, (τ t).left = spMap e' ≫ (pt t).left := fun t => rfl
  have hpt : ∀ t, (pt t).left = spMap (fracToField R) ≫ (τ t).left := fun t => by
    rw [hτ, ← Category.assoc, hee]
    exact (Category.id_comp _).symm
  have hτinj : Function.Injective τ := fun s t h => by
    apply hinj
    ext1
    rw [hpt, hpt, h]
  have hτN : ∀ t, τ t ^ N = 1 := fun t => by
    change preHom G u (pt t) ^ N = 1
    rw [← map_pow, (honto _).2 ⟨t, rfl⟩, map_one]
  obtain ⟨Γ, i, hΓ, hi⟩ := GlobalTheory.T.torsion_embedding_geometric_points R T X G hG x N hN τ hτinj hτN (by
    intro Ω' _ _ a g hg
    have hw : spMap (a.comp e') ≫ ξ = Spec.map (CommRingCat.ofHom a) ≫ (genPt R).hom ≫ x := by
      have h0 : spMap (a.comp e') ≫ ξ = spMap a ≫ spMap e' ≫ ξ := by
        rw [← sp_comp, Category.assoc]
      exact h0.trans (congrArg (spMap a ≫ ·) hu)
    let w : Over.mk (spMap (a.comp e') ≫ ξ) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom a) ≫ (genPt R).hom ≫ x) :=
      Over.homMk (𝟙 _) ((Category.id_comp _).trans hw.symm)
    have hgN : preHom G w g ^ N = 1 := by rw [← map_pow, hg, map_one]
    have hgn : preHom G w g ^ n = 1 := by
      obtain ⟨m, rfl⟩ := hNn
      rw [pow_mul, hgN, one_pow]
    obtain ⟨x₀, hx₀⟩ := hFT Ω' (a.comp e') _ hgn
    let v : Over.mk (spMap (a.comp e') ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap (a.comp e')) rfl
    have hv : preHom G v x₀ = preHom G w g := by
      ext1
      exact hx₀.symm
    have h1 : preHom G v (x₀ ^ N) = preHom G v 1 := by
      rw [map_pow, hv, hgN, map_one]
    have h2 : x₀ ^ N = 1 := by
      haveI := hG.separated
      haveI := isDominant_spMap (a.comp e')
      haveI : IsReduced (Over.mk ξ).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of Ω)))
      ext1
      refine ext_of_isDominant_of_isSeparated G.hom ?_ (spMap (a.comp e')) ?_
      · rw [Over.w, Over.w]
      · exact congrArg CommaMorphism.left h1
    obtain ⟨t, rfl⟩ := (honto _).1 h2
    refine ⟨t, ?_⟩
    have h3 : (preHom G w g).left = g.left := Category.id_comp _
    have h4 : ∀ q : Spec (CommRingCat.of Ω) ⟶ G.left, spMap (a.comp e') ≫ q = spMap a ≫ spMap e' ≫ q := fun q => by
      rw [← sp_comp, Category.assoc]
    exact h3.symm.trans (hx₀.trans (h4 _)))
  exact ⟨Γ, i, hΓ, fun t => (hpt t).trans (congrArg (spMap (fracToField R) ≫ ·) (hi t).symm)⟩
