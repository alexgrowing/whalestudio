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

theorem exists_ptMap_eq {O : Type} [CommRing O] {D : Type} [CommRing D] [Algebra O D] (w : specO O O ⟶ specO O D) :
    ∃ φ : D →ₐ[O] O, ptMap φ = w := by
  let f : CommRingCat.of D ⟶ CommRingCat.of O := Spec.preimage w.left
  have hf : Spec.map f = w.left := Spec.map_preimage _
  have hw : w.left ≫ (specO O D).hom = (specO O O).hom := Over.w w
  have hc : ∀ c : O, f.hom (algebraMap O D c) = c := by
    have h2 : Spec.map (CommRingCat.ofHom (algebraMap O D) ≫ f) = Spec.map (CommRingCat.ofHom (algebraMap O O)) := by
      rw [Spec.map_comp, hf]; exact hw
    have h3 := Spec.map_injective h2
    intro c
    have := congrArg (fun g : CommRingCat.of O ⟶ CommRingCat.of O => g.hom c) h3
    simpa using this
  refine ⟨{ f.hom with commutes' := hc }, ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom f.hom) = w.left
  rw [CommRingCat.ofHom_hom, hf]

theorem unitOf_chi_eq_weil : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (P' : GlobalTheory.HTMap.FP t ξ (p ^ n)) (x0 : R →+* 𝓞_ℂ_[p]) (hu : IsUnit (x0 P'.f)) (P : PtP E p) (π : P.G.left ⟶ t.G.left) (hg : IsGrpPullback P.G t.G (spMap x0 ≫ ξ) π) (b : P'.Bˣ) (tt : P.T), (∀ (β : P'.B →+* 𝓞_ℂ_[p]) (w : Sp 𝓞_ℂ_[p] ⟶ t.G.left), P'.At x0 w β → ∀ z : GlobalTheory.ChTor.Pts P.A.A, z.left ≫ P.gen ≫ π = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ w → algebraMap 𝓞_ℂ_[p] ℂ_[p] (β b) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p])) → ∀ (w : specO 𝓞_ℂ_[p] 𝓞_ℂ_[p] ⟶ Hs P' x0 hu) (z : GlobalTheory.ChTor.Pts P.A.A), z.left ≫ P.gen = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ (w ≫ aH P' x0 hu hg.1).left → algebraMap 𝓞_ℂ_[p] ℂ_[p] (unitOf (w ≫ chi P' x0 hu b) : 𝓞_ℂ_[p]) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p]) := by
  intro E _ _ _ H X t R _ ξ p _ n _ P' x0 hu P π hg b tt hb w z hz
  obtain ⟨φ, rfl⟩ := exists_ptMap_eq w
  let β : P'.B →+* 𝓞_ℂ_[p] := φ.toRingHom.comp (inB P' x0 hu)
  have hβ1 : β.comp P'.str = x0 := by
    change φ.toRingHom.comp ((inB P' x0 hu).comp P'.str) = x0
    rw [inB_str]
    exact RingHom.ext fun r => φ.commutes (x0 r)
  have hβ2 : spMap β ≫ P'.u.left = (ptMap φ ≫ aH P' x0 hu hg.1).left ≫ π := by
    rw [Over.comp_left, Category.assoc, aH_left_π]
    change _ = spMap φ.toRingHom ≫ spMap (inB P' x0 hu) ≫ P'.u.left
    exact (GlobalTheory.HTMap.spc_assoc _ _ _).symm
  have hat : P'.At x0 ((ptMap φ ≫ aH P' x0 hu hg.1).left ≫ π) β := ⟨hβ1, hβ2⟩
  have hz' : z.left ≫ P.gen ≫ π =
      spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ (ptMap φ ≫ aH P' x0 hu hg.1).left ≫ π := by
    rw [← Category.assoc, hz, Category.assoc]
  have key := hb β _ hat z hz'
  rw [GlobalTheory.GmPoints.unitOf_ptMap, unitOf_chi]
  exact key

end GlobalTheory.FinPartAt
