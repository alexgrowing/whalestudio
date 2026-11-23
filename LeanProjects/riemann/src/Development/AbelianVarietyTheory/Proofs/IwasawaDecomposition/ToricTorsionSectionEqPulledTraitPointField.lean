import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionSectionsUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionMapUniformisationGenericStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.ToricOverField

theorem unitOn_val_map {U B : Type} [CommRing U] [CommRing B] (w : U →+* B) (x : Uˣ) (y : Bˣ)
    (h : (y : B) = w x) : (unitOn y).val = (spMap w).appTop.hom (unitOn x).val := by
  have k := congrArg (fun φ => φ.hom (x : U)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom w))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at k
  change (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (y : B) = _
  rw [h]
  exact k

theorem exists_point {A B X : Type} [CommRing A] [CommRing B] [AddCommGroup X] (f : A →+* B)
    (τ : Multiplicative X →* Bˣ) : ∃ z : Over.mk (spMap f) ⟶ splitTorus (Sp A) X,
      ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ)) := by
  refine ⟨(GlobalTheory.splitTorusPointsEquiv (Sp A) X (Over.mk (spMap f))).symm
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toMonoidHom).comp τ), fun χ => ?_⟩
  rw [GlobalTheory.UU.chV, MulEquiv.apply_symm_apply]
  rfl

theorem toric_section_eq_over_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W]
    (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') (k : ℕ)
    (s' : ∀ (A : Type) [CommRing A] (a : W →+* A) (τ : Multiplicative P'.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t'.G)),
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : W →+* A) (ha : ∀ x ∈ maximalIdeal W, a x = 0) (a' : W →+* A')
      (f : A →+* A') (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t' (spMap a)) τ h
      (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P'.D.toPre.X),
      a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
      (s' A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P' ha m₀).left ≫ m₀.φ) →
    ∀ (R : Type) [CommRing R] (t : SAB H (Sp R)) (g : R →+* W) (m : SABMap t' t (spMap g))
      (V : Type) [CommRing V] (ψ : R →+* V) (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
      (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
      (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
      (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G),
      GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
      n.φ ≫ mV.φ = n'.φ ≫ m.φ →
    ∀ (Ω' : Type) [Field Ω'] (σ : Ω →+* Ω') (a' : W →+* Ω'), a' = σ.comp β →
    ∀ (U : Type) [CommRing U] (u : V →+* U) (w : U →+* Ω'), w.comp u = σ.comp α →
    ∀ (τU : Multiplicative P'.D.toPre.X →* Uˣ) (τ'' : Multiplicative P'.D.toPre.X →* Ω'ˣ) (h : τ'' ^ k = 1),
      (∀ χ, (τ'' χ : Ω') = w (τU χ : U)) →
    ∀ (z : Over.mk (spMap u) ⟶ splitTorus (Sp V) P'.D.toPre.X),
      (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τU (Multiplicative.ofAdd χ))) →
      (s' Ω' a' τ'' h).left ≫ m.φ = spMap w ≫ (z ≫ j).left ≫ mV.φ := by
  intro E _ _ _ H W _ _ _ t' P' k s' hs R _ t g m V _ ψ tV mV Ω _ α β hβ tΩ n n' j hj hn
    Ω' _ σ a' ha' U _ u w hw τU τ'' h hτ z hz
  obtain ⟨z', hz'⟩ := exists_point σ τ''
  have key : z'.left ≫ SplitTorus.bcMap (spMap α) P'.D.toPre.X = spMap w ≫ z.left := by
    refine GlobalTheory.UU.splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
    · rw [Category.assoc, SplitTorus.bcMap_hom, ← Category.assoc, Over.w z', Category.assoc, Over.w z]
      change spMap σ ≫ spMap α = spMap w ≫ spMap u
      simp only [spMap]
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hw]
    · rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, GlobalTheory.UU.bcMap_charUnit,
        Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
      have e1 := (GlobalTheory.UU.chV_val z' χ).symm.trans (congrArg Units.val (hz' χ))
      have e2 := (GlobalTheory.UU.chV_val z χ).symm.trans (congrArg Units.val (hz χ))
      exact e1.trans ((unitOn_val_map w _ _ (hτ _)).trans (congrArg _ e2.symm))
  rw [hs Ω Ω' β hβ a' σ tΩ n' τ'' h z' ha' hz', ← hj, Category.assoc, ← hn, Over.comp_left, Over.comp_left,
    Category.assoc, ← Category.assoc _ n.φ, GlobalTheory.TorusPart.pullTorus_left, Category.assoc,
    ← Category.assoc z'.left, key]
  simp only [Category.assoc]

end GlobalTheory.ToricOverField
