import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FlatBaseChangeSections

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem subring_subtype_flat {k : Type} [Field k] (R : Subring k) : R.subtype.Flat := by
  have : FaithfulSMul R k := (faithfulSMul_iff_algebraMap_injective R k).2 R.subtype_injective
  let _ := FractionRing.liftAlgebra R k
  have := FractionRing.isScalarTower_liftAlgebra R k
  have h1 : Module.Flat R (FractionRing R) := IsLocalization.flat _ (nonZeroDivisors R)
  have h2 : Module.Flat R k := Module.Flat.trans R (FractionRing R) k
  exact (RingHom.flat_algebraMap_iff (R := R) (S := k)).2 h2

theorem resG_cstOn_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (c : R) : resG X h (cstOn p U c) = cstOn p V c := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top ≫
    X.presheaf.map (homOfLE h).op).hom c = _
  erw [Scheme.Hom.appLE_map]
  rfl

theorem app_cstOn_const {R : Type} [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp R) (j : Y ⟶ X)
    {U : X.Opens} {V : Y.Opens} (h : V ≤ j ⁻¹ᵁ U) (c : R) :
    resG Y h ((j.app U).hom (cstOn p U c)) = cstOn (j ≫ p) V c := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top ≫ j.appLE U V h).hom c = _
  exact congrArg (fun g => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g).hom c)
    (Scheme.Hom.appLE_comp_appLE j p ⊤ U V le_top h)

theorem cstOn_comp_spMap_const {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : Scheme.{0}}
    (p : X ⟶ Sp R') (U : X.Opens) (c : R) : cstOn (p ≫ spMap φ) U c = cstOn p U (φ c) := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (p ≫ spMap φ).appLE ⊤ U le_top =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫ p.appLE ⊤ U le_top := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    erw [Scheme.Hom.comp_appLE]
    rfl
  exact congrArg (fun g => g.hom c) e

def secComb {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} {n : ℕ}
    (c : Fin n → R) (τ : Fin n → L.Sec) : L.Sec where
  f i := ∑ a, cstOn p _ (c a) * (τ a).f i
  compat i j := by
    change resG X _ _ = _ * resG X _ _
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, map_mul, resG_cstOn_const, resG_cstOn_const, mul_left_comm]
    exact congrArg _ ((τ a).compat i j)

theorem resG_comb_pull {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X X₁ X₀ : Scheme.{0}}
    (f : X ⟶ Sp R') (f₁ : X₁ ⟶ Sp R) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁) (hf : j ≫ f₁ = f ≫ spMap φ)
    {n : ℕ} (c : Fin n → R) {U₀ : X₀.Opens} (t : Fin n → Γ(X₀, U₀)) {U₁ : X₁.Opens} {V V' W : X.Opens}
    (h₁ : U₁ ≤ π₁ ⁻¹ᵁ U₀) (hV : V ≤ j ⁻¹ᵁ U₁) (hV' : V' ≤ (j ≫ π₁) ⁻¹ᵁ U₀) (hW' : W ≤ V') (hW : W ≤ V) :
    resG X hW' (∑ a, cstOn f V' (φ (c a)) * resG X hV' (((j ≫ π₁).app U₀).hom (t a))) =
      resG X hW (resG X hV ((j.app U₁).hom
        (∑ a, cstOn f₁ U₁ (c a) * resG X₁ h₁ ((π₁.app U₀).hom (t a))))) := by
  rw [Cartier.resG_resG, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_mul, map_mul, app_cstOn_const, resG_cstOn_const, hf, cstOn_comp_spMap_const,
    Cartier.app_resG, Cartier.resG_resG, Cartier.resG_resG]
  rfl

theorem exists_finset_sec_descends : ∀ (k : Type) [Field k] (R₀ : Subring k) (X X₀ : Scheme.{0}) (f : X ⟶ Sp k) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [IsProper f₀] (L : LB X₀) (σ : (L.pull π).Sec), IsPullback π f f₀ (spMap R₀.subtype) → L.IsLB → ∃ F : Finset k, ∀ (R₁ : Subring k) (hR : R₀ ≤ R₁), (F : Set k) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hR)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ τ : (L.pull π₁).Sec, SameDiv σ (Cartier.secPull τ j) := by
  classical
  intro k _ R₀ X X₀ f f₀ π _ L σ hπ hL
  obtain ⟨n, c, τ, hσ⟩ := GlobalTheory.T.flat_base_change_sections R₀ k R₀.subtype X₀ X f₀ f π L (subring_subtype_flat R₀) hπ hL σ
  refine ⟨Finset.univ.image c, fun R₁ hR hF X₁ f₁ π₁ j _ hj hf => ?_⟩
  subst hj
  let c₁ : Fin n → R₁ := fun a => ⟨c a, hF (by simp)⟩
  refine ⟨secComb f₁ c₁ fun a => Cartier.secPull (τ a) π₁, fun x => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ ((j ≫ π₁) x)))
  have h1 : (j ≫ π₁) ⁻¹ᵁ L.U i ≤ (L.pull (j ≫ π₁)).U fun _ => i := (Cartier.pull_U L _ fun _ => i).ge
  have h2 : (j ≫ π₁) ⁻¹ᵁ L.U i ≤ ((L.pull π₁).pull j).U fun _ _ => i :=
    (j.preimage_mono (Cartier.pull_U L π₁ fun _ => i).ge).trans
      (Cartier.pull_U (L.pull π₁) j fun _ _ => i).ge
  refine ⟨(j ≫ π₁) ⁻¹ᵁ L.U i, fun _ => i, fun _ _ => i, h1, h2, 1, hi, ?_⟩
  refine Eq.trans ?_ (one_mul _).symm
  refine (congrArg (resG X h1) (hσ fun _ => i)).trans ?_
  exact resG_comb_pull R₁.subtype f f₁ π₁ j hf c₁ (fun a => (τ a).f i)
    (Cartier.pull_U L π₁ fun _ => i).le (Cartier.pull_U (L.pull π₁) j fun _ _ => i).le
    (Cartier.pull_U L (j ≫ π₁) fun _ => i).le h1 h2

end GlobalTheory.LogPair
