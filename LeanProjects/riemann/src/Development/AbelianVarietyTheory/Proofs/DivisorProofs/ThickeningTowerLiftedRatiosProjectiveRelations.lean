import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerSquaresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheafStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLbOfGeneratedSystem
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.LiftRatios

theorem appLE_rs {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens} (hU : U' ≤ U) (hV : V' ≤ V)
    (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ f ⁻¹ᵁ U') (y : Γ(Y, U)) :
    (f.appLE U' V' h').hom (rs Y hU y) = rs X hV ((f.appLE U V h).hom y) := by
  change (Y.presheaf.map (homOfLE hU).op ≫ f.appLE U' V' h').hom y =
    (f.appLE U V h ≫ X.presheaf.map (homOfLE hV).op).hom y
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem app_cst_comp {R : Type} [CommRing R] {X X' : Scheme.{0}} (φ : X' ⟶ X) (f : X ⟶ Spec (CommRingCat.of R))
    (V : X.Opens) (r : R) : (φ.app V).hom (cst f V r) = cst (φ ≫ f) (φ ⁻¹ᵁ V) r := by
  have e := Scheme.Hom.appLE_comp_appLE φ f ⊤ V (φ ⁻¹ᵁ V) (by simp) le_rfl
  rw [Scheme.Hom.app_eq_appLE]
  exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) e

theorem preimage_injective {X Y : Scheme.{0}} (f : X ⟶ Y) (hf : Surjective f) {U U' : Y.Opens}
    (h : f ⁻¹ᵁ U = f ⁻¹ᵁ U') : U = U' := by
  refine SetLike.ext fun y => ?_
  obtain ⟨z, rfl⟩ := hf.surj y
  rw [← Scheme.Hom.mem_preimage, ← Scheme.Hom.mem_preimage, h]

theorem mem_of_appLE_mem (R : Type) [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (e : ℕ)
    (V : (Y (e + 1)).left.Opens) (hV : IsAffineOpen V) (W : (Y e).left.Opens) (hW : β e ⁻¹ᵁ V = W)
    (x : Γ((Y (e + 1)).left, V)) (hx : ((β e).appLE V W hW.ge).hom x ∈ towerIdeal Y e I W) :
    x ∈ towerIdeal Y (e + 1) I V := by
  subst hW
  rw [Scheme.Hom.appLE_eq_app] at hx
  obtain ⟨-, -, hk⟩ := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) _ _ ((Y (e + 1)).hom ≫ thick R I (e + 1)) (β e) (Y e).hom
    ((GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).1 e)
  obtain ⟨hs, hker⟩ := hk V hV
  have hc : β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := by
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  have hmap : Ideal.map ((β e).app V).hom (towerIdeal Y (e + 1) I V) = towerIdeal Y e I (β e ⁻¹ᵁ V) := by
    unfold towerIdeal
    rw [Ideal.map_map]
    congr 1
    ext r
    rw [RingHom.comp_apply, app_cst_comp, hc]
  have hx' : x ∈ Ideal.comap ((β e).app V).hom (Ideal.map ((β e).app V).hom (towerIdeal Y (e + 1) I V)) := by
    rw [hmap]
    exact hx
  rw [Ideal.comap_map_of_surjective _ hs] at hx'
  have hle : Ideal.comap ((β e).app V).hom ⊥ ≤ towerIdeal Y (e + 1) I V := by
    intro y hy
    have hy' : y ∈ RingHom.ker ((β e).app V).hom := hy
    rw [hker] at hy'
    exact Ideal.map_mono (Ideal.pow_le_self (Nat.succ_ne_zero e)) hy'
  exact SetLike.le_def.1 (sup_le le_rfl hle) hx'

theorem lifted_ratios_mod : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), (∀ e i j, (Y e).left.basicOpen (C.ρ e i j) = C.D e i ⊓ C.D e j) ∧ (∀ e i, C.ρ e i i - 1 ∈ towerIdeal Y e I (C.D e i)) ∧ ∀ e i j l, rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i l) - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) * rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (C.ρ e j l) ∈ towerIdeal Y e I (C.D e i ⊓ C.D e j) := by
  intro R _ I Y β hβ n C
  have hsur : ∀ e, Surjective (β e) := fun e =>
    MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (GlobalTheory.GenSystem.surjective_thickTrans R I e)
  have h1 : ∀ e i j, (Y e).left.basicOpen (C.ρ e i j) = C.D e i ⊓ C.D e j := by
    intro e
    induction e with
    | zero => exact C.basic
    | succ e ih =>
      intro i j
      refine preimage_injective (β e) (hsur e) ?_
      have hb := Scheme.basicOpen_appLE (β e) (C.D e i) (C.D (e + 1) i) (C.pre e i).ge (C.ρ (e + 1) i j)
      rw [C.ρ_pull, ih] at hb
      rw [Scheme.Hom.preimage_inf, C.pre, C.pre, hb]
      exact (inf_eq_right.2 ((Scheme.Hom.preimage_mono (β e) (Scheme.basicOpen_le _ _)).trans
        (C.pre e i).le)).symm
  refine ⟨h1, ?_, ?_⟩
  · intro e
    induction e with
    | zero =>
      intro i
      rw [C.ρ_self, sub_self]
      exact Ideal.zero_mem _
    | succ e ih =>
      intro i
      refine mem_of_appLE_mem R I Y β hβ e _ (C.aff (e + 1) i) _ (C.pre e i) _ ?_
      rw [map_sub, map_one, C.ρ_pull]
      exact ih i
  · intro e
    induction e with
    | zero =>
      intro i j l
      rw [C.cocycle, sub_self]
      exact Ideal.zero_mem _
    | succ e ih =>
      intro i j l
      have hV : IsAffineOpen (C.D (e + 1) i ⊓ C.D (e + 1) j) := by
        rw [← h1 (e + 1) i j]
        exact (C.aff (e + 1) i).basicOpen _
      have hW : β e ⁻¹ᵁ (C.D (e + 1) i ⊓ C.D (e + 1) j) = C.D e i ⊓ C.D e j := by
        rw [Scheme.Hom.preimage_inf, C.pre, C.pre]
      refine mem_of_appLE_mem R I Y β hβ e _ hV _ hW _ ?_
      rw [map_sub, map_mul, appLE_rs (β e) _ inf_le_left (C.pre e i).ge, appLE_rs (β e) _ inf_le_left (C.pre e i).ge,
        appLE_rs (β e) _ inf_le_right (C.pre e j).ge, C.ρ_pull, C.ρ_pull, C.ρ_pull]
      exact ih i j l

end GlobalTheory.FormalAlg.LiftRatios
