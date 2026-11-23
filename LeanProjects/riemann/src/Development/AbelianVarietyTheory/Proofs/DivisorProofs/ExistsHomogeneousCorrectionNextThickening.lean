import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCorrectionNextLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsXPowMulSubMemVanishingIdealReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerSquaresStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem veryAmpleBy_comp_quotient {X : Scheme.{0}} {R : Type} [CommRing R] (J : Ideal R)
    (f : X ⟶ Spec (CommRingCat.of (R ⧸ J))) (H : LB X) {m : ℕ} (s : Fin (m + 1) → LB.Sec H)
    (h : VeryAmpleBy f H s) :
    VeryAmpleBy (f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) H s := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun i => ?_⟩
  obtain ⟨ha, r, hr, hsurj⟩ := h2 i
  refine ⟨ha, r, hr, fun y => ?_⟩
  obtain ⟨P, rfl⟩ := hsurj y
  obtain ⟨P', rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective P
  refine ⟨P', ?_⟩
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map, cst_comp_spec]

theorem exists_homogeneous_correction_succ : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ t₀ : ℕ, ∀ t, t₀ ≤ t → ∀ (e : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ vanIdeal ((Y e).hom ≫ thick R I e) (s e) → ∃ G : MvPolynomial (Fin (n + 1)) R, G.IsHomogeneous t ∧ (∀ d, MvPolynomial.coeff d G ∈ I ^ (e + 1)) ∧ F - G ∈ vanIdeal ((Y (e + 1)).hom ≫ thick R I (e + 1)) (s (e + 1)) := by
  intro R _ _ I Y β hβ H v hH n s hs hva
  have hVA : ∀ e, VeryAmpleBy (Y e).hom (H e) (s e) := by
    rintro (_ | e)
    · exact hva
    · obtain ⟨j₀, hj, w, hw, hr⟩ := tower I Y β hβ H v hH s hs e
      exact GlobalTheory.AbLaw.veryAmpleBy_of_isNilpotent _ _ _ (Ideal.Quotient.factor_surjective _)
        (GlobalTheory.Degen.isNilpotent_ker_factor_pow I _)
        _ _ _ _ j₀ hj _ _ w n _ _ (hH _).1 (hH _).1 ((isGen_iff _).2 hw) hr hva
  have hVAR : ∀ e, VeryAmpleBy ((Y e).hom ≫ thick R I e) (H e) (s e) := fun e =>
    veryAmpleBy_comp_quotient _ _ _ _ (hVA e)
  have c₁ : ∀ e, β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := fun e => by
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  have hpb := (GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).1
  exact GlobalTheory.T.homogeneous_correction_next_level_alt R I n (fun e => vanIdeal ((Y e).hom ≫ thick R I e) (s e))
    (fun e _ _ _ h => mem_vanIdeal_of_sat _ _ (hVA e).1 h)
    (fun e a ha => (mem_vanIdeal _ _ _).2 fun k => by
      rw [MvPolynomial.eval₂Hom_C, cst_comp_spec, RingHom.comp_apply,
        Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero])
    (fun e t F hF hK i => GlobalTheory.T.exists_X_pow_mul_sub_mem_vanishingIdeal_reduction R (I ^ (e + 1)) (Y (e + 1)).left (Y e).left
      ((Y (e + 1)).hom ≫ thick R I (e + 1)) (β e) (Y e).hom (hpb e) (H (e + 1)) (H e) (v e) n (s (e + 1)) (s e)
      (hH _).1 (hH _).1 (hH e).2 (hs e) (hVAR (e + 1)) t F hF (by rw [c₁]; exact hK) i)

end GlobalTheory.FormalAlg
