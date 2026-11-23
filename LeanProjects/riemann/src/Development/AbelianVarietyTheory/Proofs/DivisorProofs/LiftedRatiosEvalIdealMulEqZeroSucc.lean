import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerSquaresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheafStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

namespace GlobalTheory.FormalAlg.JStep

theorem appLE_cst {R : Type} [CommRing R] {X X' : Scheme.{0}} (g : X ⟶ X') (f : X' ⟶ Spec (CommRingCat.of R))
    (U' : X'.Opens) (U : X.Opens) (h : U ≤ g ⁻¹ᵁ U') (r : R) :
    (g.appLE U' U h).hom (AbLaw.cst f U' r) = AbLaw.cst (g ≫ f) U r := by
  simp only [AbLaw.cst, RingHom.comp_apply, rs]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply (g.appTop)]
  congr 1

theorem cst_pow_eq_zero {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (V : X.Opens) {a : R} (ha : a ∈ I ^ (e + 1)) :
    AbLaw.cst (p ≫ thick R I e) V a = 0 := by
  rw [thick, cst_comp_spec, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

theorem ev_succ_C_mul_eq_zero : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R) (i : Fin (n + 1)), a ∈ I → C.ev e i F = 0 → C.ev (e + 1) i (MvPolynomial.C a * F) = 0 := by
  intro R _ I Y β hpb n C e a F i ha hF
  have hsq := (GlobalTheory.T.isPullback_thick_tower_squares R I Y β hpb).1 e
  have hk := (GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) (Y (e + 1)).left (Y e).left ((Y (e + 1)).hom ≫ thick R I (e + 1))
    (β e) (Y e).hom hsq).2.2 (C.D (e + 1) i) (C.aff (e + 1) i)
  have hw : β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := by
    rw [← Category.assoc, (hpb e).w, Category.assoc, thickTrans_comp]

  have hev : ((β e).appLE (C.D (e + 1) i) (C.D e i) (C.pre e i).ge).hom (C.ev (e + 1) i F) = C.ev e i F := by
    have hcomp : ((β e).appLE (C.D (e + 1) i) (C.D e i) (C.pre e i).ge).hom.comp (C.ev (e + 1) i) = C.ev e i := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [Charts.ev, appLE_cst, hw]
      · intro j
        simp [Charts.ev, C.ρ_pull]
    exact RingHom.congr_fun hcomp F

  have hx : C.ev (e + 1) i F ∈ RingHom.ker ((β e).app (C.D (e + 1) i)).hom := by
    rw [RingHom.mem_ker]
    have h2 : ((β e).appLE (C.D (e + 1) i) (C.D e i) (C.pre e i).ge).hom (C.ev (e + 1) i F) =
        rs (Y e).left (C.pre e i).ge (((β e).app (C.D (e + 1) i)).hom (C.ev (e + 1) i F)) := rfl
    rw [hev, hF] at h2
    have h3 := congrArg (rs (Y e).left (C.pre e i).le) h2
    rw [map_zero, rs_rs, rs_self] at h3
    exact h3.symm
  rw [hk.2] at hx
  rw [map_mul, Charts.ev, MvPolynomial.eval₂Hom_C]
  have hm : AbLaw.cst ((Y (e + 1)).hom ≫ thick R I (e + 1)) (C.D (e + 1) i) a * C.ev (e + 1) i F ∈
      (I * I ^ (e + 1)).map (AbLaw.cst ((Y (e + 1)).hom ≫ thick R I (e + 1)) (C.D (e + 1) i)) := by
    rw [Ideal.map_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ ha) hx
  have hbot : (I * I ^ (e + 1)).map (AbLaw.cst ((Y (e + 1)).hom ≫ thick R I (e + 1)) (C.D (e + 1) i)) = ⊥ := by
    refine le_bot_iff.1 (Ideal.map_le_iff_le_comap.2 fun r hr => ?_)
    rw [← pow_succ'] at hr
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact cst_pow_eq_zero I (e + 1) (Y (e + 1)).hom _ hr
  rw [hbot] at hm
  exact (Ideal.mem_bot).1 hm

end GlobalTheory.FormalAlg.JStep
