import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerSquaresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheafStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FormalAlg.LevSurj

theorem appLE_cst {R : Type} [CommRing R] {X X' : Scheme.{0}} (g : X' ⟶ X) (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.Opens) (V : X'.Opens) (h : V ≤ g ⁻¹ᵁ U) (a : R) :
    (g.appLE U V h).hom (AbLaw.cst f U a) = AbLaw.cst (g ≫ f) V a := by
  simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  change ((X.presheaf.map (homOfLE le_top).op ≫ g.appLE U V h).hom) _ =
    ((g.appTop ≫ X'.presheaf.map (homOfLE le_top).op).hom) _
  rw [Scheme.Hom.map_appLE]
  rfl

theorem appLE_of_eq {X X' : Scheme.{0}} (g : X' ⟶ X) (U : X.Opens) (V : X'.Opens) (hV : g ⁻¹ᵁ U = V)
    (h : V ≤ g ⁻¹ᵁ U) (hs : Function.Surjective (g.app U).hom) :
    Function.Surjective (g.appLE U V h).hom ∧ RingHom.ker (g.appLE U V h).hom = RingHom.ker (g.app U).hom := by
  subst hV
  have : g.appLE U (g ⁻¹ᵁ U) h = g.app U := by simp [Scheme.Hom.appLE]
  rw [this]
  exact ⟨hs, rfl⟩

end GlobalTheory.FormalAlg.LevSurj

namespace GlobalTheory.FormalAlg.LevSurj

theorem ev_surjective : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), (∀ e (V : (Y e).left.Opens), towerIdeal Y e (I ^ (e + 1)) V = ⊥) ∧ ∀ e i, Function.Surjective (C.ev e i) := by
  intro R _ I Y β hβ n C
  have h1 : ∀ e (V : (Y e).left.Opens), towerIdeal Y e (I ^ (e + 1)) V = ⊥ := by
    intro e V
    rw [towerIdeal, show thick R I e = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))) from rfl,
      cst_comp_spec, ← Ideal.map_map, Ideal.map_quotient_self, Ideal.map_bot]
  refine ⟨h1, fun e i => ?_⟩
  induction e with
  | zero =>
    have hc : AbLaw.cst ((Y 0).hom ≫ thick R I 0) (C.D 0 i) =
        (AbLaw.cst (Y 0).hom (C.D 0 i)).comp (Ideal.Quotient.mk _) := cst_comp_spec _ _ _
    have : C.ev 0 i = (MvPolynomial.eval₂Hom (AbLaw.cst (Y 0).hom (C.D 0 i)) (C.ρ 0 i)).comp
        (MvPolynomial.map (Ideal.Quotient.mk _)) := by
      ext <;> simp [Charts.ev, hc]
    rw [this]
    exact (C.surj i).comp (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective)
  | succ e ih =>
    have hp : β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := by
      rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
    have hev : ((β e).appLE (C.D (e + 1) i) (C.D e i) (C.pre e i).ge).hom.comp (C.ev (e + 1) i) = C.ev e i := by
      rw [Charts.ev, MvPolynomial.comp_eval₂Hom, Charts.ev]
      congr 1
      · ext a
        simp only [RingHom.comp_apply]
        rw [appLE_cst]
        exact congrArg (fun q => AbLaw.cst q (C.D e i) a) (by simpa only [Category.assoc] using hp)
      · funext j
        exact C.ρ_pull e i j
    have hk := (GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) (Y (e + 1)).left (Y e).left ((Y (e + 1)).hom ≫ thick R I (e + 1))
      (β e) (Y e).hom ((GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).1 e)).2.2 (C.D (e + 1) i) (C.aff (e + 1) i)
    obtain ⟨hr, hker⟩ := appLE_of_eq (β e) (C.D (e + 1) i) (C.D e i) (C.pre e i) (C.pre e i).ge hk.1
    rw [hk.2] at hker
    set r := ((β e).appLE (C.D (e + 1) i) (C.D e i) (C.pre e i).ge).hom with hr_def
    set c := AbLaw.cst ((Y (e + 1)).hom ≫ thick R I (e + 1)) (C.D (e + 1) i) with hc_def
    set S := (C.ev (e + 1) i).range with hS_def
    have hsq : ∀ x y, x ∈ RingHom.ker r → y ∈ RingHom.ker r → x * y = 0 := by
      intro x y hx hy
      rw [hker] at hx hy
      have hxy := Ideal.mul_mem_mul hx hy
      rw [← Ideal.map_mul, ← pow_add] at hxy
      have hle : (I ^ (e + 1 + (e + 1))).map c ≤ (I ^ (e + 1 + 1)).map c :=
        Ideal.map_mono (Ideal.pow_le_pow_right (by omega))
      have h0 : (I ^ (e + 1 + 1)).map c = ⊥ := h1 (e + 1) (C.D (e + 1) i)
      have := hle hxy
      rw [h0] at this
      exact (Submodule.mem_bot _).1 this
    have hsplit : ∀ b, ∃ s ∈ S, b - s ∈ RingHom.ker r := by
      intro b
      obtain ⟨P, hP⟩ := ih (r b)
      refine ⟨C.ev (e + 1) i P, ⟨P, rfl⟩, ?_⟩
      rw [RingHom.mem_ker, map_sub, ← hP, ← hev, RingHom.comp_apply, sub_self]
    have hKS : ∀ x ∈ RingHom.ker r, x ∈ S := by
      intro x hx
      have hx' := hx
      rw [hker] at hx'
      change x ∈ Submodule.span _ _ at hx'
      induction hx' using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, -, rfl⟩ := hy
        exact ⟨MvPolynomial.C a, by simp [Charts.ev, c]⟩
      | zero => exact S.zero_mem
      | add y z hy hz ihy ihz =>
        have hy' : y ∈ RingHom.ker r := hker ▸ hy
        have hz' : z ∈ RingHom.ker r := hker ▸ hz
        exact S.add_mem (ihy hy') (ihz hz')
      | smul a y hy ihy =>
        have hy' : y ∈ RingHom.ker r := hker ▸ hy
        obtain ⟨s, hs, has⟩ := hsplit a
        have : a • y = s * y + (a - s) * y := by rw [smul_eq_mul]; ring
        rw [this, hsq _ _ has hy', add_zero]
        exact S.mul_mem hs (ihy hy')
    intro b
    obtain ⟨s, hs, hbs⟩ := hsplit b
    have : b ∈ S := by
      have := S.add_mem hs (hKS _ hbs)
      rwa [add_sub_cancel] at this
    exact this

end GlobalTheory.FormalAlg.LevSurj
