import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueStalkHomPadicAlgClosureValuation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFiniteTypeIntOfModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicMemRangeCompleteDvrPadicAlgCl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionCompleteDvrPadicAlgCl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

theorem GlobalTheory.ValPt.exists_dvr_factor : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → ∀ (κ : FractionRing V →+* PadicAlgCl p), (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → ∀ y : Sp (OO p) ⟶ M.Z, ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (fV : V →+* V') (fK : FractionRing V →+* FractionRing V') (κ' : FractionRing V' →+* PadicAlgCl p) (iV : V' →+* OO p) (ξ : Sp V' ⟶ M.Z), IsLocalHom fV ∧ (∀ x, fK (algebraMap V _ x) = algebraMap V' _ (fV x)) ∧ κ'.comp fK = κ ∧ IsLocalHom iV ∧ (∀ x, (iV x : PadicAlgCl p) = κ' (algebraMap V' _ x)) ∧ spMap iV ≫ ξ = y := by
  intro o Ω _ _ _ _ M p _ V _ _ _ hc κ hV y

  haveI : CharZero (FractionRing V) := κ.charZero
  haveI : CharZero V := (algebraMap V (FractionRing V)).charZero
  set x : M.Z := y (cPt p) with hxdef
  obtain ⟨φ, hφloc, hφ, -⟩ := GlobalTheory.ValPt.exists_unique_stalk_hom M.Z x p y rfl
  obtain ⟨U, hU, hxU, hft⟩ := GlobalTheory.RatModel.exists_affineOpen_finiteType_int o Ω M x
  have hQ := GlobalTheory.PadicUnitBall.padic_mem_range p V hc κ hV
  let y₀ : Γ(M.Z, U) →+* PadicAlgCl p := (OO p).subtype.comp (φ.comp (M.Z.presheaf.germ U x hxU).hom)
  obtain ⟨W, _, _, _, hcW, _, fV, fK, κ', -, hfVloc, -, hfK, hκ', hW, hy₀⟩ :=
    GlobalTheory.DvrFinExt.exists_finite_extension p V hc κ hV hQ Γ(M.Z, U) y₀
  let j : W →+* PadicAlgCl p := κ'.comp (algebraMap W (FractionRing W))
  have hj : Function.Injective j :=
    κ'.injective.comp (IsFractionRing.injective W (FractionRing W))
  let ψ : M.Z.presheaf.stalk x →+* PadicAlgCl p := (OO p).subtype.comp φ

  have hψK : ∀ s, ψ s ∈ κ'.range := by
    intro s
    let xU : U := ⟨x, hxU⟩
    letI := M.Z.presheaf.algebra_section_stalk xU
    haveI := hU.isLocalization_stalk xU
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (hU.primeIdealOf xU).asIdeal.primeCompl (show M.Z.presheaf.stalk (xU : M.Z) from s)
    have hb : IsUnit (algebraMap Γ(M.Z, U) (M.Z.presheaf.stalk (xU : M.Z)) (b : Γ(M.Z, U))) :=
      IsLocalization.map_units _ b
    have hb' : ψ (algebraMap Γ(M.Z, U) (M.Z.presheaf.stalk (xU : M.Z)) (b : Γ(M.Z, U))) ≠ 0 :=
      ((hb.map φ).map (OO p).subtype).ne_zero
    have hga : ∀ c : Γ(M.Z, U), ψ (algebraMap Γ(M.Z, U) (M.Z.presheaf.stalk (xU : M.Z)) c) = y₀ c := fun c => rfl
    obtain ⟨ka, hka⟩ := hy₀ a
    obtain ⟨kb, hkb⟩ := hy₀ (b : Γ(M.Z, U))
    have e1 : ψ s * y₀ b = y₀ a := by
      rw [← hga, ← hga, ← map_mul, hab]
    have hb'' : y₀ b ≠ 0 := by rw [← hga]; exact hb'
    refine ⟨ka * kb⁻¹, ?_⟩
    rw [map_mul, map_inv₀, hka, hkb, ← e1, mul_inv_cancel_right₀ hb'']
  have hψW : ∀ s, ψ s ∈ j.range := by
    intro s
    obtain ⟨k, hk⟩ := hψK s
    have hn : ‖κ' k‖ ≤ 1 := by rw [hk]; exact (mem_OO_iff _).1 (φ s).2
    obtain ⟨w, hw⟩ := (hW k).1 hn
    exact ⟨w, by rw [← hk, ← hw]; rfl⟩
  let e := RingEquiv.ofBijective j.rangeRestrict ⟨fun a b h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  let φ' : M.Z.presheaf.stalk x →+* W := e.symm.toRingHom.comp (ψ.codRestrict j.range hψW)
  have hjφ' : ∀ s, j (φ' s) = ψ s := by
    intro s
    have h := e.apply_symm_apply (ψ.codRestrict j.range hψW s)
    exact congrArg Subtype.val h
  have hjO : ∀ w, j w ∈ OO p := fun w => (mem_OO_iff _).2 ((hW _).2 ⟨w, rfl⟩)
  let iV : W →+* OO p := j.codRestrict (OO p) hjO
  have hiVloc : IsLocalHom iV := by
    constructor
    intro w hw
    obtain ⟨u, hu⟩ := hw
    have hw0 : j w ≠ 0 := by
      intro h0
      have : ((u : OO p) : PadicAlgCl p) = 0 := by rw [hu]; exact h0
      exact u.ne_zero (Subtype.ext this)
    have hwne : algebraMap W (FractionRing W) w ≠ 0 := fun h => hw0 (by simp [j, h])
    have hinv : ‖κ' (algebraMap W (FractionRing W) w)⁻¹‖ ≤ 1 := by
      have h1 : ((u⁻¹ : (OO p)ˣ) : OO p) * (u : OO p) = 1 := u.inv_mul
      have h2 : ((((u⁻¹ : (OO p)ˣ) : OO p) : PadicAlgCl p)) * j w = 1 := by
        have := congrArg (fun t : OO p => (t : PadicAlgCl p)) h1
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
        rw [hu] at this; exact this
      have h3 : κ' (algebraMap W (FractionRing W) w)⁻¹ = (((u⁻¹ : (OO p)ˣ) : OO p) : PadicAlgCl p) := by
        rw [map_inv₀]
        exact (eq_inv_of_mul_eq_one_left h2).symm
      rw [h3]; exact (mem_OO_iff _).1 (Subtype.prop _)
    obtain ⟨w', hw'⟩ := (hW _).1 hinv
    have hww : w * w' = 1 := by
      apply IsFractionRing.injective W (FractionRing W)
      rw [map_mul, hw', map_one, mul_inv_cancel₀ hwne]
    exact ⟨⟨w, w', hww, by rw [mul_comm]; exact hww⟩, rfl⟩
  have hcomp : iV.comp φ' = φ := by
    ext s
    exact hjφ' s
  refine ⟨W, inferInstance, inferInstance, inferInstance, fV, fK, κ', iV, spMap φ' ≫ M.Z.fromSpecStalk x,
    hfVloc, hfK, hκ', hiVloc, fun w => rfl, ?_⟩
  rw [← Category.assoc, ← hφ, ← hcomp]
  show (Spec.map (CommRingCat.ofHom iV) ≫ Spec.map (CommRingCat.ofHom φ')) ≫ _ = Spec.map (CommRingCat.ofHom (iV.comp φ')) ≫ _
  rw [← Spec.map_comp]
  rfl
