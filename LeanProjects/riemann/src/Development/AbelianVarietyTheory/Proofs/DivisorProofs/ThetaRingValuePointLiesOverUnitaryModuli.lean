import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

noncomputable section

namespace GlobalTheory.GSep

theorem valPt_lies_over_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → ∀ (z₁ : X₁.M.Z) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (y : Sp (FractionRing V₁) ⟶ Xo.XF c), GlobalTheory.GSep.RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ π = y ≫ C.i → ∃ (yK : X₁.S.R →+* FractionRing V₁) (x' : Sp (FractionRing V₁) ⟶ Sp (ratHull X₁.S.R)), (∀ a, yK a = X₁.M.val (jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) ∧ x' ≫ spMap (toRat X₁.S.R) = spMap yK ∧ x' ≫ u = y := by
  intro E _ _ _ H Dw _ l Xo c C X₁ act u π hL z₁ V₁ _ _ _ ev y hreg hy
  set yw := jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hyw
  set w := yw (IsLocalRing.closedPoint (FractionRing V₁)) with hw
  have hle : X₁.S.R ≤ X₁.M.O w := fun a ha => hreg a ha

  have hπw : π w = C.i (y (IsLocalRing.closedPoint (FractionRing V₁))) := by
    have h1 : yw ≫ π = y ≫ C.i := by simpa only [hyw, Category.assoc] using hy
    have h2 := congrArg (fun f => f (IsLocalRing.closedPoint (FractionRing V₁))) h1
    exact h2
  have hc : ∀ n : ℤ, n ≠ 0 → IsUnit (n : X₁.M.O w) := fun n hn => by
    rw [← map_intCast (X₁.M.stalkEquiv w) n, MulEquiv.isUnit_map, ← map_intCast (π.stalkMap w).hom n,
      isUnit_map_iff, hπw, ← isUnit_map_iff (C.i.stalkMap _).hom, map_intCast]
    have h : IsUnit (n : c.F) := IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)
    have h' := ((h.map (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom).map
      ((Sp c.F).presheaf.germ ⊤ ((pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) (y (IsLocalRing.closedPoint (FractionRing V₁))))
        trivial).hom).map ((pullback.snd _ _ : Xo.XF c ⟶ Sp c.F).stalkMap _).hom
    rwa [map_intCast, map_intCast, map_intCast] at h'
  have hle' : ratHull X₁.S.R ≤ X₁.M.O w := fun x hx => by
    obtain ⟨n, hn, h⟩ := mem_ratHull.1 hx
    obtain ⟨h1, h2⟩ := (RatModel.isUnit_O_iff _).1 (hc n hn)
    have e : ((n : X₁.M.O w) : X₁.Ω₁) = n := by simp
    rw [e] at h1 h2
    have := mul_mem h2 (hle h)
    rwa [inv_mul_cancel_left₀ h1] at this
  have hsp : yw (IsLocalRing.closedPoint (FractionRing V₁)) ⤳ w := specializes_rfl
  let ψ : ratHull X₁.S.R →+* X₁.M.Z.presheaf.stalk w :=
    (X₁.M.stalkEquiv w).symm.toRingHom.comp (Subalgebra.inclusion hle').toRingHom
  let φ : X₁.M.Z.presheaf.stalk w →+* FractionRing V₁ := (X₁.M.Z.presheaf.stalkSpecializes hsp ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of (FractionRing V₁)) yw).hom
  have hK : (RatModel.valHom yw w (RatModel.range_eq_singleton yw _)).comp (Subalgebra.inclusion hle).toRingHom =
      (φ.comp ψ).comp (toRat X₁.S.R) :=
    RingHom.ext fun a => (RatModel.valLoc_eq_val yw hsp (Subalgebra.inclusion hle a)).symm
  refine ⟨(RatModel.valHom yw w (RatModel.range_eq_singleton yw _)).comp (Subalgebra.inclusion hle).toRingHom,
    spMap (φ.comp ψ), fun a => rfl, ?_, ?_⟩
  · rw [hK]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI := C.isPreimmersion_i
  haveI : IsProper C.z := GlobalTheory.ThetaDescent.isProper_of_isProjOver C.proj
  haveI : C.Z.IsSeparated := by
    constructor
    rw [← terminal.comp_from C.z]
    infer_instance
  haveI : IsDominant (spMap (X₁.M.stalkHom w)) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (X₁.M.stalkHom w))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (X₁.M.stalkHom_injective w)]
    exact bot_le
  have hfs : ∀ {B : Type} [CommRing B] [IsLocalRing B] (q : Sp B ⟶ X₁.M.Z) (h : q (IsLocalRing.closedPoint B) ⤳ w),
      spMap (X₁.M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of B) q).hom ≫
        X₁.M.Z.fromSpecStalk w = q := by
    intro B _ _ q h
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of B) q
  have e1 : spMap (X₁.M.stalkHom w) ≫ spMap ψ = spMap (ratHull X₁.S.R).val.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun a => congrArg Subtype.val ((X₁.M.stalkEquiv w).apply_symm_apply (Subalgebra.inclusion hle' a))
  have e2 : spMap (X₁.M.stalkHom w) ≫ X₁.M.Z.fromSpecStalk w = X₁.M.pt :=
    hfs X₁.M.pt (X₁.M.pt_specializes _ w)
  have hab : spMap ψ ≫ u ≫ C.i = X₁.M.Z.fromSpecStalk w ≫ π := by
    refine ext_of_isDominant (spMap (X₁.M.stalkHom w)) ?_
    rw [reassoc_of% e1, reassoc_of% e2, hL.2.2.2]
  have e3 : spMap φ ≫ X₁.M.Z.fromSpecStalk w = yw := hfs yw hsp
  rw [← cancel_mono C.i, Category.assoc]
  rw [show spMap (φ.comp ψ) = spMap φ ≫ spMap ψ by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp], Category.assoc, hab, reassoc_of% e3, ← hy]
  simp only [hyw, Category.assoc]

end GlobalTheory.GSep
