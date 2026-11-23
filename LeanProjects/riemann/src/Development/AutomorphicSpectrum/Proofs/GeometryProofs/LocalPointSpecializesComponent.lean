import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEig
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointNormalCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermStalkClosedPointToBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldMapsLocalRingUniqueStatement

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.Coef

section General

variable {X : Scheme.{0}} {K R : Type} [CommRing K] [CommRing R] [IsLocalRing R]

def cst (g : X ⟶ Sp K) (x : X) : K →+* X.presheaf.stalk x :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp g.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem stalkClosedPointTo_germ_top (z : Sp R ⟶ X) (t : Γ(X, ⊤)) :
    (Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ ⊤ (centre z) trivial).hom t) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z.appTop.hom t) := by
  have h : X.presheaf.germ ⊤ (centre z) trivial ≫ Scheme.stalkClosedPointTo z =
      z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    refine (Scheme.germ_stalkClosedPointTo z ⊤ trivial).trans ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
    congr 1
  exact congrArg (fun q => q.hom t) h

theorem val_cst (z : Sp R ⟶ X) (g : X ⟶ Sp K) (φ : K →+* R) (h : z ≫ g = spMap φ) (k : K) :
    (Scheme.stalkClosedPointTo z).hom (cst g (centre z) k) = φ k := by
  show (Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ ⊤ (centre z) trivial).hom
    (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k))) = φ k
  rw [stalkClosedPointTo_germ_top]
  have h2 : z.appTop.hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k)) =
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k) := by
    have h' : z ≫ g = Spec.map (CommRingCat.ofHom φ) := h
    rw [← h']; simp only [Scheme.Hom.comp_appTop]; rfl
  rw [h2]
  have h3 := congrArg (fun q => q.hom k) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  have h3' : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (φ k) =
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k) := h3
  rw [← h3']
  simp

variable {Ω : Type} [Field Ω]

theorem genMap_cst (ξ : Sp Ω ⟶ X) (g : X ⟶ Sp K) (φ : K →+* Ω) (h : ξ ≫ g = spMap φ) (p : Cpt ξ) (k : K) :
    genMap ξ p (cst g p.1 k) = φ k := by
  have h1 : genMap ξ p (cst g p.1 k) = (Scheme.stalkClosedPointTo ξ).hom (cst g (centre ξ) k) :=
    congrArg (Scheme.stalkClosedPointTo ξ).hom
      (X.presheaf.germ_stalkSpecializes_apply (show p.1 ∈ (⊤ : X.Opens) from trivial) p.2 _)
  rw [h1, val_cst ξ g φ h]

theorem exists_lift {ξ : Sp Ω ⟶ X} {F : Type} [Field F] [NumberField F] (hξ : IsCptGen ξ) (hN : NormalCpt ξ)
    (p : Cpt ξ) (inc : F →+* Ω) (hq : ∀ n : ℕ, 0 < n → IsUnit (n : X.presheaf.stalk p.1)) :
    ∃ κ : F →+* X.presheaf.stalk p.1, (genMap ξ p).comp κ = inc := by
  haveI : CharZero Ω := charZero_of_injective_ringHom inc.injective
  have hinv : ∀ n : ℕ, 0 < n → ((n : Ω))⁻¹ ∈ regAt ξ p := by
    intro n hn
    obtain ⟨u, hu⟩ := hq n hn
    refine ⟨(u⁻¹ : _ˣ), ?_⟩
    have h1 : genMap ξ p u = (n : Ω) := by rw [hu, map_natCast]
    have h2 : genMap ξ p (u⁻¹ : _ˣ) * genMap ξ p u = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [h1] at h2
    exact eq_inv_of_mul_eq_one_left h2
  have hmem : ∀ r : ℚ, Rat.castHom Ω r ∈ regAt ξ p := by
    intro r
    rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
    exact mul_mem (intCast_mem _ _) (hinv r.den r.den_pos)
  let ψ : ℚ →+* regAt ξ p := (Rat.castHom Ω).codRestrict _ hmem
  have hint : ∀ a : F, inc a ∈ regAt ξ p := by
    intro a
    refine hN p _ ⟨(minpoly ℚ a).map ψ, (minpoly.monic (Algebra.IsIntegral.isIntegral a)).map ψ, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (regAt ξ p) Ω).comp ψ = inc.comp (algebraMap ℚ F) := Subsingleton.elim _ _
    rw [e, ← Polynomial.hom_eval₂]
    have := minpoly.aeval ℚ a
    rw [Polynomial.aeval_def] at this
    rw [this, map_zero]
  have hb : Function.Bijective (genMap ξ p).rangeRestrict :=
    ⟨fun a b hab => hξ.inj p (congrArg Subtype.val hab), (genMap ξ p).rangeRestrict_surjective⟩
  refine ⟨(RingEquiv.ofBijective _ hb).symm.toRingHom.comp (inc.codRestrict (genMap ξ p).range hint), ?_⟩
  ext a
  exact congrArg Subtype.val ((RingEquiv.ofBijective _ hb).apply_symm_apply (inc.codRestrict (genMap ξ p).range hint a))

end General

theorem exists_coef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (T : Type) [CommRing T] [IsLocalRing T] (y : Sp T ⟶ Xo.XF c) (c₀ : c.F →+* T), y ≫ pullback.snd _ _ = spMap c₀ → centre y ∈ U → ∃ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (κ : c.F →+* Y.X.presheaf.stalk (centre (y ≫ Y.j))), (genMap (Z.ξ₀ ≫ Y.j) ⟨_, h⟩).comp κ = Z.inc ∧ (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp κ = c₀ := by
  intro E _ _ _ H D l Xo c U O _ β Y Z T _ _ y c₀ hy hU
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have h0 : genPt Z.ξ₀ ⤳ centre y := (Z.closure _).1 hU
  have h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := h0.map Y.j.continuous
  refine ⟨h, ?_⟩
  have hN : NormalCpt (Z.ξ₀ ≫ Y.j) := XR.normalCpt_of_isCptGen Z.gen Y.normal
  have hq : ∀ n : ℕ, 0 < n → IsUnit (n : Y.X.presheaf.stalk (centre (y ≫ Y.j))) := by
    intro n hn
    haveI : IsLocalHom (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom := Scheme.isLocalHom_stalkClosedPointTo _
    have e : (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom (n : Y.X.presheaf.stalk (centre (y ≫ Y.j))) =
        c₀ (n : c.F) := (map_natCast _ n).trans (map_natCast c₀ n).symm
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom _
      ((congrArg IsUnit e).mpr ((IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')).map c₀))
  obtain ⟨κ, hκ⟩ := exists_lift Z.gen hN ⟨centre (y ≫ Y.j), h⟩ Z.inc hq
  refine ⟨κ, hκ, ?_⟩
  let π := genMap Z.ξ₀ ⟨centre y, h0⟩
  let s : c.F →+* (Xo.XF c).presheaf.stalk (centre y) := (Y.j.stalkMap (centre y)).hom.comp κ
  let t : c.F →+* (Xo.XF c).presheaf.stalk (centre y) := cst (pullback.snd _ _) (centre y)
  have hD : GlobalTheory.CompanionTheory.Ar.Dominates Z.ξ₀ (Z.ξ₀ ≫ Y.j) Y.j (RingHom.id Z.Ω) := by
    show Z.ξ₀ ≫ Y.j = Spec.map (CommRingCat.ofHom (RingHom.id Z.Ω)) ≫ Z.ξ₀ ≫ Y.j
    have e : CommRingCat.ofHom (RingHom.id Z.Ω) = 𝟙 _ := rfl
    rw [e, Spec.map_id, Category.id_comp]
  have hs : π.comp s = Z.inc := by
    ext a
    exact (PullReg.stalkMap_comp_genMap hD ⟨centre y, h0⟩ h (κ a)).trans (congrArg (fun f => f a) hκ)
  have ht : π.comp t = Z.inc := by
    ext a
    exact genMap_cst Z.ξ₀ (pullback.snd _ _) Z.inc Z.over_inc ⟨centre y, h0⟩ a
  have est : s = t := GlobalTheory.T.number_field_maps_local_ring_unique c.F _ Z.Ω π s t (hs.trans ht.symm)
  have e1 : (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp κ = (Scheme.stalkClosedPointTo y).hom.comp s := by
    rw [Scheme.stalkClosedPointTo_comp]
    rfl
  rw [e1, est]
  ext a
  exact val_cst y (pullback.snd _ _) c₀ hy a

end GlobalTheory.CompanionTheory.Ar.LocFn.Coef
