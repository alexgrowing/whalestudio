import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesToPullChartIffOfFlat
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.CompletionDVR

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolDiv

theorem dvd_of_traits {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R]
    {a b : R} (ha : a ≠ 0)
    (h : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ g : R →+* W, Function.Injective g →
      g a ∣ g b) : a ∣ b := by
  refine GlobalTheory.dvd_of_forall_height_eq_one ha fun p _ hp _ => ?_
  let V := Localization.AtPrime p
  have hV : IsDiscreteValuationRing V := GlobalTheory.isDiscreteValuationRing_of_height_eq_one p hp V
  have hi : Function.Injective (algebraMap R V) := IsLocalization.injective V p.primeCompl_le_nonZeroDivisors
  obtain ⟨⟨i1, i2⟩, i3, hinj, hloc, -⟩ := ReciprocityTheory.CA.Pt.completionDVR V
  let g := algebraMap V (AdicCompletion (maximalIdeal V) V)
  have hg : Function.Injective (g.comp (algebraMap R V)) := hinj.comp hi
  have hd : g (algebraMap R V a) ∣ g (algebraMap R V b) :=
    h _ ⟨i2, i3, charZero_of_injective_ringHom hg⟩ _ hg
  have hd' : algebraMap R V a ∣ algebraMap R V b := by
    rcases ValuationRing.dvd_total (algebraMap R V a) (algebraMap R V b) with h1 | ⟨e, he⟩
    · exact h1
    · obtain ⟨d, hd⟩ := hd
      have h0 : g (algebraMap R V a) ≠ 0 := fun e0 => ha (hg (e0.trans (map_zero _).symm))
      have h1 : g e * d = 1 := by
        apply mul_left_cancel₀ h0
        have := congrArg g he
        rw [map_mul, hd] at this
        rw [mul_one]
        linear_combination -this
      obtain ⟨u, rfl⟩ : IsUnit e := isUnit_of_map_unit g e (IsUnit.of_mul_eq_one _ h1)
      exact ⟨(u⁻¹ : Vˣ), by rw [he, Units.mul_inv_cancel_right]⟩
  obtain ⟨z, hz⟩ := hd'
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj p.primeCompl z
  refine ⟨s, s.2, r, hi ?_⟩
  rw [map_mul, map_mul, hz, ← hrs]
  ring

theorem span_eq_of_traits {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R]
    {a b : R} (ha : a ≠ 0)
    (h : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ g : R →+* W, Function.Injective g →
      (Ideal.span {a}).map g = (Ideal.span {b}).map g) : Ideal.span {a} = Ideal.span {b} := by
  have h' : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ g : R →+* W, Function.Injective g →
      Associated (g a) (g b) := fun W _ _ _ hW g hg => by
    have := h W hW g hg
    rwa [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
      Ideal.span_singleton_eq_span_singleton] at this
  have hb : b ≠ 0 := by
    rintro rfl
    let K := FractionRing R
    have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
    have hg : Function.Injective ((PowerSeries.C (R := K)).comp (algebraMap R K)) :=
      PowerSeries.C_injective.comp (IsFractionRing.injective R K)
    have := h' _ (GlobalTheory.FrameCmp.cDvr_powerSeries K) _ hg
    rw [map_zero, associated_zero_iff_eq_zero] at this
    exact ha (hg (this.trans (map_zero _).symm))
  exact Ideal.span_singleton_eq_span_singleton.2 (associated_of_dvd_dvd
    (dvd_of_traits ha fun W _ _ _ hW g hg => (h' W hW g hg).dvd)
    (dvd_of_traits hb fun W _ _ _ hW g hg => (h' W hW g hg).symm.dvd))

theorem idlAlong_fromSpecStalk {X : Scheme.{0}} (I : X.IdealSheafData) (x : X) {W : Type} [CommRing W] [IsLocalRing W]
    (g : X.presheaf.stalk x →+* W) :
    idlAlong I (Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecStalk x) = (FinalTheorems.stalkId I x).map g := by
  obtain ⟨⟨U, hU⟩, hx, -⟩ := EffCartierData.exists_affine_le (show x ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have e0 : ∀ (y : X) (hy : y ∈ U), X.fromSpecStalk y = Spec.map (X.presheaf.germ U y hy) ≫ hU'.fromSpec :=
    fun y hy => (hU'.fromSpecStalk_eq_fromSpecStalk hy).symm
  generalize hχ : Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecStalk x = χ
  have e1 : χ = Spec.map (X.presheaf.germ U x hx ≫ CommRingCat.ofHom g) ≫ hU'.fromSpec := by
    rw [← hχ, e0 x hx]
    exact (Spec.map_comp_assoc (X.presheaf.germ U x hx) (CommRingCat.ofHom g) hU'.fromSpec).symm
  have hc : χ (closedPoint W) ∈ U := by
    have : χ (closedPoint W) ∈ Set.range hU'.fromSpec :=
      ⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun f => f (closedPoint W)) e1.symm)⟩
    rwa [hU'.range_fromSpec] at this
  have e2 : χ = Spec.map (X.presheaf.germ U _ hc ≫ Scheme.stalkClosedPointTo χ) ≫ hU'.fromSpec := by
    rw [Spec.map_comp, Category.assoc, ← e0 _ hc]
    exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk χ).symm
  have e3 := Spec.map_injective ((cancel_mono hU'.fromSpec).1 (e1.symm.trans e2))
  unfold idlAlong
  rw [ds_stalkId_eq_map I ⟨U, hU⟩ _ hc, ds_stalkId_eq_map I ⟨U, hU⟩ x hx, Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← e3]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_lift (Z : Model Xo c β) (hβ : IsDedFrac β) (x : Z.X) {K : Type} [Field K]
    (g : Z.X.presheaf.stalk x →+* K) (hg : Function.Injective g) :
    ∃ y : Sp K ⟶ Xo.XF c, y ≫ Z.j = Spec.map (CommRingCat.ofHom g) ≫ Z.X.fromSpecStalk x := by
  obtain ⟨h₁, -, -, _, _, _, _⟩ := GlobalTheory.ModelRelCompare.densePart Z hβ
  have := (Z.normal x).1
  refine GlobalTheory.HomExt.exists_lift_of_range_subset Z.j _ ?_
  rintro _ ⟨t, rfl⟩
  obtain ⟨ξ, hξ, hs⟩ := GlobalTheory.exists_mem_genericPoints_specializes x
  have hξ' := GlobalTheory.genericPoints_subset_range_of_isDominant Z.j hξ
  obtain ⟨q, rfl⟩ : ξ ∈ Set.range (Z.X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact hs
  have ht : Spec.map (CommRingCat.ofHom g) t ⤳ q := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    change Ideal.comap g t.asIdeal ≤ q.asIdeal
    rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime, Ideal.comap_bot_of_injective _ hg]
    exact bot_le
  have h2 := ht.map (Z.X.fromSpecStalk x).continuous
  have h3 := (hξ : Maximal IsIrreducible _).2 isIrreducible_singleton.closure (specializes_iff_closure_subset.1 h2)
  rw [Scheme.Hom.comp_apply, (h2.antisymm (specializes_iff_closure_subset.2 h3)).eq]
  exact hξ'

theorem idealSheaf_eq_comap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H) (Xo : Moduli D l)
    (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F)
    (β' : O' →+* c'.F) (Z : Model Xo c β) (Z' : Model Xo' c' β') (BD : EffCartierData Z.X) (BD' : EffCartierData Z'.X)
    (φ : InvFun (𝓞 E)) (σ : 𝓞 E ≃+* 𝓞 E) (r : Xo'.XF c' ⟶ Xo.XF c)
    (_ν : TwMap σ Z'.oF.t Z.oF.t r), IsDedFrac β → IsDedFrac β' → Algebra.FiniteType ℤ O' → IsTwInv H φ → σ H.w0 = H.w0 →
    IsPhiDiv φ Z BD → IsPhiDiv φ Z' BD' → ∀ π : Z'.X ⟶ Z.X, Z'.j ≫ π = r ≫ Z.j →
    BD'.idealSheaf = BD.idealSheaf.comap π := by
  intro E _ _ _ H D l l' Xo Xo' c c' O O' _ _ β β' Z Z' BD BD' φ σ r ν hβ hβ' _ htw hσ hB hB' π hπ
  obtain ⟨h₁, -⟩ := GlobalTheory.ModelRelCompare.densePart Z' hβ'
  refine GlobalTheory.Vanishing.eq_comap_of_stalk fun x => ?_
  obtain ⟨hd, hn⟩ := Z'.normal x
  obtain ⟨i, hi⟩ := BD.exists_mem (π x)
  obtain ⟨i', hi'⟩ := BD'.exists_mem x
  have hz : CharZero (Z'.X.presheaf.stalk x) := by
    obtain ⟨y, -⟩ := exists_lift Z' hβ' x _ (IsFractionRing.injective _ (FractionRing (Z'.X.presheaf.stalk x)))
    have := charZero_of_point (K := .of (FractionRing (Z'.X.presheaf.stalk x))) y
    exact ⟨fun p q e => Nat.cast_injective (R := FractionRing (Z'.X.presheaf.stalk x)) (by
      simpa using congrArg (algebraMap _ (FractionRing (Z'.X.presheaf.stalk x))) e)⟩
  have key : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W →
      ∀ g : Z'.X.presheaf.stalk x →+* W, Function.Injective g → (FinalTheorems.stalkId BD'.idealSheaf x).map g =
        ((FinalTheorems.stalkId BD.idealSheaf (π x)).map (π.stalkMap x).hom).map g := by
    intro W _ _ _ hW g hg
    obtain ⟨y, hy⟩ := exists_lift Z' hβ' x ((algebraMap W (FractionRing W)).comp g)
      ((IsFractionRing.injective W _).comp hg)
    have e1 : jK W ≫ Spec.map (CommRingCat.ofHom g) ≫ Z'.X.fromSpecStalk x = y ≫ Z'.j := by
      rw [hy, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have e2 : Spec.map (CommRingCat.ofHom (g.comp (π.stalkMap x).hom)) ≫ Z.X.fromSpecStalk (π x) =
        (Spec.map (CommRingCat.ofHom g) ≫ Z'.X.fromSpecStalk x) ≫ π := by
      rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      rfl
    rw [Ideal.map_map, ← idlAlong_fromSpecStalk, ← idlAlong_fromSpecStalk]
    refine GlobalTheory.T.polarization_transfer_models E H D l l' Xo Xo' c c' O O' β β' Z Z' BD BD' φ σ r ν hβ hβ' htw hσ hB hB' W hW _ _ y e1 ?_
    rw [e2, ← Category.assoc, e1, Category.assoc, hπ]
  rw [BD.stalkId_idealSheaf i _ hi, BD'.stalkId_idealSheaf i' _ hi', Ideal.map_span, Set.image_singleton] at key ⊢
  exact span_eq_of_traits (nonZeroDivisors.ne_zero (Cartier.isRegularFn_iff_germ.1 (BD'.regular i') x hi')) key

end GlobalTheory.PolDiv
