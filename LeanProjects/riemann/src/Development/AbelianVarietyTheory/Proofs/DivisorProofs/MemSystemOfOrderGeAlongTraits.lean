import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
open GlobalTheory

noncomputable section

namespace GlobalTheory.USepStrait

theorem range_jK_spMap_subset_of_injective (V R : Type) [CommRing V] [IsDomain V] [CommRing R] [IsDomain R] (ρ : V →+* R)
    (hρ : Function.Injective ρ) (X : Scheme.{0}) (χ : Sp V ⟶ X) : Set.range (jK R ≫ spMap ρ ≫ χ) ⊆ Set.range (jK V ≫ χ) := by
  intro x ⟨p, hp⟩
  let q : Sp (FractionRing V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  have key : (spMap ρ) ((jK R) p) = (jK V) q := by
    apply PrimeSpectrum.ext
    change Ideal.comap ρ (Ideal.comap (algebraMap R (FractionRing R)) p.asIdeal) =
      Ideal.comap (algebraMap V (FractionRing V)) ⊥
    haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
    rw [Ideal.eq_bot_of_prime p.asIdeal, Ideal.comap_comap,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V)),
      Ideal.comap_bot_of_injective _ (by rw [RingHom.coe_comp]; exact (IsFractionRing.injective R (FractionRing R)).comp hρ)]
  refine ⟨q, ?_⟩
  rw [← hp]
  change χ ((jK V) q) = χ ((spMap ρ) ((jK R) p))
  rw [key]

theorem mem_of_ordGe_on : UTraitExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (φ : InvFun (𝓞 E)) (d : ℕ) (J : C.Z.IdealSheafData), UValOn Xo c C.i φ J d → ∀ (M : Scheme.{0}) (z₁ : M) (U : M.Opens) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (N₁ : ℕ) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] N₁ (M.presheaf.stalk z₁)), GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ev' : M.presheaf.stalk z₁ →+* V), IsLocalHom ev' → Set.range (jK V ≫ spMap ev' ≫ M.fromSpecStalk z₁) ⊆ (U : Set M) → ∀ y' : Sp (FractionRing V) ⟶ Xo.XF c, y' ≫ C.iF = spMap ((algebraMap V (FractionRing V)).comp ev') ≫ ζ → ∀ (D e : ℕ) (f : M.presheaf.stalk z₁), Φ.OrdGe φ (D * (2 * d)) e f → ev' f ∈ idlAlong J (spMap ev' ≫ ζ ≫ pullback.fst C.z (spMap C.b)) ^ D ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map ev') ^ e := by
  intro hExt E _ _ _ H Dw l Xo c C φ d J hval M z₁ U ζ N₁ Φ hT V _ _ _ _ hV ev' hev' hU y' hy' D e f hf
  have hB : GlobalTheory.Mum.Base V := ⟨⟨inferInstance, inferInstance, inferInstance, hV⟩, inferInstance⟩
  obtain ⟨T, fx, fK, hfi, hfl, -, hfK, hTy⟩ := hExt E H Dw l Xo c V hB inferInstance y'
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  let evT := fx.comp ev'
  haveI : IsLocalHom evT := RingHom.isLocalHom_comp fx ev'
  have hring : (algebraMap T.V (FractionRing T.V)).comp evT = fK.comp ((algebraMap V (FractionRing V)).comp ev') :=
    RingHom.ext fun a => (hfK (ev' a)).symm
  have hsq : jK T.V ≫ spMap evT ≫ ζ = T.y ≫ C.iF := by
    rw [hTy, Category.assoc, hy', ← Category.assoc, GlobalTheory.USepTrait.sp_comp, ← Category.assoc, GlobalTheory.USepTrait.sp_comp, hring]
  have hrange : Set.range (jK T.V ≫ spMap evT ≫ M.fromSpecStalk z₁) ⊆ (U : Set M) := by
    have e1 : jK T.V ≫ spMap evT ≫ M.fromSpecStalk z₁ = jK T.V ≫ spMap fx ≫ spMap ev' ≫ M.fromSpecStalk z₁ := by
      rw [← GlobalTheory.USepTrait.sp_comp ev' fx, Category.assoc]
    rw [e1]
    exact (range_jK_spMap_subset_of_injective V T.V fx hfi M (spMap ev' ≫ M.fromSpecStalk z₁)).trans
      (by simpa only [Category.assoc] using hU)
  have hT' := hT T evT inferInstance hsq hrange
  change ∃ (y : Φ.Y) (f : T.V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] T.P.D.toPre.X), Φ.m y = 1 ∧ IsPrincipalIdealRing (Φ.V y) ∧
      Function.Injective f ∧ IsLocalHom f ∧ f.comp evT = Φ.ev y ∧
      ∀ k, Φ.t y k ^ 2 = f T.ϖ ∧ ∀ a b, Φ.δ y k a b = T.be (e a) (e b) at hT'
  obtain ⟨y2, f₂, eq, hm, hP, hf₂i, hf₂l, hf₂c, ht⟩ := hT'
  obtain ⟨tK, m1, m2⟩ := T.gen
  have hyχ : T.y ≫ C.i = jK T.V ≫ (spMap evT ≫ ζ ≫ pullback.fst C.z (spMap C.b)) := by
    show T.y ≫ C.iF ≫ pullback.fst _ _ = _
    rw [← Category.assoc, ← hsq]
    simp only [Category.assoc]
  obtain ⟨n, hn, hid⟩ := hval T.V T.cdvr T.ϖ T.irr _ T.y hyχ T.t tK m1 m2 T.P T.be T.lev T.mono
  have hid' : (idlAlong J (spMap ev' ≫ ζ ≫ pullback.fst C.z (spMap C.b))).map fx = Ideal.span {T.ϖ ^ n} := by
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, ← hid, ← Category.assoc, GlobalTheory.USepTrait.sp_comp]
  have hm0 : 0 < Φ.m y2 := by omega
  let k : Fin (Φ.m y2) := ⟨0, hm0⟩
  have hδ : Φ.δ y2 k = pull eq.toLinearMap T.be := LinearMap.ext₂ fun a b => (ht k).2 a b
  have hev : φ.evalZ (Φ.δ y2 k) = φ.evalZ T.be := by
    rw [hδ]; exact evalZ_pull φ eq.surjective T.be
  have hb : ((D * (2 * n) : ℕ) : ℝ) = ((D * (2 * d) : ℕ) : ℝ) * φ.evalZ (Φ.δ y2 k) := by
    rw [hev]; push_cast; rw [hn]; ring
  have hmem := hf.mem y2 hP hm k (D * (2 * n)) hb
  have htp : Φ.t y2 k ^ (D * (2 * n)) = f₂ (T.ϖ ^ (n * D)) := by
    rw [show D * (2 * n) = 2 * (n * D) by ring, pow_mul, (ht k).1, map_pow]
  haveI := hf₂l
  have hK : (Ideal.span {T.ϖ ^ (n * D)} ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map evT) ^ e).map f₂ =
      Ideal.span {Φ.t y2 k ^ (D * (2 * n))} ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map (Φ.ev y2)) ^ e := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_pow, Ideal.map_map, hf₂c, htp]
  have h1 : evT f ∈ Ideal.span {T.ϖ ^ (n * D)} ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map evT) ^ e := by
    rw [← GlobalTheory.USepTrait.comap_map_eq f₂ hf₂i (Ideal.span {T.ϖ ^ (n * D)} ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map evT) ^ e)]
    rw [Ideal.mem_comap]
    rw [hK, ← RingHom.comp_apply, hf₂c]
    exact hmem
  haveI := hfl
  have hK' : ((idlAlong J (spMap ev' ≫ ζ ≫ pullback.fst C.z (spMap C.b))) ^ D ⊔
      ((maximalIdeal (M.presheaf.stalk z₁)).map ev') ^ e).map fx =
      Ideal.span {T.ϖ ^ (n * D)} ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map evT) ^ e := by
    rw [Ideal.map_sup, Ideal.map_pow, hid', Ideal.span_singleton_pow, ← pow_mul, Ideal.map_pow, Ideal.map_map]
  rw [← GlobalTheory.USepTrait.comap_map_eq fx hfi (_ ^ D ⊔ _), hK']
  exact h1

end GlobalTheory.USepStrait
