import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumLengthMulLogCardEqNegLogAdicAbvNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArithmeticVarietyDimZeroFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.PlaceFormula

theorem coheight_eq_one {Z : Scheme.{0}} [IsIntegral Z] (hd : topologicalKrullDim Z = 1) {z : Z}
    (hz : z ≠ genericPoint Z) : Order.coheight z = 1 := by
  have hg (w : Z) : w ≤ genericPoint Z := genericPoint_specializes w
  refine le_antisymm ((Order.coheight_le_coe_iff (n := 1)).2 fun y hy => ?_) (Order.one_le_iff_ne_zero.2 fun h => ?_)
  · have h1 : y = genericPoint Z := by
      by_contra h
      have h2 : y ⤳ z := hy.le
      have h3 := (SmallSecHeight.isClosed_of_ne hd h).closure_eq ▸ specializes_iff_mem_closure.1 h2
      exact hy.ne h3
    have h2 : Order.coheight y = 0 := Order.coheight_eq_zero.2 fun w _ => h1 ▸ hg w
    simp [h2]
  · have h1 : z ⤳ genericPoint Z := Order.coheight_eq_zero.1 h (hg z)
    exact hz (h1.antisymm (genericPoint_specializes z)).eq

theorem spec_appTop {K : CommRingCat.{0}} {Z : Scheme.{0}} [IsAffine Z] (y : Spec K ⟶ Z) :
    Spec.map (y.appTop ≫ (Scheme.ΓSpecIso K).hom) ≫ (isAffineOpen_top Z).fromSpec = y := by
  rw [IsAffineOpen.fromSpec_top, Spec.map_comp, ← Scheme.isoSpec_Spec_hom, Scheme.isoSpec_hom_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem fromSpec_comp {k : CommRingCat.{0}} {Z : Scheme.{0}} [IsAffine Z] (q : Z ⟶ Spec k) :
    (isAffineOpen_top Z).fromSpec ≫ q = Spec.map ((Scheme.ΓSpecIso k).inv ≫ q.appTop) := by
  rw [IsAffineOpen.fromSpec_top, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_inv_naturality]

theorem valAt_spec {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] [IsAffine Z] (ψ : Γ(Z, ⊤) ⟶ CommRingCat.of K)
    (a : Γ(Z, ⊤)) :
    valAt (K := K) (Spec.map ψ ≫ (isAffineOpen_top Z).fromSpec) (fnOf ⊤ trivial a) = ψ.hom a := by
  have h := Spec.map_injective ((cancel_mono _).1 (spec_appTop (Spec.map ψ ≫ (isAffineOpen_top Z).fromSpec)))
  rw [OfModel.valAt_fnOf (U := ⊤) _ trivial le_rfl]
  conv_rhs => rw [← h]
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem injective_of_charZero {F R : Type} [Field F] [NumberField F] [CommRing R] [CharZero R] (φ : 𝓞 F →+* R) :
    Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => ?_)
  simpa [RingHom.mem_ker] using hn

set_option maxHeartbeats 400000 in

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (q : Z ⟶ Sp (𝓞 F)), IsArithVar q 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (t : Z.functionFieldˣ),
    ∑ᶠ (z : Z) (_ : (q z).asIdeal = v.asIdeal),
      (Scheme.ord (t : Z.functionField) z : ℝ) * Real.log (Nat.card (Z.residueField z)) =
    -∑ᶠ y : {y : Sp (AlgebraicClosure F) ⟶ Z // y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))},
      Real.log (e.w (valAt y.1 (t : Z.functionField))) := by
  intro F _ _ Z _ _ q hZ v e t
  have := GlobalTheory.ArithCurveFinite.isFinite _ Z q hZ
  have : IsAffine Z := isAffine_of_isAffineHom q
  have hU := isAffineOpen_top Z
  have := hZ.charZero
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  let φ : CommRingCat.of (𝓞 F) ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso _).inv ≫ q.appTop
  have hq : hU.fromSpec ≫ q = Spec.map φ := fromSpec_comp q
  let : Algebra (𝓞 F) Γ(Z, ⊤) := φ.hom.toAlgebra
  have hbij : Function.Bijective hU.fromSpec := by
    refine ⟨hU.fromSpec.isOpenEmbedding.injective, fun z => ?_⟩
    have : z ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; trivial
    exact this
  have : Module.Finite (𝓞 F) Γ(Z, ⊤) := (IsFinite.SpecMap_iff φ).1 (by
    rw [← hq, IsAffineOpen.fromSpec_top]; infer_instance)
  have := functionField_isFractionRing_of_isAffineOpen Z ⊤ hU
  have hφ : Function.Injective (algebraMap (𝓞 F) Γ(Z, ⊤)) := injective_of_charZero _
  have := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have hi : Function.Injective ((algebraMap Γ(Z, ⊤) Z.functionField).comp (algebraMap (𝓞 F) Γ(Z, ⊤))) :=
    (IsFractionRing.injective _ _).comp hφ
  let : Algebra F Z.functionField := (IsFractionRing.lift hi).toAlgebra
  have : IsScalarTower (𝓞 F) Γ(Z, ⊤) Z.functionField :=
    .of_algebraMap_eq fun a => IsFractionRing.lift_algebraMap (K := F) hi a
  have : Module.Finite F Z.functionField := Module.Finite.of_isLocalization (𝓞 F) Γ(Z, ⊤) (nonZeroDivisors _)

  let P (τ : Z.functionField →ₐ[F] AlgebraicClosure F) :
      {y : Sp (AlgebraicClosure F) ⟶ Z // y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))} :=
    ⟨Spec.map (CommRingCat.ofHom (τ.toRingHom.comp (algebraMap Γ(Z, ⊤) Z.functionField))) ≫ hU.fromSpec, by
      rw [Category.assoc, hq, ← Spec.map_comp]
      congr 1
      ext a
      change τ (algebraMap Γ(Z, ⊤) _ (algebraMap (𝓞 F) _ a)) = _
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F, τ.commutes]
      rfl⟩
  have hP : Function.Bijective P := by
    refine ⟨fun τ τ' h => ?_, fun y => ?_⟩
    · have h1 := congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 (congrArg Subtype.val h)))
      exact AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (nonZeroDivisors Γ(Z, ⊤)) h1)
    · obtain ⟨ψ, hψ⟩ : ∃ ψ : Γ(Z, ⊤) ⟶ CommRingCat.of (AlgebraicClosure F), Spec.map ψ ≫ hU.fromSpec = y.1 :=
        ⟨_, spec_appTop y.1⟩
      have h1 := y.2
      rw [← hψ, Category.assoc, hq, ← Spec.map_comp] at h1
      have h2 (a : 𝓞 F) : ψ.hom (algebraMap _ _ a) = algebraMap _ _ a :=
        congrArg (fun f => f.hom a) (Spec.map_injective h1)
      have h3 : Function.Injective ψ.hom := by
        rw [RingHom.injective_iff_ker_eq_bot]
        refine Ideal.eq_bot_of_comap_eq_bot (R := 𝓞 F) (eq_bot_iff.2 fun a ha => ?_)
        rw [Ideal.mem_comap, RingHom.mem_ker, h2] at ha
        exact injective_of_charZero (algebraMap (𝓞 F) (AlgebraicClosure F)) (ha.trans (map_zero _).symm)
      have h4 : (IsFractionRing.lift (K := Z.functionField) h3).comp (algebraMap F _) = algebraMap F _ :=
        IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) (RingHom.ext fun a => by
          simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
          rw [IsScalarTower.algebraMap_apply (𝓞 F) Γ(Z, ⊤), IsFractionRing.lift_algebraMap, h2])
      refine ⟨⟨IsFractionRing.lift h3, fun a => congrArg (fun f => f a) h4⟩, Subtype.ext ?_⟩
      rw [← hψ]
      exact congrArg (fun f => Spec.map f ≫ hU.fromSpec)
        (CommRingCat.hom_ext (RingHom.ext fun a =>
          IsFractionRing.lift_algebraMap (K := Z.functionField) h3 a))
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(Z, ⊤)) (t : Z.functionField)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap _ Z.functionField b ≠ 0 := by simpa using hb0
  have hab' : algebraMap _ Z.functionField a = t * algebraMap _ _ b := by rw [← hab, div_mul_cancel₀ _ hb1]
  have ha1 : algebraMap _ Z.functionField a ≠ 0 := hab' ▸ mul_ne_zero t.ne_zero hb1
  have ha0 : a ≠ 0 := by simpa using ha1
  have hval (τ) : valAt (P τ).1 (t : Z.functionField) = τ t := by
    have hg : below (P τ).1 = genericPoint Z :=
      SmallSecHeight.eq_genericPoint hZ (Scheme.SpecToEquivOfField _ Z (P τ).1).2.hom.charZero
    have h1 (c : Γ(Z, ⊤)) : valAt (P τ).1 (algebraMap _ Z.functionField c) = τ (algebraMap _ _ c) := valAt_spec _ c
    have h2 := h1 a
    rw [hab', OfModel.valAt_mul _ (hg ▸ regAt_genericPoint _) (hg ▸ regAt_genericPoint _), h1, map_mul] at h2
    exact mul_right_cancel₀ ((map_ne_zero τ).2 hb1) h2
  have hR : ∑ᶠ y : {y : Sp (AlgebraicClosure F) ⟶ Z // y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))},
      Real.log (e.w (valAt y.1 (t : Z.functionField))) =
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v (Algebra.norm F (t : Z.functionField))) := by
    rw [← finsum_eq_of_bijective P hP (f := fun τ => Real.log (e.w (τ t))) fun τ => by rw [hval],
      finsum_eq_sum_of_fintype, ← e.w_alg, Algebra.norm_eq_prod_embeddings, map_prod, Real.log_prod]
    exact fun τ _ => e.w.ne_zero ((map_ne_zero τ).2 t.ne_zero)

  have hL (c : Γ(Z, ⊤)) (hc : c ≠ 0) : ∑ᶠ (z : Z) (_ : (q z).asIdeal = v.asIdeal),
      (Scheme.ord (algebraMap _ Z.functionField c) z : ℝ) * Real.log (Nat.card (Z.residueField z)) =
      -Real.log (NumberField.HeightOneSpectrum.adicAbv F v (Algebra.norm F (algebraMap _ Z.functionField c))) := by
    let (m : PrimeSpectrum Γ(Z, ⊤)) : Algebra Γ(Z, ⊤) (Z.presheaf.stalk (hU.fromSpec m)) :=
      TopCat.Presheaf.algebra_section_stalk Z.presheaf (⟨hU.fromSpec m, trivial⟩ : (⊤ : Z.Opens))
    have (m : PrimeSpectrum Γ(Z, ⊤)) : IsLocalization.AtPrime (Z.presheaf.stalk (hU.fromSpec m)) m.asIdeal :=
      hU.isLocalization_stalk' m trivial
    have (m : PrimeSpectrum Γ(Z, ⊤)) : IsLocalRing (Z.presheaf.stalk (hU.fromSpec m)) :=
      Z.toLocallyRingedSpace.isLocalRing _
    rw [← GlobalTheory.finsum_length_mul_log_card_eq_neg_log_adicAbv_norm F Γ(Z, ⊤) Z.functionField (fun m => Z.presheaf.stalk (hU.fromSpec m)) v c hc]
    refine (finsum_eq_of_bijective _ hbij fun m => ?_).symm
    have hqm (m) : (q (hU.fromSpec m)).asIdeal = m.asIdeal.comap (algebraMap (𝓞 F) Γ(Z, ⊤)) := by
      rw [← Scheme.Hom.comp_apply, hq]; rfl
    refine finsum_congr_Prop (by rw [hqm]) fun h => ?_
    have hne : hU.fromSpec m ≠ genericPoint Z := fun h' => v.ne_bot (by
      have h1 := genericPoint_eq_of_isOpenImmersion hU.fromSpec
      rw [genericPoint_eq_bot_of_affine] at h1
      rw [← h, h', ← h1]
      exact (hqm _).trans (Ideal.comap_bot_of_injective _ hφ))
    have h1 := ord_algebraMap (coheight_eq_one hZ.dim_eq hne)
      ((map_ne_zero_iff _ (germ_injective_of_isIntegral Z (U := ⊤) _ trivial)).2 hc)
    rw [algebraMap_germ (U := ⊤) trivial c] at h1
    exact congrArg (· * _) ((Int.cast_natCast _).symm.trans (congrArg _ h1.symm))
  have hfin : {z : Z | (q z).asIdeal = v.asIdeal}.Finite :=
    (q.finite_preimage_singleton ⟨v.asIdeal, v.isPrime⟩).subset fun z hz => PrimeSpectrum.ext hz
  have h1 := hL a ha0
  have h2 := hL b hb0
  have hn (x : Z.functionField) (hx : x ≠ 0) :
      NumberField.HeightOneSpectrum.adicAbv F v (Algebra.norm F x) ≠ 0 :=
    AbsoluteValue.ne_zero _ (Algebra.norm_ne_zero_iff.2 hx)
  rw [hab', map_mul, map_mul, Real.log_mul (hn _ t.ne_zero) (hn _ hb1)] at h1
  simp only [Scheme.ord_mul t.ne_zero hb1, Int.cast_add, add_mul] at h1
  have h3 := finsum_mem_add_distrib
    (f := fun z => (Scheme.ord (t : Z.functionField) z : ℝ) * Real.log (Nat.card (Z.residueField z)))
    (g := fun z => (Scheme.ord (algebraMap _ Z.functionField b) z : ℝ) * Real.log (Nat.card (Z.residueField z))) hfin
  simp only [Set.mem_ofPred_eq] at h3
  rw [hR]
  linear_combination h1 - h2 - h3

end GlobalTheory.TrueGeo.PlaceFormula
