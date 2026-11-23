import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRatSecOfPull
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsChowFormIntLineZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ImageInject

open GlobalTheory.CompHS GlobalTheory.FlagTan GlobalTheory.TrueGeo GlobalTheory.TrueGeo.SmallSec TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

private theorem exists_place {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (ι : K →ₐ[F] AlgebraicClosure F) :
    ∃ v' : FinitePlace K, ∀ a b : K, e.w (ι a) ≤ e.w (ι b) ↔ v' a ≤ v' b := by
  have hint : ∀ x : 𝓞 K, ι (x : K) ∈ e.O := fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int e.O (x.isIntegral_coe.map (ι : K →+* AlgebraicClosure F).toIntAlgHom)
  let ρ : 𝓞 K →+* e.O := ((ι : K →+* AlgebraicClosure F).comp (algebraMap (𝓞 K) K)).codRestrict e.O hint
  have hP : ∀ x : 𝓞 K, x ∈ (IsLocalRing.maximalIdeal e.O).comap ρ ↔ e.w (ι (x : K)) < 1 := fun x => by
    rw [Ideal.mem_comap, e.O.valuation_lt_one_iff, valuation_lt_one_iff]
    rfl
  obtain ⟨a₀, ha₀, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let P : HeightOneSpectrum (𝓞 K) := ⟨(IsLocalRing.maximalIdeal e.O).comap ρ, inferInstance, fun h => by
    have h1 : algebraMap (𝓞 F) (𝓞 K) a₀ ∈ (IsLocalRing.maximalIdeal e.O).comap ρ := by
      rw [hP, show ((algebraMap (𝓞 F) (𝓞 K) a₀ : 𝓞 K) : K) = algebraMap F K (a₀ : F) from rfl, ι.commutes, e.w_alg]
      exact (v.adicAbv_coe_lt_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a₀).2 ha₀
    rw [h, Ideal.mem_bot] at h1
    exact ha0 ((map_eq_zero_iff _ (RingOfIntegers.algebraMap.injective F K)).1 h1)⟩
  have hle : ∀ x : 𝓞 K, e.w (ι (x : K)) ≤ 1 := fun x => (e.mem_O _).1 (hint x)
  have hv : ∀ x : 𝓞 K, FinitePlace.mk P (x : K) < 1 ↔ e.w (ι (x : K)) < 1 := fun x => by
    rw [← hP, FinitePlace.mk_apply]
    exact FinitePlace.norm_lt_one_iff_mem K P x
  have hv1 : ∀ x : 𝓞 K, FinitePlace.mk P (x : K) ≤ 1 := fun x => by
    rw [FinitePlace.mk_apply]
    exact FinitePlace.norm_le_one K P x
  have key : ∀ a : K, FinitePlace.mk P a ≤ 1 → e.w (ι a) ≤ 1 ∧ (FinitePlace.mk P a < 1 → e.w (ι a) < 1) := by
    intro a ha
    have h1 : P.valuation K a ≤ 1 := by
      rw [FinitePlace.mk_apply, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def] at ha
      exact (WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P)).1
        (by exact_mod_cast ha)
    obtain ⟨n, d, hd⟩ := P.exists_primeCompl_mul_eq_of_integer a h1
    have hd1 : e.w (ι ((d : 𝓞 K) : K)) = 1 := (hle _).antisymm (not_lt.1 fun h => d.2 ((hP _).2 h))
    have hd2 : FinitePlace.mk P ((d : 𝓞 K) : K) = 1 := (hv1 _).antisymm (not_lt.1 fun h => d.2 ((hP _).2 ((hv _).1 h)))
    have e1 : e.w (ι a) = e.w (ι (n : K)) := by
      rw [show (n : K) = a * ((d : 𝓞 K) : K) from hd.symm, map_mul, map_mul, hd1, mul_one]
    have e2 : FinitePlace.mk P a = FinitePlace.mk P (n : K) := by
      rw [show (n : K) = a * ((d : 𝓞 K) : K) from hd.symm, map_mul, hd2, mul_one]
    rw [e1, e2]
    exact ⟨hle n, (hv n).1⟩
  refine ⟨FinitePlace.mk P, fun a b => ?_⟩
  by_cases hb : b = 0
  · subst hb
    simp only [map_zero]
    rw [(e.w.nonneg _).ge_iff_eq', (apply_nonneg _ _).ge_iff_eq']
    simp
  have hb1 : 0 < e.w (ι b) := e.w.pos ((map_ne_zero ι).2 hb)
  have hb2 : 0 < FinitePlace.mk P b := FinitePlace.pos_iff.2 hb
  refine ⟨fun h => not_lt.1 fun h' => ?_, fun h => ?_⟩
  · have ha2 : 0 < FinitePlace.mk P a := hb2.trans h'
    have h3 : FinitePlace.mk P (b / a) < 1 := by rw [map_div₀]; exact (div_lt_one ha2).2 h'
    have h4 := (key _ h3.le).2 h3
    have ha1 : 0 < e.w (ι a) := e.w.pos ((map_ne_zero ι).2 (FinitePlace.pos_iff.1 ha2))
    rw [map_div₀, map_div₀, div_lt_one ha1] at h4
    exact h4.not_ge h
  · have h4 := (key (a / b) (by rw [map_div₀]; exact (div_le_one hb2).2 h)).1
    rwa [map_div₀, map_div₀, div_le_one hb1] at h4

section Dense

variable {F : Type} [Field F] [NumberField F]

private theorem isIntegral_of_dense (R K : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 F) R]
    [Algebra.FiniteType (𝓞 F) R] [Field K] [Algebra R K] [IsFractionRing R K]
    (hinj : Function.Injective (algebraMap (𝓞 F) R)) (h : K) {t₀ : R} (ht₀ : t₀ ≠ 0)
    (hgen : ∀ P : Ideal R, P.IsPrime → P.comap (algebraMap (𝓞 F) R) = ⊥ →
      ∃ a ∉ P, ∃ b, algebraMap R K a * h = algebraMap R K b)
    (hpt : ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (φ : R →+* AlgebraicClosure F),
      (∀ a : 𝓞 F, φ (algebraMap _ _ a) = algebraMap F _ (a : F)) → (∀ s, e.w (φ s) ≤ 1) → φ t₀ ≠ 0 →
      ∀ a b, algebraMap R K a * h = algebraMap R K b → φ a ≠ 0 → e.w (φ b) ≤ e.w (φ a)) :
    IsIntegral R h := by
  by_contra hint
  obtain ⟨S, _, _, _, _, t, hRS, ht, hne, hab⟩ := exists_overring R K h hint
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have htm : t ∈ m := hle (Ideal.subset_span rfl)
  let : Algebra (𝓞 F) S := ((algebraMap R S).comp (algebraMap (𝓞 F) R)).toAlgebra
  have : IsScalarTower (𝓞 F) R S := .of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType (𝓞 F) S := .trans (S := R) inferInstance inferInstance
  obtain ⟨v, e, φ, h₁, h₂, h₃, h₄⟩ := exists_point (F := F) S (hRS.comp hinj) m (fun hb => by
    obtain ⟨a, ha, b, e⟩ := hgen (m.comap (algebraMap R S)) inferInstance
      ((Ideal.comap_comap _ _).trans hb)
    exact ha (by rw [Ideal.mem_comap, hab a b e]; exact m.mul_mem_left _ htm))
    ((map_ne_zero_iff _ hRS).2 ht₀)
  obtain ⟨a, ha, b, hb⟩ := hgen (RingHom.ker (φ.comp (algebraMap R S))) (RingHom.ker_isPrime _)
    (eq_bot_iff.2 fun x hx => by
      have : algebraMap F (AlgebraicClosure F) (x : F) = 0 := (h₁ x).symm.trans hx
      simpa using this)
  have h₅ := hpt v e (φ.comp (algebraMap R S)) h₁ (fun s => h₂ _) h₄ a b hb ha
  have h₆ : e.w (φ (algebraMap R S a)) = e.w (φ (algebraMap R S b)) * e.w (φ t) := by
    rw [hab a b hb, map_mul, map_mul]
  have h₇ : 0 < e.w (φ (algebraMap R S a)) := e.w.pos ha
  have h₈ := h₃ t htm
  have h₉ := e.w.nonneg (φ t)
  change e.w (φ (algebraMap R S b)) ≤ e.w (φ (algebraMap R S a)) at h₅
  nlinarith

private theorem regAt_of_dense {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp (𝓞 F)) [LocallyOfFiniteType p]
    (hN : Geo.Tor.IsNormalScheme X) (hp : (p (genericPoint X)).asIdeal = ⊥) (U O : X.Opens)
    (hO : genericPoint X ∈ O) (h : X.functionField) (hgen : ∀ x ∈ U, (p x).asIdeal = ⊥ → RegAt x h)
    (hpt : ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (yt : Sp e.O ⟶ X),
      (spMap e.O.subtype ≫ yt) ≫ p =
        spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) →
      ⊤ ≤ yt ⁻¹ᵁ U → below (spMap e.O.subtype ≫ yt) ∈ O → e.w (TrueGeo.valAt (spMap e.O.subtype ≫ yt) h) ≤ 1) :
    ∀ x ∈ U, RegAt x h := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx
  replace hW : IsAffineOpen W := hW
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  obtain ⟨t₀, ht₀O, ht₀⟩ := hW.exists_basicOpen_le (V := O) ⟨_, hO⟩ (gen_mem hxW)
  have ht0 : t₀ ≠ 0 := fun e => by
    rw [e, Scheme.basicOpen_zero] at ht₀
    exact ht₀
  let ρ := Spec.preimage (hW.fromSpec ≫ p)
  have hρ : Spec.map ρ = hW.fromSpec ≫ p := Spec.map_preimage _
  let : Algebra (𝓞 F) Γ(X, W) := ρ.hom.toAlgebra
  have hft : Algebra.FiniteType (𝓞 F) Γ(X, W) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ρ)).mp (hρ ▸ inferInstance)
  have := functionField_isFractionRing_of_isAffineOpen X W hW
  have hP (P : PrimeSpectrum Γ(X, W)) :
      (p (hW.fromSpec P)).asIdeal = P.asIdeal.comap (algebraMap (𝓞 F) Γ(X, W)) := by
    exact congrArg (fun q : Spec Γ(X, W) ⟶ Sp (𝓞 F) => (q P).asIdeal) hρ.symm
  have hPW (P : PrimeSpectrum Γ(X, W)) : hW.fromSpec P ∈ W := hW.range_fromSpec.le ⟨P, rfl⟩
  have hfn (a : Γ(X, W)) : algebraMap _ X.functionField a = fnOf W (gen_mem hxW) a := rfl
  have hinj : Function.Injective (algebraMap (𝓞 F) Γ(X, W)) := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot, eq_bot_iff, ← hp]
    obtain ⟨P, hP'⟩ := hW.range_fromSpec.ge (gen_mem hxW)
    rw [← hP']
    exact (Ideal.comap_mono bot_le).trans (hP P).ge
  have hint : IsIntegral Γ(X, W) h := by
    refine isIntegral_of_dense (F := F) _ _ hinj h ht0 (fun P hPp hP0 => ?_)
      fun v e φ h₁ h₂ hφ a b hab ha => ?_
    · obtain ⟨c, rfl⟩ := hgen _ (hWU (hPW ⟨P, hPp⟩)) ((hP ⟨P, hPp⟩).trans hP0)
      let := X.presheaf.algebra_section_stalk (⟨_, hPW ⟨P, hPp⟩⟩ : W)
      have := hW.isLocalization_stalk' ⟨P, hPp⟩ (hPW ⟨P, hPp⟩)
      obtain ⟨⟨b, a⟩, e⟩ := @IsLocalization.surj _ _ P.primeCompl _ _ _ this c
      refine ⟨a, a.2, b, ?_⟩
      rw [hfn, hfn, ← algebraMap_germ (hPW ⟨P, hPp⟩), ← algebraMap_germ (hPW ⟨P, hPp⟩), ← map_mul,
        mul_comm]
      exact congrArg _ e
    · let φ' : Γ(X, W) →+* e.O := φ.codRestrict e.O fun s => (e.mem_O _).2 (h₂ s)
      have e₁ : spMap e.O.subtype ≫ Spec.map (CommRingCat.ofHom φ') ≫ hW.fromSpec =
          Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec := by
        rw [← Category.assoc, ← Spec.map_comp]
        rfl
      have e₂ : (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec) ≫ p =
          spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
        rw [Category.assoc, ← hρ, ← Spec.map_comp, ← Spec.map_comp]
        congr 1
        ext a
        exact h₁ a
      have h₀ : below (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec) ∈ O := by
        refine ht₀O ?_
        change Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint _) ∈ hW.fromSpec ⁻¹ᵁ X.basicOpen t₀
        rw [hW.fromSpec_preimage_basicOpen]
        change φ t₀ ∉ IsLocalRing.maximalIdeal _
        rw [IsLocalRing.maximalIdeal_eq_bot]
        exact hφ
      have h₃ := hpt v e (Spec.map (CommRingCat.ofHom φ') ≫ hW.fromSpec) (e₁ ▸ e₂)
        ((Points.le_preimage_specMap_fromSpec hW _).trans (Scheme.Hom.preimage_mono _ hWU)) (e₁ ▸ h₀)
      rw [e₁] at h₃
      have h₄ := Points.le_preimage_specMap_fromSpec hW (CommRingCat.ofHom φ)
      have h₅ := (Points.le_preimage_iff _ _).1 h₄
      have h₆ (c : Γ(X, W)) : TrueGeo.valAt (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec)
          (algebraMap _ X.functionField c) = φ c := by
        rw [hfn, valAt_fnOf h₅, Points.valR_eq _ _ h₄, Points.valMap_specMap_fromSpec]
        rfl
      have h₇ : RegAt (below (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec)) h := by
        refine hgen _ (hWU h₅) ?_
        refine (congrArg (fun q : Sp (AlgebraicClosure F) ⟶ Sp (𝓞 F) =>
          (q (IsLocalRing.closedPoint (AlgebraicClosure F))).asIdeal) e₂).trans ?_
        change Ideal.comap (algebraMap (𝓞 F) F) (Ideal.comap (algebraMap F (AlgebraicClosure F))
          (IsLocalRing.maximalIdeal _)) = ⊥
        rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _
          (algebraMap F (AlgebraicClosure F)).injective,
          Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)]
      rw [← h₆ b, ← hab, valAt_mul (f := algebraMap _ X.functionField a) (regAt_fnOf h₅ _ _) h₇, h₆,
        map_mul]
      exact mul_le_of_le_one_right (e.w.nonneg _) h₃
  let := X.presheaf.algebra_section_stalk (⟨x, hxW⟩ : W)
  have : IsScalarTower Γ(X, W) (X.presheaf.stalk x) X.functionField :=
    .of_algebraMap_eq fun a => (algebraMap_germ hxW a).symm
  have := (hN x).2
  exact IsIntegrallyClosed.algebraMap_eq_of_integral (hint.tower_top (A := X.presheaf.stalk x))

private theorem valR_algX {k C : Type} [CommRing k] [CommRing C] {X : Scheme.{0}} (p : X ⟶ Sp k) (x : Sp C ⟶ X)
    (σ : k →+* C) (h : x ≫ p = spMap σ) (a : k) : valR x ⊤ (algX p ⊤ a) = σ a := by
  have := valR_appLE x p (U := ⊤) (V := ⊤) le_top (le_preimage_top x) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)
  rw [h] at this
  exact this.trans (valR_specMap (CommRingCat.ofHom σ) a)

private theorem asIdeal_gen {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
    (h : ∀ a : k, a ≠ 0 → fnOf ⊤ (Opens.mem_top _) (algX p ⊤ a) ≠ 0) : (p (genericPoint X)).asIdeal = ⊥ := by
  refine eq_bot_iff.2 fun a ha => by_contra fun h0 => ?_
  have h1 := (unitAt_fnOf_iff (x := genericPoint X) (Opens.mem_top _) _ _).1
    ((unitAt_iff (h a h0)).2 ⟨regAt_genericPoint _, regAt_genericPoint _⟩)
  have h2 := Scheme.basicOpen_appLE p ⊤ ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)
  have h3 := (h2.le h1).2
  erw [basicOpen_eq_of_affine] at h3
  exact h3 ha

end Dense

section Val

variable {C : Type} [Field C] {X : Scheme.{0}} [IsIntegral X] {x : Sp C ⟶ X} {f g : X.functionField}

private theorem unitAt_of_valAt (hf : RegAt (below x) f) (h : TrueGeo.valAt x f ≠ 0) : Cartier.UnitAt (below x) f := by
  obtain ⟨a, rfl⟩ := hf
  rw [valAt_algebraMap] at h
  exact ⟨a, (isUnit_map_iff (Scheme.stalkClosedPointTo x).hom a).1 h.isUnit, rfl⟩

private theorem valAt_add' (hf : RegAt (below x) f) (hg : RegAt (below x) g) :
    TrueGeo.valAt x (f + g) = TrueGeo.valAt x f + TrueGeo.valAt x g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_add, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_add]

private theorem valAt_one' : TrueGeo.valAt x (1 : X.functionField) = 1 := by
  rw [← map_one (algebraMap (X.presheaf.stalk (below x)) X.functionField), valAt_algebraMap, map_one]

private theorem valAt_zero' : TrueGeo.valAt x (0 : X.functionField) = 0 := by
  rw [← map_zero (algebraMap (X.presheaf.stalk (below x)) X.functionField), valAt_algebraMap, map_zero]

end Val

private theorem exists_spec {F : Type} [Field F] [NumberField F] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp (𝓞 F))
    (P : TRing F) (χ : P.R →+* X.functionField)
    (hχ : ∀ a : 𝓞 F, χ (algebraMap F P.R (a : F)) = fnOf ⊤ (Opens.mem_top _) (algX p ⊤ a)) :
    ∃ O : X.Opens, genericPoint X ∈ O ∧ ∀ x : Sp (AlgebraicClosure F) ⟶ X,
      x ≫ p = spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) → below x ∈ O →
      ∃ (K : IntermediateField F (AlgebraicClosure F)) (_ : FiniteDimensional F K) (θ : P.R →ₐ[F] K),
        ∀ r, RegAt (below x) (χ r) ∧ TrueGeo.valAt x (χ r) = θ r := by
  choose W hW a ha using fun i : Fin P.n =>
    (regAt_genericPoint (X := X) (χ (Ideal.Quotient.mk _ (MvPolynomial.X i)))).exists_fnOf
  refine ⟨⟨⋂ i, W i, isOpen_iInter_of_finite fun i => (W i).isOpen⟩, Set.mem_iInter.2 hW, fun x hx hO => ?_⟩
  have hx' : x ≫ p = spMap ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)) := by
    rw [hx, ← Spec.map_comp]; rfl
  have hint : ∀ b : 𝓞 F, RegAt (below x) (χ (algebraMap F P.R (b : F))) ∧
      TrueGeo.valAt x (χ (algebraMap F P.R (b : F))) = algebraMap F _ (b : F) := fun b => by
    rw [hχ, valAt_fnOf (Opens.mem_top _), valR_algX p x _ hx']
    exact ⟨regAt_fnOf (Opens.mem_top _) _ _, rfl⟩
  have hc : ∀ c : F, RegAt (below x) (χ (algebraMap F P.R c)) ∧
      TrueGeo.valAt x (χ (algebraMap F P.R c)) = algebraMap F _ c := fun c => by
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) c
    have hd0 : algebraMap F (AlgebraicClosure F) (d : F) ≠ 0 := by
      simpa using nonZeroDivisors.ne_zero hd
    have hu := unitAt_of_valAt (hint d).1 ((hint d).2 ▸ hd0)
    have e : χ (algebraMap F P.R (algebraMap (𝓞 F) F n / algebraMap (𝓞 F) F d)) =
        χ (algebraMap F P.R (n : F)) * (χ (algebraMap F P.R (d : F)))⁻¹ := by
      rw [← div_eq_mul_inv]
      exact map_div₀ (χ.comp (algebraMap F P.R)) _ _
    have hr := (hint n).1.mul hu.inv.regAt
    refine ⟨e ▸ hr, ?_⟩
    have e2 := valAt_mul hr (hint d).1
    rw [inv_mul_cancel_right₀ hu.ne_zero, (hint n).2, (hint d).2, ← e] at e2
    rw [map_div₀ (algebraMap F (AlgebraicClosure F)), eq_div_iff hd0]
    exact e2.symm
  have hreg : ∀ r, RegAt (below x) (χ r) := fun r => by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective r
    induction q using MvPolynomial.induction_on with
    | C c => exact (hc c).1
    | add q q' h h' => rw [map_add, map_add]; exact h.add h'
    | mul_X q i h =>
      rw [map_mul, map_mul, ← ha i]
      exact h.mul (regAt_fnOf (Set.mem_iInter.1 hO i) _ _)
  let θ : P.R →ₐ[F] AlgebraicClosure F :=
    { toFun := fun r => TrueGeo.valAt x (χ r)
      map_one' := by rw [map_one, valAt_one']
      map_mul' := fun r r' => by rw [map_mul, valAt_mul (hreg r) (hreg r')]
      map_zero' := by rw [map_zero, valAt_zero']
      map_add' := fun r r' => by rw [map_add, valAt_add' (hreg r) (hreg r')]
      commutes' := fun c => (hc c).2 }
  let K := IntermediateField.adjoin F (Set.range fun i : Fin P.n => θ (Ideal.Quotient.mk _ (MvPolynomial.X i)))
  have hK : ∀ r, θ r ∈ K := fun r => by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective r
    induction q using MvPolynomial.induction_on with
    | C c => exact (θ.commutes c).symm ▸ K.algebraMap_mem c
    | add q q' h h' => rw [map_add, map_add]; exact K.add_mem h h'
    | mul_X q i h =>
      rw [map_mul, map_mul]
      exact K.mul_mem h (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  exact ⟨K, IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y,
    θ.codRestrict K.toSubalgebra hK, fun r => ⟨hreg r, rfl⟩⟩

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

private theorem exists_frPt_spec (Z : Comp Xo c) {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp (𝓞 c.F))
    (ψ : Om Z →+* X.functionField)
    (hψ : ∀ a : 𝓞 c.F, ψ (algebraMap c.F (Om Z) (a : c.F)) = fnOf ⊤ (Opens.mem_top _) (algX p ⊤ a)) :
    ∃ O : X.Opens, genericPoint X ∈ O ∧ ∀ x : Sp (AlgebraicClosure c.F) ⟶ X,
      x ≫ p = spMap (algebraMap c.F (AlgebraicClosure c.F)) ≫ spMap (algebraMap (𝓞 c.F) c.F) → below x ∈ O →
      ∃ (K : IntermediateField c.F (AlgebraicClosure c.F)) (_ : FiniteDimensional c.F K) (y : FrPt Xo c K),
        ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, RegAt (below x) (ψ (genVal Z f)) ∧
          TrueGeo.valAt x (ψ (genVal Z f)) = (evR Xo c f y : K) := by
  have hG := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  obtain ⟨P, φ, u, hu⟩ := fromTest_of_isLocalRing (genFr hG Z)
  obtain ⟨O, hO, h⟩ := exists_spec p P (ψ.comp (φ : P.R →+* Om Z)) fun a => by
    rw [← hψ, ← φ.commutes]; rfl
  refine ⟨O, hO, fun x hx hxO => ?_⟩
  obtain ⟨K, hK, θ, hθ⟩ := h x hx hxO
  obtain ⟨y, hy⟩ := exists_frMap θ u
  refine ⟨K, hK, y, fun e f hf => ?_⟩
  rw [genVal_apply hG, evC, evR_eq hf.1 hu, evR_eq hf.1 hy]
  exact hθ _

variable {K : Type} [Field K] [NumberField K] [Algebra c.F K] {y : FrPt Xo c K} {v : FinitePlace K}

private theorem abs_le_iff (F : FinFr y v) {e' : ℕ} (he : 0 < e') (a b : F.T.Fr) :
    F.abs a ≤ F.abs b ↔ nval F.T.V e' b ≤ nval F.T.V e' a := by
  have h1 := one_lt_absNorm_real v.maximalIdeal
  by_cases ha : a = 0
  · subst ha
    simp only [map_zero, nval_zero, le_top, iff_true]
    exact F.abs.nonneg _
  by_cases hb : b = 0
  · subst hb
    rw [map_zero, nval_zero, nval_of_ne ha, top_le_iff]
    exact iff_of_false (F.abs.pos ha).not_ge (EReal.coe_ne_top _)
  rw [F.abs_apply, F.abs_apply, nval_of_ne ha, nval_of_ne hb, nval_of_ne ha, nval_of_ne hb]
  simp only [nrmOf, EReal.coe_ne_top, if_false, EReal.toReal_coe, EReal.coe_le_coe_iff]
  rw [Real.rpow_le_rpow_left_iff h1, neg_le_neg_iff, div_le_div_iff_of_pos_right (by exact_mod_cast F.lies.1),
    div_le_div_iff_of_pos_right (by exact_mod_cast he)]

private theorem nval_pow' (F : FinFr y v) (e' : ℕ) {a : F.T.Fr} (ha : a ≠ 0) (n : ℕ) :
    nval F.T.V e' (a ^ n) = (n : EReal) * nval F.T.V e' a := by
  rw [nval_of_ne ha, nval_of_ne (pow_ne_zero n ha), vV, vV, map_pow, WithZero.log_pow, ← EReal.coe_natCast,
    ← EReal.coe_mul]
  congr 1
  push_cast
  simp only [nsmul_eq_mul]
  push_cast
  ring

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7}
  (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

private theorem small_le {Z : Comp Xo c} {G : WTZ E} {τ : ℕ} {t : ℝ} {f : cuspOn U Z (τ • G)}
    (hf : f ∈ smallL U x V dict Z G τ t) {w₀ : latOn U Z G} (h0 : evR Xo c (w₀ : cuspOn U Z G) y ≠ 0)
    (hw : ∀ w : latOn U Z G, v (evR Xo c (w : cuspOn U Z G) y) ≤ v (evR Xo c (w₀ : cuspOn U Z G) y)) :
    v (evR Xo c f y) ≤ v (evR Xo c (w₀ : cuspOn U Z G) y) ^ τ := by
  obtain ⟨F⟩ := FinFr.nonempty y v
  obtain ⟨la, e', ho, hv⟩ := F.exists_mem_valSet
  have hsec : ∀ {G' : WTZ E} (g : cuspOn U Z G'), (g : Rul Xo c) ∈ secZ Xo c (exZ Dw G') := fun g =>
    AllWt.cuspW_le_secZ _ (AllWt.cuspOn_le U Z _ g.2)
  have h1 := hf.1 la _ hv
  have hfac : F.fac (exZ Dw (τ • G)) = F.fac (exZ Dw G) ^ τ := by
    clear h1 hf f
    induction τ with
    | zero =>
      rw [zero_smul, pow_zero, ← F.fac_zero]
      congr 1
      funext i; cases i <;> rfl
    | succ n ih =>
      rw [succ_nsmul, pow_succ, ← ih, ← F.fac_add]
      congr 1
      exact funext fun i => exZ_add _ _ i
  have h2 : depthOn U Z G (fun f => nval F.T.V e' (evI F.pt f)) =
      nval F.T.V e' (evI F.pt (w₀ : cuspOn U Z G)) := by
    refine le_antisymm (iInf₂_le _ w₀.2) (le_iInf₂ fun w hw' => (abs_le_iff F ho.1 _ _).1 ?_)
    change F.nrm _ ≤ F.nrm _
    rw [F.nrm_eq (hsec w), F.nrm_eq (hsec _)]
    exact mul_le_mul_of_nonneg_left (hw ⟨w, hw'⟩) (F.fac_pos _).le
  have h3 : evI F.pt (w₀ : cuspOn U Z G) ≠ 0 := fun e => by
    have := F.nrm_eq (hsec (w₀ : cuspOn U Z G))
    rw [FinFr.nrm, e, map_zero] at this
    exact (mul_pos (F.fac_pos _) (FinitePlace.pos_iff.2 h0)).ne this
  rw [h2, ← nval_pow' F e' h3, ← abs_le_iff F ho.1, map_pow] at h1
  change F.nrm _ ≤ F.nrm _ ^ τ at h1
  rw [F.nrm_eq (hsec f), F.nrm_eq (hsec _), hfac, mul_pow] at h1
  exact le_of_mul_le_mul_left h1 (pow_pos (F.fac_pos _) _)

end Frames

private theorem exists_unit_sec {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v)
    {X : Scheme.{0}} {B : LB X} {W : Type} (s : W → B.Sec) (hs : ⨆ w, nonzeroLocus (s w) = ⊤) (k : B.ι)
    (yt : Sp e.O ⟶ X) (hU : ⊤ ≤ yt ⁻¹ᵁ B.U k) :
    (∀ w, e.w (valR (spMap e.O.subtype ≫ yt) (B.U k) ((s w).f k)) ≤ 1) ∧
      ∃ w, e.w (valR (spMap e.O.subtype ≫ yt) (B.U k) ((s w).f k)) = 1 := by
  have h1 : ∀ (O : X.Opens) (_ : ⊤ ≤ yt ⁻¹ᵁ O) (a : Γ(X, O)), e.w (valR (spMap e.O.subtype ≫ yt) O a) ≤ 1 :=
    fun O hO a => by
      rw [valR_spMap_comp _ _ _ hO]
      exact (e.mem_O _).1 (valR yt O a).2
  refine ⟨fun w => h1 _ hU _, ?_⟩
  obtain ⟨w, hw⟩ := Opens.mem_iSup.1 (hs.ge (Opens.mem_top (yt (IsLocalRing.closedPoint e.O))))
  refine ⟨w, (h1 _ hU _).antisymm ?_⟩
  have hb : ⊤ ≤ yt ⁻¹ᵁ X.basicOpen ((s w).f k) :=
    (le_preimage_iff _ _).2 ((Cartier.mem_nonzeroLocus_iff _ k ((le_preimage_iff _ _).1 hU)).1 hw)
  have hb' : ⊤ ≤ (spMap e.O.subtype ≫ yt) ⁻¹ᵁ X.basicOpen ((s w).f k) := fun z _ =>
    hb (x := spMap e.O.subtype z) trivial
  obtain ⟨b, hb1⟩ := (X.toRingedSpace.isUnit_res_basicOpen ((s w).f k)).exists_right_inv
  have h2 := congrArg (valR (spMap e.O.subtype ≫ yt) (X.basicOpen ((s w).f k))) hb1
  erw [valR_mul _ _ hb', valR_one _ _ hb', valR_res _ (X.basicOpen_le _) hb'] at h2
  have h3 := congrArg e.w h2
  rw [map_mul, map_one] at h3
  exact h3.ge.trans (mul_le_of_le_one_right (e.w.nonneg _) (h1 _ hb b))

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x₀ : ℝ) {D : D7}
  (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

set_option maxHeartbeats 1600000 in

private theorem regAt_of_small (Z : Comp Xo c) (G : WTZ E) {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp (𝓞 c.F))
    (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn U Z G → L.B.Sec)
    {Nm : (c.F →+* ℂ) → cuspOn U Z G → ℝ} {d : ℕ}
    (hM : GlobalTheory.ImageModel.IsModelOf Nm (latOn U Z G) (genPoint Z (cuspOn U Z G)) d p L ψ s) {τ : ℕ} {t : ℝ}
    {f : cuspOn U Z (τ • G)} (hf : f ∈ smallL U x₀ V dict Z G τ t) (w : latOn U Z G)
    (hw0 : genVal Z ((w : cuspOn U Z G) : Rul Xo c) ≠ 0) (k : L.B.ι) (hk : genericPoint X ∈ L.B.U k)
    (hgen : ∀ x ∈ L.B.U k, (p x).asIdeal = ⊥ → RegAt x (ψ (genVal Z (f : Rul Xo c)) *
      (ψ (genVal Z ((w : cuspOn U Z G) : Rul Xo c)))⁻¹ ^ τ * fnOf (L.B.U k) hk ((s w).f k) ^ τ)) :
    ∀ x ∈ L.B.U k, RegAt x (ψ (genVal Z (f : Rul Xo c)) *
      (ψ (genVal Z ((w : cuspOn U Z G) : Rul Xo c)))⁻¹ ^ τ * fnOf (L.B.U k) hk ((s w).f k) ^ τ) := by
  have : LocallyOfFiniteType p := by
    obtain ⟨N, j, hj, h⟩ := hM.arith.isProjOver
    have := isProper_str (𝓞 c.F) N
    rw [← h]
    infer_instance
  have hp : (p (genericPoint X)).asIdeal = ⊥ := asIdeal_gen p fun a ha => by
    rw [← hM.base]
    simpa using ha
  have hsec : ∀ {G' : WTZ E} (g : cuspOn U Z G'), (g : Rul Xo c) ∈ secZ Xo c (exZ Dw G') := fun g =>
    AllWt.cuspW_le_secZ _ (AllWt.cuspOn_le U Z _ g.2)
  obtain ⟨O₁, hO₁, hbr⟩ := exists_frPt_spec Z p ψ hM.base
  obtain ⟨O₂, hO₂, hu⟩ := ((unitAt_iff ((map_ne_zero ψ).2 hw0)).2
    ⟨regAt_genericPoint (X := X) _, regAt_genericPoint _⟩).exists_nhds
  refine regAt_of_dense p hM.normal hp (L.B.U k) (O₁ ⊓ O₂) ⟨hO₁, hO₂⟩ _ hgen fun v e yt hyt hU hO => ?_
  obtain ⟨K, hK, y, hy⟩ := hbr _ hyt hO.1
  have : NumberField K := NumberField.of_module_finite c.F K
  obtain ⟨v', hv'⟩ := exists_place e K.val
  obtain ⟨hle, w₀, hw₀⟩ := exists_unit_sec e s hM.bpf k yt hU
  have hxk : below (spMap e.O.subtype ≫ yt) ∈ L.B.U k :=
    hU (x := spMap e.O.subtype (IsLocalRing.closedPoint _)) trivial
  generalize spMap e.O.subtype ≫ yt = x at hy hle hw₀ hxk hO ⊢
  have hrat : ∀ w' : latOn U Z G, e.w (K.val (evR Xo c (w' : cuspOn U Z G) y)) =
      e.w (K.val (evR Xo c (w₀ : cuspOn U Z G) y)) * e.w (valR x (L.B.U k) ((s w').f k)) := fun w' => by
    have h1 := congrArg (TrueGeo.valAt x) (hM.ratio w' w₀ k hk)
    have h2 := hy _ _ (hsec (w' : cuspOn U Z G))
    have h3 := hy _ _ (hsec (w₀ : cuspOn U Z G))
    change TrueGeo.valAt x (ψ (genVal Z ((w' : cuspOn U Z G) : Rul Xo c)) * _) =
      TrueGeo.valAt x (ψ (genVal Z ((w₀ : cuspOn U Z G) : Rul Xo c)) * _) at h1
    rw [valAt_mul h2.1 (regAt_fnOf hxk _ _), valAt_mul h3.1 (regAt_fnOf hxk _ _), valAt_fnOf hxk, valAt_fnOf hxk] at h1
    have h4 := congrArg e.w h1
    rw [map_mul, map_mul, hw₀, mul_one] at h4
    exact (congrArg e.w h2.2).symm.trans (h4.trans (congrArg (e.w · * _) h3.2))
  have hwu := hu _ hO.2
  have hw1 := hy _ _ (hsec (w : cuspOn U Z G))
  have hw2 : K.val (evR Xo c (w : cuspOn U Z G) y) ≠ 0 := fun h => valAt_ne_zero hwu (hw1.2.trans h)
  have hw3 := e.w.pos hw2
  have h0 : evR Xo c (w₀ : cuspOn U Z G) y ≠ 0 := fun h => by
    rw [hrat w, h, map_zero, map_zero, zero_mul] at hw3
    exact lt_irrefl _ hw3
  have h5 := small_le U x₀ V dict hf h0 (v := v') fun w' => (hv' _ _).1 (by
    rw [hrat w']
    exact mul_le_of_le_one_right (e.w.nonneg _) (hle w'))
  rw [← map_pow, ← hv', map_pow, map_pow] at h5
  have hf1 := hy _ _ (hsec f)
  have hinv : TrueGeo.valAt x (ψ (genVal Z ((w : cuspOn U Z G) : Rul Xo c)))⁻¹ =
      (K.val (evR Xo c (w : cuspOn U Z G) y))⁻¹ := by
    have h := valAt_mul hwu.regAt hwu.inv.regAt
    rw [mul_inv_cancel₀ hwu.ne_zero, valAt_one', hw1.2] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  rw [valAt_mul (hf1.1.mul (regAt_pow hwu.inv.regAt _)) (regAt_pow (regAt_fnOf hxk _ _) _),
    valAt_mul hf1.1 (regAt_pow hwu.inv.regAt _), valAt_pow hwu.inv.regAt, valAt_pow (regAt_fnOf hxk _ _),
    valAt_fnOf hxk, hinv, hf1.2, map_mul, map_mul, map_pow, map_pow, map_inv₀]
  have h6 : e.w (K.val (evR Xo c (w₀ : cuspOn U Z G) y)) ^ τ * (e.w (K.val (evR Xo c (w : cuspOn U Z G) y)))⁻¹ ^ τ *
      e.w (valR x (L.B.U k) ((s w).f k)) ^ τ = 1 := by
    rw [← mul_pow, ← mul_pow, mul_right_comm, ← hrat w, mul_inv_cancel₀ hw3.ne', one_pow]
  refine le_of_le_of_eq ?_ h6
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h5 (by positivity)) (by positivity)

end Main

end GlobalTheory.ImageInject

end

theorem _root_.GlobalTheory.T.hermitian_lattice_sections_good_two : Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t, ∀ w : latOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 → (∀ (k : L.B.ι) (x : X) (hx : x ∈ L.B.U k), (p x).asIdeal = ⊥ → GlobalTheory.Cartier.RegAt x (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem hx) ((s w).f k) ^ (8 * i))) → ∀ (k : L.B.ι) (x : X) (hx : x ∈ L.B.U k), GlobalTheory.Cartier.RegAt x (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem hx) ((s w).f k) ^ (8 * i)) := by
  intro _ D T j Y e o _ _ Z u X _ p L ψ s t _ _ _ _ hM i _ f hf w hw0 hgen k x hx
  exact GlobalTheory.ImageInject.regAt_of_small Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z _ p L ψ s hM hf w hw0 k (gen_mem hx)
    (fun x' hx' h0 => hgen k x' hx' h0) x hx
