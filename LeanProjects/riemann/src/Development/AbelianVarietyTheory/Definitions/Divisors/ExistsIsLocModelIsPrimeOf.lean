import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory.FieldPair

variable {k K : Type} [Field k] [Field K]

structure Place (c : k →+* K) where

  ring : ValuationSubring K

  const_mem : ∀ a, c a ∈ ring

  dvr : IsDiscreteValuationRing ring

  essFiniteType : (c.codRestrict ring const_mem).EssFiniteType

attribute [instance] Place.dvr

namespace Place

variable {c : k →+* K} (E : Place c) {n : ℕ}

def const : k →+* E.ring := c.codRestrict E.ring E.const_mem

def ord (f : K) : ℤ := WithZero.log (Ring.ordFrac E.ring f)

def toRat (n : ℕ) : Forms E.const n →ₛₗ[E.ring.subtype] Forms c n :=
  TopForm.formMap n E.ring.subtype rfl

def IsFormOrd (η : Forms c n) (a : ℤ) : Prop :=
  ∃ ω : Forms E.const n, IsFreeGen E.ring ω ∧
    ∃ f : Kˣ, η = (f : K) • E.toRat n ω ∧ E.ord f = a

open Classical in

def formOrd (η : Forms c n) : ℤ := if h : ∃ a, E.IsFormOrd η a then h.choose else 0

def ordQ : (K →₀ ℚ) →ₗ[ℚ] ℚ := Finsupp.linearCombination ℚ fun g => (E.ord g : ℚ)

def disc (η : Forms c n) (φ : K →₀ ℚ) : ℚ := E.formOrd η - E.ordQ φ

def Contains (R : Subring K) : Prop := ∀ f ∈ R, f ∈ E.ring

def IsPrimeOf (R : Subring K) : Prop :=
  E.Contains R ∧ ∀ f ∈ E.ring, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ E.ord b = 0 ∧ f * b = a

@[simp] theorem ordQ_single (g : K) (t : ℚ) : E.ordQ (Finsupp.single g t) = t * E.ord g := by
  simp [ordQ]

theorem ext {E F : Place c} (h : E.ring = F.ring) : E = F := by
  cases E; cases F; cases h; rfl

@[simp] theorem ord_one : E.ord 1 = 0 := by simp [ord]

theorem ord_mul {f g : K} (hf : f ≠ 0) (hg : g ≠ 0) : E.ord (f * g) = E.ord f + E.ord g := by
  rw [ord, ord, ord, map_mul, WithZero.log_mul ((map_ne_zero _).2 hf) ((map_ne_zero _).2 hg)]

theorem ord_inv (f : K) : E.ord f⁻¹ = -E.ord f := by
  rw [ord, ord, map_inv₀, WithZero.log_inv]

theorem ord_zpow (f : K) (m : ℤ) : E.ord (f ^ m) = m * E.ord f := by
  rw [ord, ord, map_zpow₀, WithZero.log_zpow, smul_eq_mul]

theorem ord_pow (f : K) (m : ℕ) : E.ord (f ^ m) = m * E.ord f := by
  rw [← zpow_natCast, ord_zpow]

theorem ord_nonneg_iff {f : K} (hf : f ≠ 0) : 0 ≤ E.ord f ↔ f ∈ E.ring := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  have h := le_ordTop_vw_iff (F := K) ht 0 f
  rw [ordTop_vw_of_ne_zero _ hf, WithTop.coe_le_coe] at h
  refine h.trans ⟨?_, fun hf => ⟨⟨_, hf⟩, by simp⟩⟩
  rintro ⟨a, ha⟩
  rw [ha, zpow_zero, one_mul]
  exact a.2

theorem ord_eq_zero {u : E.ring} (hu : IsUnit u) : E.ord (u : K) = 0 :=
  (congrArg WithZero.log (Ring.ordFrac_of_isUnit hu)).trans WithZero.log_one

theorem ord_irreducible {t : E.ring} (ht : Irreducible t) : E.ord (t : K) = 1 :=
  (congrArg WithZero.log (Ring.ordFrac_irreducible (K := K) ht)).trans (WithZero.log_exp 1)

theorem ring_ne_top : E.ring ≠ ⊤ := by
  intro h
  refine IsDiscreteValuationRing.not_isField E.ring ?_
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha => ?_⟩
  have ha' : (a : K) ≠ 0 := fun e => ha (Subtype.ext e)
  exact ⟨⟨(a : K)⁻¹, h.ge trivial⟩, Subtype.ext (mul_inv_cancel₀ ha')⟩

theorem Contains.mono {E : Place c} {R R' : Subring K} (h : E.Contains R') (hR : R ≤ R') :
    E.Contains R := fun f hf => h f (hR hf)

theorem contains_ring_iff (F : Place c) : F.Contains E.ring.toSubring ↔ F = E :=
  ⟨fun h => ext (ValuationSubring.eq_of_le_of_ne_top E.ring h F.ring_ne_top).symm,
    fun h => h ▸ fun _ hf => hf⟩

theorem isPrimeOf_self : E.IsPrimeOf E.ring.toSubring :=
  ⟨fun _ h => h, fun f hf => ⟨f, hf, 1, one_mem _, one_ne_zero, E.ord_one, mul_one f⟩⟩

theorem isPrimeOf_ring_iff (F : Place c) : F.IsPrimeOf E.ring.toSubring ↔ F = E :=
  ⟨fun h => (E.contains_ring_iff F).1 h.1, fun h => h ▸ F.isPrimeOf_self⟩

theorem isFreeGen_toRat {ω : Forms E.const n} (hω : IsFreeGen E.ring ω) :
    IsFreeGen K (E.toRat n ω) := by
  letI := E.const.toAlgebra
  letI := c.toAlgebra
  haveI : IsScalarTower k E.ring K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FormallyEtale E.ring K := .of_isLocalization (nonZeroDivisors E.ring)
  exact hω.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k E.ring K) n)

theorem toRat_ne_zero {ω : Forms E.const n} (hω : IsFreeGen E.ring ω) : E.toRat n ω ≠ 0 :=
  fun h => one_ne_zero ((E.isFreeGen_toRat hω).1 (a₁ := 1) (a₂ := 0) (by simp [h]))

variable {E}

theorem IsFormOrd.ne_zero {η : Forms c n} {a : ℤ} (h : E.IsFormOrd η a) : η ≠ 0 := by
  obtain ⟨ω, hω, f, rfl, -⟩ := h
  exact smul_ne_zero f.ne_zero (E.toRat_ne_zero hω)

theorem IsFormOrd.unique {η : Forms c n} {a b : ℤ} (h : E.IsFormOrd η a)
    (h' : E.IsFormOrd η b) : a = b := by
  obtain ⟨ω, hω, f, rfl, rfl⟩ := h
  obtain ⟨ω', hω', g, e, rfl⟩ := h'
  obtain ⟨u, rfl⟩ := hω.2 ω'
  have hu := hω.smul_iff.1 hω'
  rw [map_smulₛₗ, smul_smul] at e
  have e' : (f : K) = g * u := smul_left_injective _ (E.toRat_ne_zero hω) e
  have hu0 : (u : K) ≠ 0 := (hu.map E.ring.subtype).ne_zero
  rw [e', E.ord_mul g.ne_zero hu0, E.ord_eq_zero hu, add_zero]

theorem IsFormOrd.formOrd_eq {η : Forms c n} {a : ℤ} (h : E.IsFormOrd η a) :
    E.formOrd η = a := by
  have h' : ∃ a, E.IsFormOrd η a := ⟨a, h⟩
  rw [formOrd, dif_pos h']
  exact h'.choose_spec.unique h

variable (E)

theorem formOrd_smul_toRat {ω : Forms E.const n} (hω : IsFreeGen E.ring ω) {f : K} (hf : f ≠ 0) :
    E.formOrd (f • E.toRat n ω) = E.ord f :=
  IsFormOrd.formOrd_eq ⟨ω, hω, Units.mk0 f hf, rfl, rfl⟩

theorem formOrd_toRat {ω : Forms E.const n} (hω : IsFreeGen E.ring ω) :
    E.formOrd (E.toRat n ω) = 0 := by
  simpa using E.formOrd_smul_toRat hω one_ne_zero

end Place

def Klt (c : k →+* K) (n : ℕ) (R : Subring K) (η : Forms c n) (φ : K →₀ ℚ) : Prop :=
  η ≠ 0 ∧ φ 0 = 0 ∧ ∀ E : Place c, E.Contains R → -1 < E.disc η φ

def EffAt (c : k →+* K) (n : ℕ) (R : Subring K) (η : Forms c n) (φ : K →₀ ℚ) : Prop :=
  η ≠ 0 ∧ φ 0 = 0 ∧ ∀ E : Place c, E.IsPrimeOf R → E.disc η φ ≤ 0

section KltApi

variable {c : k →+* K} {n : ℕ} {R R' : Subring K} {η : Forms c n} {φ : K →₀ ℚ}

theorem Klt.form_ne_zero (h : Klt c n R η φ) : η ≠ 0 := h.1

theorem Klt.apply_zero (h : Klt c n R η φ) : φ 0 = 0 := h.2.1

theorem Klt.lt_disc (h : Klt c n R η φ) {E : Place c} (hE : E.Contains R) : -1 < E.disc η φ :=
  h.2.2 E hE

theorem Klt.mono (h : Klt c n R η φ) (hR : R ≤ R') : Klt c n R' η φ :=
  ⟨h.1, h.2.1, fun _ hE => h.lt_disc (hE.mono hR)⟩

theorem EffAt.form_ne_zero (h : EffAt c n R η φ) : η ≠ 0 := h.1

theorem EffAt.apply_zero (h : EffAt c n R η φ) : φ 0 = 0 := h.2.1

theorem EffAt.disc_le (h : EffAt c n R η φ) {E : Place c} (hE : E.IsPrimeOf R) :
    E.disc η φ ≤ 0 := h.2.2 E hE

theorem klt_ring_iff (E : Place c) (hη : η ≠ 0) (hφ : φ 0 = 0) :
    Klt c n E.ring.toSubring η φ ↔ -1 < E.disc η φ :=
  ⟨fun h => h.lt_disc E.isPrimeOf_self.1,
    fun h => ⟨hη, hφ, fun F hF => (E.contains_ring_iff F).1 hF ▸ h⟩⟩

theorem effAt_ring_iff (E : Place c) (hη : η ≠ 0) (hφ : φ 0 = 0) :
    EffAt c n E.ring.toSubring η φ ↔ E.disc η φ ≤ 0 :=
  ⟨fun h => h.disc_le E.isPrimeOf_self,
    fun h => ⟨hη, hφ, fun F hF => (E.isPrimeOf_ring_iff F).1 hF ▸ h⟩⟩

theorem klt_uniformiser_iff (E : Place c) {ω : Forms E.const n} (hω : IsFreeGen E.ring ω)
    {t : E.ring} (ht : Irreducible t) (s : ℚ) :
    Klt c n E.ring.toSubring (E.toRat n ω) (Finsupp.single (t : K) s) ↔ s < 1 := by
  have h0 : (0 : K) ≠ t := fun h => ht.ne_zero (Subtype.ext h.symm)
  rw [klt_ring_iff E (E.toRat_ne_zero hω) (Finsupp.single_eq_of_ne h0), Place.disc,
    Place.ordQ_single, E.ord_irreducible ht, E.formOrd_toRat hω]
  push_cast
  constructor <;> intro <;> linarith

theorem effAt_uniformiser_iff (E : Place c) {ω : Forms E.const n} (hω : IsFreeGen E.ring ω)
    {t : E.ring} (ht : Irreducible t) (s : ℚ) :
    EffAt c n E.ring.toSubring (E.toRat n ω) (Finsupp.single (t : K) s) ↔ 0 ≤ s := by
  have h0 : (0 : K) ≠ t := fun h => ht.ne_zero (Subtype.ext h.symm)
  rw [effAt_ring_iff E (E.toRat_ne_zero hω) (Finsupp.single_eq_of_ne h0), Place.disc,
    Place.ordQ_single, E.ord_irreducible ht, E.formOrd_toRat hω]
  push_cast
  constructor <;> intro <;> linarith

end KltApi

structure IsLocModel (c : k →+* K) (R : Subring K) : Prop where

  const_mem : ∀ a, c a ∈ R

  isLocalRing : IsLocalRing R

  essFiniteType : (c.codRestrict R const_mem).EssFiniteType

  frac : ∀ f : K, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ f * b = a

def TrBasis (c : k →+* K) {n : ℕ} (x : Fin n → K) : Prop :=
  letI := c.toAlgebra
  IsTranscendenceBasis k x

theorem isLocModel_self : IsLocModel (RingHom.id k) ⊤ where
  const_mem _ := trivial
  isLocalRing := (Subring.topEquiv (R := k)).symm.isLocalRing
  essFiniteType := (RingHom.FiniteType.of_surjective _ fun a => ⟨a.1, rfl⟩).essFiniteType
  frac f := ⟨f, trivial, 1, trivial, one_ne_zero, mul_one f⟩

namespace Place

variable {c : k →+* K} (E : Place c) {n : ℕ}

theorem isLocModel : IsLocModel c E.ring.toSubring where
  const_mem := E.const_mem
  isLocalRing := inferInstanceAs (IsLocalRing E.ring)
  essFiniteType := E.essFiniteType
  frac f := by
    obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := E.ring) f
    have hb0 : (b : K) ≠ 0 := fun h => nonZeroDivisors.ne_zero hb (Subtype.ext h)
    refine ⟨a, a.2, b, b.2, hb0, ?_⟩
    rw [← e]
    exact div_mul_cancel₀ _ hb0

theorem exists_isFreeGen [PerfectField k] {x : Fin n → K} (hx : TrBasis c x) :
    ∃ ω : Forms E.const n, IsFreeGen E.ring ω := by
  letI := E.const.toAlgebra
  letI := c.toAlgebra
  haveI : IsScalarTower k E.ring K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType k E.ring := E.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField k E.ring
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨m, z, b, -, hb⟩ := exists_basis_kaehler_uniformiser k ht
  have h1 := trdeg_eq_of_basis_kaehler k K b
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := k) hx
  rw [h1, Cardinal.mk_fin] at h2
  obtain rfl : n = m + 1 := by exact_mod_cast h2
  exact ⟨_, isFreeGen_dForm z b hb⟩

theorem isFormOrd_formOrd [PerfectField k] {x : Fin n → K} (hx : TrBasis c x) {η : Forms c n}
    (hη : η ≠ 0) : E.IsFormOrd η (E.formOrd η) := by
  obtain ⟨ω, hω⟩ := E.exists_isFreeGen hx
  obtain ⟨f, rfl⟩ := (E.isFreeGen_toRat hω).2 η
  have hf : f ≠ 0 := fun h => hη (by rw [h]; exact zero_smul _ _)
  have h : E.IsFormOrd (f • E.toRat n ω) _ := ⟨ω, hω, Units.mk0 f hf, rfl, rfl⟩
  exact h.formOrd_eq.symm ▸ h

theorem formOrd_smul [PerfectField k] {x : Fin n → K} (hx : TrBasis c x) {η : Forms c n}
    (hη : η ≠ 0) {f : K} (hf : f ≠ 0) : E.formOrd (f • η) = E.ord f + E.formOrd η := by
  obtain ⟨ω, hω, g, e, h⟩ := E.isFormOrd_formOrd hx hη
  rw [← h, e, smul_smul, E.formOrd_smul_toRat hω (mul_ne_zero hf g.ne_zero),
    E.ord_mul hf g.ne_zero]

end Place

section Scheme

variable {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {n : ℕ}

def locRing (x : X) : Subring X.functionField :=
  (algebraMap (X.presheaf.stalk x) X.functionField).range

theorem mem_locRing {x : X} {f : X.functionField} : f ∈ locRing x ↔ RegAt x f := Iff.rfl

def placeEquiv (p : X ⟶ Sp k) : DivOver p ≃ Place (Cartier.constFn p) where
  toFun E := ⟨E.ring, E.const_mem, E.dvr, E.essFiniteType⟩
  invFun E := ⟨E.ring, E.const_mem, E.dvr, E.essFiniteType⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem ord_placeEquiv (E : DivOver p) (f : X.functionFieldˣ) :
    (placeEquiv p E).ord f = E.ord f := rfl

theorem formOrd_placeEquiv (E : DivOver p) (η : RatForms p n) :
    (placeEquiv p E).formOrd η = E.formOrd η := rfl

theorem contains_placeEquiv (E : DivOver p) (x : X) :
    (placeEquiv p E).Contains (locRing x) ↔ E.Through x := Iff.rfl

theorem disc_placeEquiv (E : DivOver p) (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ) :
    (placeEquiv p E).disc η (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) =
      discrep E η m g := by
  rw [Place.disc, Place.ordQ_single, discrep, formOrd_placeEquiv, ord_placeEquiv]
  ring

theorem nonempty_place_affineLine :
    Nonempty (Place (Cartier.constFn (spMap (algebraMap k (Polynomial k))))) :=
  have ⟨_, E, _⟩ := DivOver.exists_isAt_affineLine (k := k)
  ⟨placeEquiv _ E⟩

theorem isLocModel_locRing [LocallyOfFiniteType p] (z : X) :
    IsLocModel (Cartier.constFn p) (locRing z) := by
  let e : X.presheaf.stalk z ≃+* locRing z := RingEquiv.ofBijective
    (algebraMap (X.presheaf.stalk z) X.functionField).rangeRestrict
    ⟨fun _ _ e => IsFractionRing.injective _ X.functionField (congrArg Subtype.val e),
      RingHom.rangeRestrict_surjective _⟩
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (x := z) (U := ⊤) trivial
  have hc (a : k) : algebraMap _ X.functionField (X.presheaf.germ U z hz (algX p U a)) =
      Cartier.constFn p a :=
    (algebraMap_germ hz _).trans (RingHom.congr_fun (fnOf_comp_algX p U _) a)
  refine ⟨fun a => ⟨_, hc a⟩, e.isLocalRing, ?_, fun f => ?_⟩
  · have h1 : (algX p U).FiniteType :=
      (p.finiteType_appLE (isAffineOpen_top _) hU _).comp
        (.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
    have h2 : (X.presheaf.germ U z hz).hom.EssFiniteType :=
      letI := X.presheaf.algebra_section_stalk (⟨z, hz⟩ : U)
      haveI := hU.isLocalization_stalk ⟨z, hz⟩
      Algebra.EssFiniteType.of_isLocalization (X.presheaf.stalk z)
        (hU.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl
    have h3 := (h1.essFiniteType.comp h2).comp
      (RingHom.FiniteType.of_surjective e.toRingHom e.surjective).essFiniteType
    convert h3 using 1
    exact RingHom.ext fun a => Subtype.ext (hc a).symm
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk z) f
    have hb' : algebraMap _ X.functionField b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    exact ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hb', div_mul_cancel₀ _ hb'⟩

theorem kltAt_iff_exists_klt (Δ : X → ℚ) (x : X) : KltAt p n Δ x ↔
    ∃ (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ), 0 < m ∧ IsLogEqn p Δ η x m g ∧
      Klt (Cartier.constFn p) n (locRing x) η
        (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) := by
  refine exists₃_congr fun η m g => ⟨fun ⟨h₁, h₂, h₃, h⟩ =>
    ⟨h₂, h₃, h₁, Finsupp.single_eq_of_ne g.ne_zero.symm, fun E hE => ?_⟩,
    fun ⟨h₂, h₃, h⟩ => ⟨h.1, h₂, h₃, fun E hE => ?_⟩⟩
  · obtain ⟨E, rfl⟩ := (placeEquiv p).surjective E
    rw [disc_placeEquiv]
    exact h E hE
  · rw [← disc_placeEquiv]
    exact h.lt_disc hE

theorem kltAt_iff_klt [PerfectField k] [LocallyOfFiniteType p] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (hn : topologicalKrullDim X = n) {Δ : X → ℚ} {x : X}
    {η : RatForms p n} {m : ℕ} {g : X.functionFieldˣ} (hη : η ≠ 0) (hm : 0 < m)
    (h : IsLogEqn p Δ η x m g) : KltAt p n Δ x ↔
      Klt (Cartier.constFn p) n (locRing x) η
        (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) := by
  refine ⟨fun h' => ⟨hη, Finsupp.single_eq_of_ne g.ne_zero.symm, fun E hE => ?_⟩,
    fun h' => (kltAt_iff_exists_klt Δ x).2 ⟨η, m, g, hm, h, h'⟩⟩
  obtain ⟨E, rfl⟩ := (placeEquiv p).surjective E
  rw [disc_placeEquiv]
  exact (h.kltAt_iff hn hη hm).1 h' E hE

end Scheme

theorem exists_isLocModel_isPrimeOf :
    ∃ (R : Subring _) (E : Place (Cartier.constFn (spMap (algebraMap k (Polynomial k))))),
      IsLocModel (Cartier.constFn (spMap (algebraMap k (Polynomial k)))) R ∧ E.IsPrimeOf R :=
  have ⟨E⟩ := nonempty_place_affineLine (k := k)
  ⟨_, E, E.isLocModel, E.isPrimeOf_self⟩

theorem exists_threshold_affineLine [PerfectField k] :
    ∃ (R : Subring (Sp (Polynomial k)).functionField)
      (η : Forms (Cartier.constFn (spMap (algebraMap k (Polynomial k)))) 1)
      (t : (Sp (Polynomial k)).functionField),
      IsLocModel (Cartier.constFn (spMap (algebraMap k (Polynomial k)))) R ∧
      ∀ s : ℚ, (Klt _ 1 R η (Finsupp.single t s) ↔ s < 1) ∧
        (EffAt _ 1 R η (Finsupp.single t s) ↔ 0 ≤ s) := by
  obtain ⟨z, E, -⟩ := DivOver.exists_isAt_affineLine (k := k)
  haveI : LocallyOfFiniteType (spMap (algebraMap k (Polynomial k))) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  have hn : topologicalKrullDim (Sp (Polynomial k)) = (1 : ℕ) := by
    change topologicalKrullDim (PrimeSpectrum (Polynomial k)) = _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    norm_num
  obtain ⟨ω, hω⟩ := E.exists_isFreeGen hn
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (placeEquiv _ E).ring
  exact ⟨_, _, _, (placeEquiv _ E).isLocModel, fun s =>
    ⟨klt_uniformiser_iff (placeEquiv _ E) hω ht s, effAt_uniformiser_iff (placeEquiv _ E) hω ht s⟩⟩

theorem trBasis_fractionRing (n : ℕ) :
    TrBasis (algebraMap k (FractionRing (MvPolynomial (Fin n) k)))
      fun i => algebraMap (MvPolynomial (Fin n) k) _ (MvPolynomial.X i) := by
  haveI : Algebra.IsAlgebraic (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  have h : IsTranscendenceBasis k
      (algebraMap (MvPolynomial (Fin n) k) (FractionRing (MvPolynomial (Fin n) k)) ∘
        MvPolynomial.X) := (IsTranscendenceBasis.mvPolynomial (Fin n) k).algebraMap_comp
  have e : (algebraMap k (FractionRing (MvPolynomial (Fin n) k))).toAlgebra =
      (inferInstance : Algebra k (FractionRing (MvPolynomial (Fin n) k))) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  unfold TrBasis
  rw [e]
  exact h

example (c : k →+* K) (n : ℕ) (R : Subring K) (φ : K →₀ ℚ) :
    ¬ Klt c n R 0 φ ∧ ¬ EffAt c n R 0 φ := ⟨fun h => h.1 rfl, fun h => h.1 rfl⟩

example (c : k →+* K) (n : ℕ) (R : Subring K) (η : Forms c n) :
    ¬ Klt c n R η (Finsupp.single 0 1) := fun h => by simpa using h.apply_zero

end GlobalTheory.FieldPair
