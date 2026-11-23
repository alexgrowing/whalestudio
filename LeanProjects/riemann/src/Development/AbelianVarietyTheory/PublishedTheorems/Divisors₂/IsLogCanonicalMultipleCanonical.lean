import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh

namespace GlobalTheory.Discrepancy

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]

structure DivOver (p : X ⟶ Sp k) where

  ring : ValuationSubring X.functionField

  const_mem : ∀ a, Cartier.constFn p a ∈ ring

  dvr : IsDiscreteValuationRing ring

  essFiniteType : ((Cartier.constFn p).codRestrict ring const_mem).EssFiniteType

attribute [instance] DivOver.dvr

namespace DivOver

variable {p : X ⟶ Sp k} (E : DivOver p) {n : ℕ}

def const : k →+* E.ring := (Cartier.constFn p).codRestrict E.ring E.const_mem

def ord (f : X.functionFieldˣ) : ℤ := WithZero.log (Ring.ordFrac E.ring (f : X.functionField))

def Through (x : X) : Prop := ∀ f, RegAt x f → f ∈ E.ring

def IsAt (z : X) : Prop := ∀ f, f ∈ E.ring ↔ RegAt z f

def toRat (n : ℕ) : Forms E.const n →ₛₗ[E.ring.subtype] RatForms p n :=
  TopForm.formMap n E.ring.subtype rfl

def IsFormOrd (η : RatForms p n) (a : ℤ) : Prop :=
  ∃ ω : Forms E.const n, IsFreeGen E.ring ω ∧
    ∃ f : X.functionFieldˣ, η = (f : X.functionField) • E.toRat n ω ∧ E.ord f = a

open Classical in

def formOrd (η : RatForms p n) : ℤ := if h : ∃ a, E.IsFormOrd η a then h.choose else 0

theorem ord_mul (f g : X.functionFieldˣ) : E.ord (f * g) = E.ord f + E.ord g := by
  rw [ord, ord, ord, Units.val_mul, map_mul,
    WithZero.log_mul ((map_ne_zero _).2 f.ne_zero) ((map_ne_zero _).2 g.ne_zero)]

@[simp] theorem ord_one : E.ord 1 = 0 := by simp [ord]

theorem ord_nonneg_iff (f : X.functionFieldˣ) :
    0 ≤ E.ord f ↔ (f : X.functionField) ∈ E.ring := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  have h := le_ordTop_vw_iff (F := X.functionField) ht 0 f
  rw [ordTop_vw_of_ne_zero _ f.ne_zero, WithTop.coe_le_coe] at h
  refine h.trans ⟨?_, fun hf => ⟨⟨_, hf⟩, by simp⟩⟩
  rintro ⟨a, ha⟩
  rw [ha, zpow_zero, one_mul]
  exact a.2

theorem ord_eq_zero {f : X.functionFieldˣ} {u : E.ring} (hu : IsUnit u)
    (e : (u : X.functionField) = f) : E.ord f = 0 := by
  rw [ord, ← e]
  exact (congrArg WithZero.log (Ring.ordFrac_of_isUnit hu)).trans WithZero.log_one

variable {E}

theorem IsFormOrd.unique {η : RatForms p n} (hη : η ≠ 0) {a b : ℤ} (h : E.IsFormOrd η a)
    (h' : E.IsFormOrd η b) : a = b := by
  obtain ⟨ω, hω, f, rfl, rfl⟩ := h
  obtain ⟨ω', hω', g, e, rfl⟩ := h'
  obtain ⟨u, rfl⟩ := hω.2 ω'
  have hu := hω.smul_iff.1 hω'
  have h0 : E.toRat n ω ≠ 0 := fun h => hη (by rw [h, smul_zero])
  rw [map_smulₛₗ, smul_smul] at e
  have e' := smul_left_injective _ h0 e
  have hu0 : (u : X.functionField) ≠ 0 := (hu.map E.ring.subtype).ne_zero
  obtain rfl : f = g * Units.mk0 _ hu0 := Units.ext e'
  rw [ord_mul, E.ord_eq_zero (f := Units.mk0 _ hu0) hu rfl, add_zero]

theorem IsFormOrd.formOrd_eq {η : RatForms p n} (hη : η ≠ 0) {a : ℤ} (h : E.IsFormOrd η a) :
    E.formOrd η = a := by
  have h' : ∃ a, E.IsFormOrd η a := ⟨a, h⟩
  rw [formOrd, dif_pos h']
  exact h'.choose_spec.unique hη h

variable (E)

theorem isFreeGen_toRat {ω : Forms E.const n} (hω : IsFreeGen E.ring ω) :
    IsFreeGen X.functionField (E.toRat n ω) := by
  letI := E.const.toAlgebra
  letI := (Cartier.constFn p).toAlgebra
  haveI : IsScalarTower k E.ring X.functionField := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FormallyEtale E.ring X.functionField :=
    .of_isLocalization (nonZeroDivisors E.ring)
  exact hω.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k E.ring X.functionField) n)

theorem exists_isFreeGen [PerfectField k] [LocallyOfFiniteType p]
    (hn : topologicalKrullDim X = n) : ∃ ω : Forms E.const n, IsFreeGen E.ring ω := by
  letI := E.const.toAlgebra
  letI := (Cartier.constFn p).toAlgebra
  haveI : IsScalarTower k E.ring X.functionField := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType k E.ring := E.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField k E.ring
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨m, z, b, -, hb⟩ := exists_basis_kaehler_uniformiser k ht
  have h1 := trdeg_eq_of_basis_kaehler k X.functionField b
  have e : (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom = Cartier.constFn p := by
    letI := algebraΓOfHom p
    have e₁ : strHom k X = p := strHom_eq fun _ => rfl
    have e₂ : X.fromSpecStalk (genericPoint X) ≫ p =
        Spec.map (CommRingCat.ofHom (Cartier.constFn p)) := by
      conv_lhs => rw [← e₁, strHom, ← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
      congr 1
      ext a
      simp [Cartier.constFn, fnOf, algX, Scheme.Hom.appLE]
      rfl
    rw [e₂, Spec.preimage_map]
    rfl
  have h2 := topologicalKrullDim_preimage_genericPoint_eq p (d := m + 1) (by rw [e]; exact h1)
  have h3 : (p ⁻¹' {genericPoint (Spec (.of k))} : Set X) = Set.univ :=
    Set.eq_univ_of_forall fun _ => Subsingleton.elim (α := PrimeSpectrum k) _ _
  rw [h3, (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq, hn] at h2
  obtain rfl : n = m + 1 := by exact_mod_cast h2
  exact ⟨_, isFreeGen_dForm z b hb⟩

theorem isFormOrd_formOrd [PerfectField k] [LocallyOfFiniteType p]
    (hn : topologicalKrullDim X = n) {η : RatForms p n} (hη : η ≠ 0) :
    E.IsFormOrd η (E.formOrd η) := by
  obtain ⟨ω, hω⟩ := E.exists_isFreeGen hn
  obtain ⟨f, rfl⟩ := (E.isFreeGen_toRat hω).2 η
  have hf : f ≠ 0 := fun h => hη (by rw [h]; exact zero_smul _ _)
  have h : E.IsFormOrd (f • E.toRat n ω) _ := ⟨ω, hω, Units.mk0 f hf, rfl, rfl⟩
  exact (h.formOrd_eq hη).symm ▸ h

end DivOver

theorem regAt_of_forall_coheight_eq_one [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] {x : X}
    {f : X.functionField} (h : ∀ z, z ⤳ x → Order.coheight z = 1 → RegAt z f) : RegAt x f := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  refine (mem_range_algebraMap_iff_forall_height_eq_one (A := X.presheaf.stalk x) f).2
    fun q hq h1 => ?_
  let P : PrimeSpectrum Γ(X, U) := ⟨q.comap (algebraMap _ (X.presheaf.stalk x)), inferInstance⟩
  have hP1 : P.asIdeal.height = 1 :=
    (IsLocalization.height_comap (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl q).trans h1
  have hPQ : P ≤ hU.primeIdealOf ⟨x, hx⟩ := fun s hs => by_contra fun hs' =>
    hq.ne_top (q.eq_top_of_isUnit_mem hs (IsLocalization.map_units (X.presheaf.stalk x)
      (⟨s, hs'⟩ : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)))
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  have hzx : (z : X) ⤳ x := by
    have h := ((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨x, hx⟩)).mp hPQ).map
      hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h
  clear_value z
  haveI := hU.isLocalization_stalk z
  have hc : Order.coheight (z : X) = 1 := by
    have := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf z).asIdeal
      (X.presheaf.stalk (z : X))
    rw [ringKrullDim_stalk_eq_coheight, hP, hP1] at this
    exact_mod_cast this
  obtain ⟨a, rfl⟩ := h z hzx hc
  obtain ⟨⟨c, s⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf z).asIdeal.primeCompl a
  refine (mem_primeLocalSubalgebra_iff q _).2 ⟨algebraMap _ _ s.1, ?_, algebraMap _ _ c, ?_⟩
  · have := s.2
    rw [Ideal.mem_primeCompl_iff] at this
    have h' : s.1 ∉ P.asIdeal := by simpa only [hP] using this
    exact h'
  · have e' := congrArg (algebraMap _ X.functionField) e
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at e'
    rw [Algebra.smul_def, mul_comm]
    exact ((algebraMap_germ hx c).trans e'.symm).trans (congrArg _ (algebraMap_germ hx s.1).symm)

namespace DivOver

variable {p : X ⟶ Sp k} {E : DivOver p} {n : ℕ} {x z : X}

theorem _root_.GlobalTheory.Discrepancy.regAt_of_specializes {f : X.functionField} (h : z ⤳ x)
    (hf : RegAt x f) : RegAt z f :=
  have ⟨U, hx, a, e⟩ := hf.exists_fnOf
  e ▸ regAt_fnOf (h.mem_open U.isOpen hx) _ a

theorem Through.of_specializes (h : E.Through z) (hz : z ⤳ x) : E.Through x :=
  fun f hf => h f (regAt_of_specializes hz hf)

theorem IsAt.through (h : E.IsAt z) (hz : z ⤳ x) : E.Through x :=
  Through.of_specializes (fun f => (h f).2) hz

def IsAt.equiv (h : E.IsAt z) : X.presheaf.stalk z ≃+* E.ring :=
  RingEquiv.ofBijective
    ((algebraMap (X.presheaf.stalk z) X.functionField).codRestrict E.ring
      fun a => (h _).2 ⟨a, rfl⟩)
    ⟨fun _ _ e => IsFractionRing.injective _ X.functionField (congrArg Subtype.val e),
      fun f => have ⟨a, ha⟩ := (h f).1 f.2; ⟨a, Subtype.ext ha⟩⟩

theorem IsAt.coheight_eq_one (h : E.IsAt z) : Order.coheight z = 1 := by
  have := (ringKrullDim_eq_of_ringEquiv h.equiv).trans
    (IsDiscreteValuationRing.ringKrullDim_eq_one E.ring)
  rw [ringKrullDim_stalk_eq_coheight] at this
  exact_mod_cast this

theorem IsAt.ord_eq [IsLocallyNoetherian X] (h : E.IsAt z) (g : X.functionFieldˣ) :
    E.ord g = Scheme.ord (g : X.functionField) z := by
  haveI : IsDiscreteValuationRing (X.presheaf.stalk z) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing h.equiv.symm
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk z)
  obtain ⟨m, u, e⟩ := exists_eq_unit_mul_zpow ht g.ne_zero
  have h1 := ordTop_vw_unit_mul_zpow (F := X.functionField) ht u m
  have h2 := ordTop_vw_unit_mul_zpow (F := X.functionField) (ht.map h.equiv)
    (Units.map h.equiv.toMonoidHom u) m
  rw [← e, ordTop_vw_of_ne_zero _ g.ne_zero, WithTop.coe_inj] at h1
  replace h2 : ordTop_vw E.ring (g : X.functionField) = m := e ▸ h2
  rw [ordTop_vw_of_ne_zero _ g.ne_zero, WithTop.coe_inj] at h2
  refine h2.trans ((Scheme.ord_eq_iff h.coheight_eq_one g.ne_zero).2 ?_).symm
  rw [← h1]
  exact (WithZero.exp_log ((map_ne_zero _).2 g.ne_zero)).symm

variable (p) in

theorem exists_isAt [LocallyOfFiniteType p] (z : X)
    [IsDiscreteValuationRing (X.presheaf.stalk z)] : ∃ E : DivOver p, E.IsAt z := by
  let V : ValuationSubring X.functionField :=
    { (algebraMap (X.presheaf.stalk z) X.functionField).range with
      mem_or_inv_mem' := ValuationRing.isInteger_or_isInteger (X.presheaf.stalk z) }
  let e : X.presheaf.stalk z ≃+* V := RingEquiv.ofBijective
    (algebraMap (X.presheaf.stalk z) X.functionField).rangeRestrict
    ⟨fun _ _ e => IsFractionRing.injective _ X.functionField (congrArg Subtype.val e),
      RingHom.rangeRestrict_surjective _⟩
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (x := z) (U := ⊤) trivial
  have hc (a : k) : algebraMap _ X.functionField (X.presheaf.germ U z hz (algX p U a)) =
      Cartier.constFn p a :=
    (algebraMap_germ hz _).trans (RingHom.congr_fun (fnOf_comp_algX p U _) a)
  refine ⟨⟨V, fun a => ⟨_, hc a⟩,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, ?_⟩, fun _ => Iff.rfl⟩
  have h1 : (algX p U).FiniteType :=
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

theorem exists_isAt_of_coheight_eq_one [LocallyOfFiniteType p] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (h : Order.coheight z = 1) : ∃ E : DivOver p, E.IsAt z :=
  haveI := IsNormalScheme.isDiscreteValuationRing_stalk h
  exists_isAt p z

theorem exists_isAt_affineLine :
    ∃ (z : Sp (Polynomial k)) (E : DivOver (spMap (algebraMap k (Polynomial k)))),
    E.IsAt z := by
  let z : Sp (Polynomial k) := ⟨Ideal.span {Polynomial.X},
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X⟩
  have hz : Order.coheight z = 1 := by
    rw [← idealHeight_eq_coheight]
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors (R := Polynomial k)
      (mem_nonZeroDivisors_of_ne_zero Polynomial.X_ne_zero) Polynomial.prime_X.not_unit
  haveI : LocallyOfFiniteType (spMap (algebraMap k (Polynomial k))) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  exact ⟨z, exists_isAt_of_coheight_eq_one hz⟩

end DivOver

section Pairs

omit [IsIntegral X] in

structure IsEffQDiv (Δ : X → ℚ) : Prop where

  finite : (Function.support Δ).Finite

  coheight : ∀ z, Δ z ≠ 0 → Order.coheight z = 1

  nonneg : ∀ z, 0 ≤ Δ z

def qWeil [IsLocallyNoetherian X] (D : CartierDiv X) (m : ℕ) : X → ℚ := fun z => D.mult z / m

variable (p : X ⟶ Sp k) {n : ℕ}

def IsLogEqn (Δ : X → ℚ) (η : RatForms p n) (x : X) (m : ℕ) (g : X.functionFieldˣ) : Prop :=
  ∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → (m : ℚ) * (E.formOrd η + Δ z) = E.ord g

variable {p} in

def discrep (E : DivOver p) (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ) : ℚ :=
  E.formOrd η - E.ord g / m

variable (n) in

def KltAt (Δ : X → ℚ) (x : X) : Prop :=
  ∃ (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ), η ≠ 0 ∧ 0 < m ∧ IsLogEqn p Δ η x m g ∧
    ∀ E : DivOver p, E.Through x → -1 < discrep E η m g

variable (n) in

def LcAt (Δ : X → ℚ) (x : X) : Prop :=
  ∃ (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ), η ≠ 0 ∧ 0 < m ∧ IsLogEqn p Δ η x m g ∧
    ∀ E : DivOver p, E.Through x → -1 ≤ discrep E η m g

variable (n) in

def IsLogCanonicalMultiple (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) : Prop :=
  ∃ η : RatForms p n, η ≠ 0 ∧ ∀ x g, G.IsEqn x g → IsLogEqn p Δ η x m g

variable {p} {Δ : X → ℚ} {η η' : RatForms p n} {x z : X} {m m' : ℕ} {g g' : X.functionFieldˣ}
  {E : DivOver p}

theorem KltAt.lcAt (h : KltAt p n Δ x) : LcAt p n Δ x :=
  have ⟨η, m, g, h₁, h₂, h₃, h₄⟩ := h; ⟨η, m, g, h₁, h₂, h₃, fun E hE => (h₄ E hE).le⟩

theorem IsLogEqn.discrep_eq_neg (h : IsLogEqn p Δ η x m g) (hm : 0 < m) (hz : z ⤳ x)
    (hE : E.IsAt z) : discrep E η m g = -Δ z := by
  have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [discrep, ← h z hz E hE]
  field_simp
  ring

theorem KltAt.lt_one (h : KltAt p n Δ x) (hz : z ⤳ x) (hE : E.IsAt z) : Δ z < 1 := by
  obtain ⟨η, m, g, -, hm, hg, h⟩ := h
  have := h E (hE.through hz)
  rw [hg.discrep_eq_neg hm hz hE] at this
  linarith

theorem LcAt.le_one (h : LcAt p n Δ x) (hz : z ⤳ x) (hE : E.IsAt z) : Δ z ≤ 1 := by
  obtain ⟨η, m, g, -, hm, hg, h⟩ := h
  have := h E (hE.through hz)
  rw [hg.discrep_eq_neg hm hz hE] at this
  linarith

theorem DivOver.ord_pow (E : DivOver p) (f : X.functionFieldˣ) (r : ℕ) :
    E.ord (f ^ r) = r * E.ord f := by
  induction r with
  | zero => simp
  | succ r ih => rw [pow_succ, E.ord_mul, ih]; push_cast; ring

theorem DivOver.ord_inv (E : DivOver p) (f : X.functionFieldˣ) : E.ord f⁻¹ = -E.ord f := by
  have := E.ord_mul f f⁻¹
  rw [mul_inv_cancel, E.ord_one] at this
  omega

variable [PerfectField k] [LocallyOfFiniteType p]

theorem DivOver.formOrd_smul (E : DivOver p) (hn : topologicalKrullDim X = n) (hη : η ≠ 0)
    (f : X.functionFieldˣ) :
    E.formOrd ((f : X.functionField) • η) = E.ord f + E.formOrd η := by
  obtain ⟨ω, hω, f', e, h⟩ := E.isFormOrd_formOrd hn hη
  refine DivOver.IsFormOrd.formOrd_eq (smul_ne_zero f.ne_zero hη) ⟨ω, hω, f * f', ?_, ?_⟩
  · rw [Units.val_mul, mul_smul, ← e]
  · rw [E.ord_mul, h]

theorem discrep_eq [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (hn : topologicalKrullDim X = n) (hη : η ≠ 0) (hη' : η' ≠ 0) (hm : 0 < m) (hm' : 0 < m')
    (h : IsLogEqn p Δ η x m g) (h' : IsLogEqn p Δ η' x m' g') (hE : E.Through x) :
    discrep E η m g = discrep E η' m' g' := by
  obtain ⟨ω, hω, f, e, -⟩ := E.isFormOrd_formOrd hn hη
  obtain ⟨f', e'⟩ := (E.isFreeGen_toRat hω).2 η'
  have hf' : f' ≠ 0 := fun h => hη' (by rw [← e', h]; exact zero_smul _ _)
  obtain ⟨c, rfl⟩ : ∃ c : X.functionFieldˣ, η' = (c : X.functionField) • η :=
    ⟨Units.mk0 f' hf' * f⁻¹, by rw [e, smul_smul, ← e']; simp⟩
  have h₁ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have h₂ : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  set u : X.functionFieldˣ := c ^ (m * m') * g ^ m' * (g' ^ m)⁻¹ with hu
  have key (F : DivOver p) : (F.ord u : ℚ) = m * m' * F.ord c + m' * F.ord g - m * F.ord g' := by
    rw [hu, F.ord_mul, F.ord_mul, F.ord_inv, F.ord_pow, F.ord_pow, F.ord_pow]
    push_cast
    ring
  have h0 (z : X) (hz : z ⤳ x) (F : DivOver p) (hF : F.IsAt z) : F.ord u = 0 := by
    have a := h z hz F hF
    have b := h' z hz F hF
    rw [F.formOrd_smul hn hη] at b
    have : (F.ord u : ℚ) = 0 := by
      rw [key, ← a, ← b]
      push_cast
      ring
    exact_mod_cast this
  have reg (v : X.functionFieldˣ) (hv : ∀ z, z ⤳ x → ∀ F : DivOver p, F.IsAt z → 0 ≤ F.ord v) :
      0 ≤ E.ord v := (E.ord_nonneg_iff v).2 (hE _ (regAt_of_forall_coheight_eq_one fun z hz h1 =>
    have ⟨F, hF⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) h1
    (hF _).1 ((F.ord_nonneg_iff v).1 (hv z hz F hF))))
  have a := reg u fun z hz F hF => (h0 z hz F hF).ge
  have b := reg u⁻¹ fun z hz F hF => by rw [F.ord_inv, h0 z hz F hF, neg_zero]
  rw [E.ord_inv] at b
  have hE0 : (E.ord u : ℚ) = 0 := by exact_mod_cast (by omega : E.ord u = 0)
  rw [key] at hE0
  rw [discrep, discrep, E.formOrd_smul hn hη]
  push_cast
  field_simp
  linear_combination -hE0

theorem IsLogEqn.kltAt_iff [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (hn : topologicalKrullDim X = n) (hη : η ≠ 0) (hm : 0 < m) (h : IsLogEqn p Δ η x m g) :
    KltAt p n Δ x ↔ ∀ E : DivOver p, E.Through x → -1 < discrep E η m g :=
  ⟨fun ⟨_, _, _, h₁, h₂, h₃, h₄⟩ E hE => discrep_eq hn h₁ hη h₂ hm h₃ h hE ▸ h₄ E hE,
    fun h' => ⟨η, m, g, hη, hm, h, h'⟩⟩

theorem DivOver.formOrd_formOf_nonneg (hn : topologicalKrullDim X = n) {U : X.Opens} (hx : x ∈ U)
    (hE : E.Through x) (ω : FormsOn p n U) (h0 : formOf U (gen_mem hx) ω ≠ 0) :
    0 ≤ E.formOrd (formOf U (gen_mem hx) ω) := by
  obtain ⟨ω', hω', f, e, h⟩ := E.isFormOrd_formOrd hn h0
  let ρ : Γ(X, U) →+* E.ring :=
    (fnOf U (gen_mem hx)).codRestrict E.ring fun a => hE _ (regAt_fnOf hx _ a)
  have hρ : ρ.comp (algX p U) = E.const :=
    RingHom.ext fun a => Subtype.ext (RingHom.congr_fun (fnOf_comp_algX p U _) a)
  have e₁ : E.toRat n (TopForm.formMap n ρ hρ ω) = formOf U (gen_mem hx) ω :=
    formMap_formMap _ _ _ rfl _ _ _ ω
  obtain ⟨a, ha⟩ := hω'.2 (TopForm.formMap n ρ hρ ω)
  rw [← ha, map_smulₛₗ, e] at e₁
  rw [← h, E.ord_nonneg_iff, ← (E.isFreeGen_toRat hω').1 e₁]
  exact a.2

omit [PerfectField k] [LocallyOfFiniteType p] in

theorem DivOver.formOrd_formOf_eq_zero {U : X.Opens} (hz : z ∈ U) (hE : E.IsAt z)
    {ω : FormsOn p n U} (hω : IsFrame ω) : E.formOrd (formOf U (gen_mem hz) ω) = 0 := by
  have h0 : formOf U (gen_mem hz) ω ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_formOf (gen_mem hz) hω).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  let ρ : Γ(X, U) →+* E.ring := hE.equiv.toRingHom.comp (X.presheaf.germ U z hz).hom
  have hρ' : E.ring.subtype.comp ρ = fnOf U (gen_mem hz) :=
    RingHom.ext fun a => algebraMap_germ hz a
  have hρ : ρ.comp (algX p U) = E.const := RingHom.ext fun a => Subtype.ext
    ((RingHom.congr_fun hρ' _).trans (RingHom.congr_fun (fnOf_comp_algX p U _) a))
  have e₁ : E.toRat n (TopForm.formMap n ρ hρ ω) = formOf U (gen_mem hz) ω :=
    formMap_formMap _ _ _ hρ' _ _ _ ω
  refine DivOver.IsFormOrd.formOrd_eq h0 ⟨TopForm.formMap n ρ hρ ω, ?_, 1, by simp [e₁], E.ord_one⟩
  letI := (algX p U).toAlgebra
  letI := E.const.toAlgebra
  letI := ρ.toAlgebra
  letI := X.presheaf.algebra_section_stalk (⟨z, hz⟩ : U)
  haveI : IsScalarTower k Γ(X, U) E.ring := IsScalarTower.of_algebraMap_eq' hρ.symm
  haveI := hω.affine.isLocalization_stalk ⟨z, hz⟩
  haveI : IsLocalization (hω.affine.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl E.ring :=
    IsLocalization.isLocalization_of_algEquiv _
      (AlgEquiv.ofRingEquiv (f := hE.equiv) fun _ => rfl :
        X.presheaf.stalk z ≃ₐ[Γ(X, U)] E.ring)
  haveI : Algebra.FormallyEtale Γ(X, U) E.ring :=
    .of_isLocalization (hω.affine.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl
  exact hω.gen.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k Γ(X, U) E.ring) n)

omit [LocallyOfFiniteType p] in

theorem kltAt_zero_of_smooth [SmoothOfRelativeDimension n p] (hn : topologicalKrullDim X = n)
    (x : X) : KltAt p n 0 x := by
  haveI := SmoothOfRelativeDimension.smooth n p
  obtain ⟨U, ω, hx, hω⟩ := exists_isFrame p n x
  have h0 : formOf U (gen_mem hx) ω ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_formOf (gen_mem hx) hω).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  refine ⟨_, 1, 1, h0, one_pos, fun z hz E hE => ?_, fun E hE => ?_⟩
  · simp [DivOver.formOrd_formOf_eq_zero (hz.mem_open U.isOpen hx) hE hω]
  · have := DivOver.formOrd_formOf_nonneg hn hx hE ω h0
    have : (0 : ℚ) ≤ E.formOrd (formOf U (gen_mem hx) ω) := by exact_mod_cast this
    simp only [discrep, E.ord_one]
    norm_num
    linarith

omit [LocallyOfFiniteType p] in

theorem isLogCanonicalMultiple_canonical [IsLocallyNoetherian X] [SmoothOfRelativeDimension n p]
    (hn : topologicalKrullDim X = n) (D : CartierDiv X) (hm : 0 < m) :
    IsLogCanonicalMultiple p n (qWeil D m) m (m • canonical p n + D) := by
  haveI := SmoothOfRelativeDimension.smooth n p
  refine ⟨baseForm p n, baseForm_ne_zero p n, fun x g hg z hz E hE => ?_⟩
  obtain ⟨U, ω, hU, hω⟩ := exists_isFrame p n z
  have hgen := isFreeGen_formOf (gen_mem hU) hω
  have h0 : formOf U (gen_mem hU) ω ≠ 0 := fun h =>
    one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  obtain ⟨c, hc⟩ := hgen.2 (baseForm p n)
  have hc0 : c ≠ 0 := fun e => baseForm_ne_zero p n (by rw [← hc, e]; exact zero_smul _ _)
  have h1 := isDivOfForm_canonical p n U ω hω z hU (Units.mk0 c hc0) hc.symm
  have h2 := E.formOrd_smul hn h0 (Units.mk0 c hc0)
  rw [DivOver.formOrd_formOf_eq_zero hU hE hω, add_zero] at h2
  replace h2 : E.formOrd (baseForm p n) = E.ord (Units.mk0 c hc0) := hc ▸ h2
  obtain ⟨V, hV, hgV⟩ := hg.exists_nhds
  obtain ⟨d, hd⟩ := D.exists_isEqn z
  have h3 := ((hgV z (hz.mem_open V.isOpen hV)).mult_eq.symm.trans
    ((h1.nsmul m).add hd).mult_eq)
  rw [← hE.ord_eq, ← hE.ord_eq, E.ord_mul, E.ord_pow] at h3
  have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [h2, h3, qWeil, hd.mult_eq, ← hE.ord_eq]
  push_cast
  field_simp

end Pairs

section Checks

variable {p : X ⟶ Sp k} {n : ℕ} [IsLocallyNoetherian X]

theorem isEffQDiv_qWeil [CompactSpace X] {D : CartierDiv X} (hD : D.Eff) (m : ℕ) :
    IsEffQDiv (qWeil D m) where
  finite := D.finite_support_mult.subset fun z hz h => hz (by simp [qWeil, h])
  coheight z hz := CartierDiv.coheight_eq_one_of_mult_ne_zero (D := D) fun h =>
    hz (by simp [qWeil, h])
  nonneg z := by
    refine div_nonneg (Int.cast_nonneg ?_) (Nat.cast_nonneg m)
    obtain ⟨g, hg⟩ := D.exists_isEqn z
    obtain ⟨a, ha⟩ := CartierDiv.eff_iff.1 hD z g hg
    by_cases hz : Order.coheight z = 1
    · rw [hg.mult_eq, ← ha, ord_algebraMap hz fun h => g.ne_zero (by rw [← ha, h, map_zero])]
      exact Int.natCast_nonneg _
    · rw [hg.mult_eq, Scheme.ord_eq_zero_of_coheight_neq_one hz]

theorem not_kltAt_of_one_le [LocallyOfFiniteType p] [GlobalTheory.IsNormalScheme X] {Δ : X → ℚ} {x z : X}
    (hz : z ⤳ x) (h1 : Order.coheight z = 1) (h : 1 ≤ Δ z) : ¬ KltAt p n Δ x := fun hk =>
  have ⟨_, hE⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) h1
  (hk.lt_one hz hE).not_ge h

example (d : ℕ) (x : (ProjVar.proj ℂ d).X) :
    KltAt (ProjVar.proj ℂ d).str (ProjVar.proj ℂ d).dim 0 x :=
  kltAt_zero_of_smooth (ProjVar.Var.topologicalKrullDim_eq _) x

end Checks

end GlobalTheory.Discrepancy

namespace GlobalTheory.Published

open GlobalTheory.Discrepancy

def NadelVanishingPair : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    letI := algebraΓOfHom p
    ∀ (N : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (r : ℕ) (M₀ : LB X),
      N.IsLB → IsEffQDiv Δ → 0 < m → IsLogCanonicalMultiple p n Δ m G →
      0 < r → IsNef ℂ M₀ → IsBig ℂ M₀ →
      (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![N] : ℚ) =
        interNumRed ℂ C ![toLB G] / m + interNumRed ℂ C ![M₀] / r) →
      ∃ J : X.IdealSheafData, (∀ x : X, x ∈ J.support ↔ ¬ KltAt p n Δ x) ∧
        ∀ i, 0 < i → Subsingleton (coh (twist (idealModule J) N) i)

def IsolatedNonKltDivisor : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → 1 ≤ n →
    letI := algebraΓOfHom p
    ∀ (Δ : X → ℚ) (r : ℕ) (N₀ : LB X) (x : X) (c : ℕ → ℝ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < r → IsNef ℂ N₀ → IsBig ℂ N₀ →
      IsClosed ({x} : Set X) → (∀ e ∈ Finset.Icc 1 n, 0 < c e) →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e →
        c e ^ e < (interNumRed ℂ Z fun _ : Fin e => N₀ : ℝ) / (r : ℝ) ^ e) →
      ∑ e ∈ Finset.Icc 1 n, (e : ℝ) / c e ≤ 1 →
      ∃ (m : ℕ) (D₀ : CartierDiv X) (U : X.Opens), 0 < m ∧ D₀.Eff ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C →
          (interNumRed ℂ C ![toLB D₀] : ℚ) / m = interNumRed ℂ C ![N₀] / r) ∧
        x ∈ U ∧ (∀ y ∈ U, LcAt p n (Δ + qWeil D₀ m) y) ∧
        (∀ y ∈ U, y ≠ x → KltAt p n (Δ + qWeil D₀ m) y) ∧ ¬ KltAt p n (Δ + qWeil D₀ m) x

def NadelVanishingAndNonKltDivisor : Prop := NadelVanishingPair ∧ IsolatedNonKltDivisor

theorem NadelVanishingPair.of_smooth (h : NadelVanishingPair) (Y : ProjVar.Var ℂ) (N D M : Y.Dv)
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hD : Y.Eff D) (hM : Y.nef M) (hM' : Y.big M)
    (e : ∀ C, Y.IsCurve C → (Y.deg C N : ℚ) =
      Y.deg C (canonical Y.str Y.dim) + Y.deg C D / m + Y.deg C M / r) :
    ∃ J : Y.X.IdealSheafData, (∀ x, x ∈ J.support ↔ ¬ KltAt Y.str Y.dim (qWeil D m) x) ∧
      ∀ i, 0 < i → Subsingleton (coh (twist (idealModule J) (Y.lb N)) i) := by
  haveI := Y.isNormalScheme
  refine h Y.X Y.str Y.dim Y.isProjOver Y.topologicalKrullDim_eq _ _ m _ r _ (isLB_toLB N)
    (isEffQDiv_qWeil hD m) hm (isLogCanonicalMultiple_canonical Y.topologicalKrullDim_eq D hm) hr
    hM hM' fun C hC => ?_
  have hC' := (Y.isCurve_iff C).2 hC
  have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  change (Y.deg C N : ℚ) = Y.deg C (m • canonical Y.str Y.dim + D) / m + Y.deg C M / r
  rw [e C hC', hC'.deg_add, hC'.deg_nsmul]
  push_cast
  field_simp

end GlobalTheory.Published
