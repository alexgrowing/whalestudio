import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdEqZeroOfUnderEqBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegAtOfForallCoheightOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DominantInducedModelReduction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRatSecOfPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionsFiniteOverIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrallyClosedFiniteDedekindClassFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrescribedValuationDifferenceElementsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerOrderMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreMapsToZeroIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderPositiveAlongFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreOverMaximalCodimOneFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreconnectedFibreAdjacentComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFibreIsPreconnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorSectionNonzeroLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionDegreePositiveOnCurveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointSpecializationCurveStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

set_option autoImplicit false

namespace GlobalTheory.SteinFibre

open GlobalTheory.Cartier

section Ord

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

theorem ord_zpow {f : X.functionField} (hf : f ≠ 0) (z : X) (n : ℤ) :
    Scheme.ord (f ^ n) z = n * Scheme.ord f z := by
  have h1 : Scheme.ord (1 : X.functionField) z = 0 := (unitAt_one z).ord_eq_zero
  induction n using Int.induction_on with
  | zero => simpa using h1
  | succ n ih => rw [zpow_add_one₀ hf, Scheme.ord_mul (zpow_ne_zero _ hf) hf, ih]; ring
  | pred n ih =>
    have h2 := Scheme.ord_mul (x := z) (zpow_ne_zero (-(n : ℤ) - 1) hf) hf
    rw [← zpow_add_one₀ hf, sub_add_cancel, ih] at h2
    linarith

theorem regAt_of_ord_nonneg [GlobalTheory.IsNormalScheme X] {z : X} (hz : Order.coheight z = 1) {f : X.functionField}
    (hf : f ≠ 0) (h : 0 ≤ Scheme.ord f z) : RegAt z f := by
  haveI := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk hz
  rcases ValuationRing.isInteger_or_isInteger (X.presheaf.stalk z) f with h1 | h1
  · exact h1
  obtain ⟨a, ha⟩ := h1
  obtain ⟨U, hzU, s, rfl⟩ := X.presheaf.exists_germ_eq a
  haveI : Nonempty U := ⟨⟨z, hzU⟩⟩
  have e : X.germToFunctionField U s = f⁻¹ := (Scheme.algebraMap_germ_eq_germToFunctionField _ hzU s).symm.trans ha
  have hs : s ≠ 0 := by
    rintro rfl
    rw [map_zero] at e
    exact inv_ne_zero hf e.symm
  have h2 := Scheme.ord_le_smul hzU hs f
  have e2 : s • f = 1 := by
    rw [Algebra.smul_def]
    change X.germToFunctionField U s * f = 1
    rw [e, inv_mul_cancel₀ hf]
  rw [e2, (unitAt_one z).ord_eq_zero] at h2
  exact (GlobalTheory.WeilCartier.unitAt_of_ord_eq_zero hz hf (le_antisymm h2 h)).regAt

end Ord

theorem exists_vertical_curve {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {e : ℕ} (hX : IsArithVar p e)
    {w x : X} {n : ℤ} (hn : n ≠ 0) (hw : (n : Γ(X, ⊤)) ∈ under w) (hwx : w ⤳ x) (hx : IsClosed ({x} : Set X))
    (U : X.Opens) (hwU : w ∈ U) (hxU : x ∉ U) :
    ∃ (Z : Scheme.{0}) (i : Z ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral Z) (κ : Type) (_ : Field κ)
      (_ : Finite κ) (_ : Algebra κ Γ(Z, ⊤)), topologicalKrullDim Z = 1 ∧ (∀ z, w ⤳ i z) ∧ (∃ z, i z = x) ∧
      ∃ z, i z ∈ U := by
  obtain ⟨V, j, _, _, hj⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint w
  have hn0 : (n : Γ(V, ⊤)) = 0 := by
    by_contra h0
    have h1 : genericPoint V ∈ V.basicOpen (n : Γ(V, ⊤)) := by
      refine ((genericPoint_spec V).mem_open_set_iff (V.basicOpen _).isOpen).2 ?_
      have : V.basicOpen (n : Γ(V, ⊤)) ≠ ⊥ := fun h => h0 (eq_zero_of_basicOpen_eq_bot _ h)
      obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 this
      exact ⟨y, trivial, hy⟩
    have h2 := Scheme.preimage_basicOpen j (U := ⊤) (n : Γ(X, ⊤))
    rw [map_intCast] at h2
    have h3 : j (genericPoint V) ∈ X.basicOpen (n : Γ(X, ⊤)) := h2.ge h1
    rw [hj] at h3
    exact (mem_under_iff w _).1 hw ((X.mem_basicOpen (n : Γ(X, ⊤)) w trivial).1 h3)
  have hl0 : ringChar Γ(V, ⊤) ≠ 0 := by
    intro h
    haveI : CharZero Γ(V, ⊤) := (CharP.ringChar_zero_iff_CharZero _).1 h
    exact hn (Int.cast_eq_zero.1 hn0)
  set l := ringChar Γ(V, ⊤) with hl
  haveI : CharP Γ(V, ⊤) l := ringChar.charP _
  haveI : Fact l.Prime := ⟨(CharP.char_is_prime_or_zero Γ(V, ⊤) l).resolve_right hl0⟩
  letI : Algebra (ZMod l) Γ(V, ⊤) := ZMod.algebra _ l
  have := hX.finite
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e1 : strHom (ZMod l) V ≫ spMap (Int.castRingHom (ZMod l)) = j ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom (ZMod l) V ≫ spMap (Int.castRingHom (ZMod l))) := by rw [e1]; infer_instance
  have : IsProper (strHom (ZMod l) V) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod l)))
  obtain ⟨x', rfl⟩ : x ∈ Set.range j :=
    hwx.mem_closed j.isClosedEmbedding.isClosed_range ⟨_, hj⟩
  have hx' : IsClosed ({x'} : Set V) := by
    have := hx.preimage j.continuous
    rwa [← Set.image_singleton, Set.preimage_image_eq _ j.isClosedEmbedding.injective] at this
  obtain ⟨y, hyU, hyx, hyd⟩ := GlobalTheory.T.closed_point_specialization_curve (ZMod l) V (strHom (ZMod l) V) x' (j ⁻¹ᵁ U) hx'
    ⟨genericPoint V, show j _ ∈ U from hj ▸ hwU⟩ hxU
  obtain ⟨Z, i, _, _, hi⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint y
  have hr : Set.range i = closure {y} := by
    have := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at this
    exact this.symm
  refine ⟨Z, i ≫ j, inferInstance, inferInstance, ZMod l, inferInstance, inferInstance,
    (i.appTop.hom.comp (algebraMap (ZMod l) Γ(V, ⊤))).toAlgebra, ?_, fun z => ?_, ?_, genericPoint Z, ?_⟩
  · rw [← GlobalTheory.topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hr, hyd]
  · rw [Scheme.Hom.comp_apply, ← hj]
    exact (genericPoint_specializes _).map j.continuous
  · obtain ⟨z, hz⟩ : x' ∈ Set.range i := hr ▸ specializes_iff_mem_closure.1 hyx
    exact ⟨z, by rw [Scheme.Hom.comp_apply, hz]⟩
  · rw [Scheme.Hom.comp_apply, hi]
    exact hyU

theorem mult_eq_of_meets (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [Ring.DimensionLEOne Γ(X, ⊤)] [Module.Finite ℤ Γ(X, ⊤)]
    (p : X ⟶ Sp (𝓞 F)) (e : ℕ) (hX : IsArithVar p e) [GlobalTheory.IsNormalScheme X]
    (L : HermLB p) (r : L.B.ι → X.functionFieldˣ) (hr : GlobalTheory.Cartier.IsRatSec L.B r)
    (hvert : ∀ z, (L.div hr).mult z ≠ 0 → (p z).asIdeal ≠ ⊥)
    (hdeg : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ]
      [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → topSelfIntersection κ (L.B.pull i) 1 = 0)
    (P : Ideal Γ(X, ⊤)) (t : Γ(X, ⊤)) (ρ : ℚ) (zi zk : X) (hP : P.IsPrime) (hP0 : P ≠ ⊥) (ht0 : t ≠ 0)
    (hle : ∀ z : X, under z = P → Order.coheight z = 1 →
      ((L.div hr).mult z : ℚ) ≤ ρ * Scheme.ord (algebraMap Γ(X, ⊤) X.functionField t) z)
    (hzi : under zi = P) (hci : Order.coheight zi = 1) (hck : Order.coheight zk = 1)
    (heq : ((L.div hr).mult zi : ℚ) = ρ * Scheme.ord (algebraMap Γ(X, ⊤) X.functionField t) zi)
    (hmeet : (closure ({zi} : Set X) ∩ closure {zk}).Nonempty) :
    ((L.div hr).mult zk : ℚ) = ρ * Scheme.ord (algebraMap Γ(X, ⊤) X.functionField t) zk := by
  haveI := hX.isNoetherian
  haveI := hX.finite
  have hPm : P.IsMaximal := hP.isMaximal hP0
  have hinj : Function.Injective (algebraMap Γ(X, ⊤) X.functionField) := X.germToFunctionField_injective ⊤
  set T := algebraMap Γ(X, ⊤) X.functionField t with hT
  have hT0 : T ≠ 0 := (map_ne_zero_iff _ hinj).2 ht0
  let g : L.B.ι → X.functionField := fun a => T ^ ρ.num * (((r a)⁻¹ ^ ρ.den : X.functionFieldˣ) : X.functionField)
  have hg0 : ∀ a, g a ≠ 0 := fun a => mul_ne_zero (zpow_ne_zero _ hT0) (Units.ne_zero _)
  have hord : ∀ a z, z ∈ L.B.U a → (Scheme.ord (g a) z : ℚ) =
      ρ.den * (ρ * Scheme.ord T z - (L.div hr).mult z) := by
    intro a z hz
    have h1 : (L.div hr).mult z = Scheme.ord (r a : X.functionField) z :=
      ((presents_divOfRatSec L.isLB hr).isEqn a z hz).mult_eq
    have h2 : (((r a)⁻¹ ^ ρ.den : X.functionFieldˣ) : X.functionField) = (r a : X.functionField) ^ (-(ρ.den : ℤ)) := by
      rw [zpow_neg, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow]
    simp only [g]
    rw [Scheme.ord_mul (zpow_ne_zero _ hT0) (Units.ne_zero _), h2, ord_zpow hT0, ord_zpow (r a).ne_zero, h1]
    push_cast
    rw [← Rat.mul_den_eq_num ρ]
    ring
  have hden : (0 : ℚ) < ρ.den := Nat.cast_pos.2 ρ.pos
  have hreg : ∀ a x, x ∈ L.B.U a → under x = P → RegAt x (g a) := by
    intro a x hx hxP
    refine GlobalTheory.WeilCartier.regAt_of_forall_coheight_one x _ fun z hzx hz => ?_
    have hzU : z ∈ L.B.U a := hzx.mem_open (L.B.U a).isOpen hx
    refine regAt_of_ord_nonneg hz (hg0 a) ?_
    have h1 := hord a z hzU
    by_cases h0 : under z = ⊥
    · have h2 : (L.div hr).mult z = 0 := by
        by_contra hne
        exact hvert z hne (GlobalTheory.T.generic_fibre_maps_to_zero_ideal F X p e hX z h0)
      rw [h2, hT, ord_eq_zero_of_under_eq_bot z t h0 ht0] at h1
      have : (Scheme.ord (g a) z : ℚ) = 0 := by rw [h1]; simp
      exact_mod_cast this.ge
    · have h2 : under z = P :=
        ((under_isPrime z).isMaximal h0).eq_of_le hP.ne_top (hxP ▸ under_le_of_specializes hzx)
      have h3 := hle z h2 hz
      have : (0 : ℚ) ≤ Scheme.ord (g a) z := by rw [h1]; exact mul_nonneg hden.le (by linarith)
      exact_mod_cast this
  obtain ⟨x, ⟨hxi, hxk⟩, hx⟩ := (isClosed_closure.inter isClosed_closure).exists_closed_singleton hmeet
  have hix : zi ⤳ x := specializes_iff_mem_closure.2 hxi
  have hkx : zk ⤳ x := specializes_iff_mem_closure.2 hxk
  obtain ⟨a, ha⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart L.isLB x
  have hia : zi ∈ L.B.U a := hix.mem_open (L.B.U a).isOpen ha
  have hka : zk ∈ L.B.U a := hkx.mem_open (L.B.U a).isOpen ha
  by_contra hne
  have hnu : ¬ UnitAt x (g a) := by
    intro hu
    obtain ⟨V, hxV, hV⟩ := hu.exists_nhds
    have h1 := hord a zk hka
    rw [(hV zk (hkx.mem_open V.isOpen hxV)).ord_eq_zero] at h1
    have h2 := (mul_eq_zero.1 (h1.symm.trans Int.cast_zero)).resolve_left hden.ne'
    exact hne (by linarith)
  have hui : UnitAt zi (g a) := by
    refine GlobalTheory.WeilCartier.unitAt_of_ord_eq_zero hci (hg0 a) ?_
    have h1 := hord a zi hia
    rw [heq, sub_self, mul_zero] at h1
    exact_mod_cast h1
  obtain ⟨V, hiV, hV⟩ := hui.exists_nhds
  obtain ⟨c, hcP, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  obtain ⟨n, hnP, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem (R := ℤ) hc0 hcP (Algebra.IsIntegral.isIntegral c))
  have hnP' : (n : Γ(X, ⊤)) ∈ under zi := by
    rw [hzi]
    simpa using hnP
  obtain ⟨Z, i, _, _, κ, _, _, _, hd, hZ, ⟨z₀, hz₀⟩, z₁, hz₁⟩ := exists_vertical_curve hX hn0 hnP' hix hx
    (V ⊓ L.B.U a) ⟨hiV, hia⟩ (fun h => hnu (hV x h.1))
  have hZP : ∀ z, under (i z) = P := fun z =>
    (hPm.eq_of_le (under_isPrime _).ne_top (hzi ▸ under_le_of_specializes (hZ z))).symm
  have hr' : IsRatSec L.dual.B fun a => (r a)⁻¹ := by
    intro b b' h
    change genericPoint X ∈ L.B.U b ⊓ L.B.U b' at h
    have h1 := hr b b' h
    have h2 : fnOf (L.B.U b ⊓ L.B.U b') h ((L.B.g b b' : Γ(X, L.B.U b ⊓ L.B.U b'))) *
        fnOf (L.B.U b ⊓ L.B.U b') h (((L.B.g b b')⁻¹ : Γ(X, L.B.U b ⊓ L.B.U b')ˣ) : Γ(X, L.B.U b ⊓ L.B.U b')) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    change (((r b)⁻¹ : X.functionFieldˣ) : X.functionField) =
      fnOf (L.B.U b ⊓ L.B.U b') h (((L.B.g b b')⁻¹ : Γ(X, L.B.U b ⊓ L.B.U b')ˣ) : Γ(X, L.B.U b ⊓ L.B.U b')) *
        (((r b')⁻¹ : X.functionFieldˣ) : X.functionField)
    rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, h1, mul_inv, eq_inv_of_mul_eq_one_right h2]
  have hmem : ∀ (y : X) (J : (L.dual.pow ρ.den).B.ι), y ∈ (L.dual.pow ρ.den).B.U J ↔ y ∈ L.B.U (J PUnit.unit) := by
    intro y J
    exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull (L := L.B) (F := 𝟙 X) (x := y) (J := J)
  obtain ⟨s, hs⟩ := GlobalTheory.T.cartier_divisor_section_nonzero_locus X Z (L.dual.pow ρ.den).B (L.dual.pow ρ.den).isLB _
    (GlobalTheory.TrueGeo.SmallSec.isRatSec_pow hr' ρ.den) (T ^ ρ.num) i
    (fun z J hz => hreg (J PUnit.unit) (i z) ((hmem _ _).1 hz) (hZP z))
  have hpos := GlobalTheory.T.section_degree_positive_on_curve _ X p e hX Z i κ hd _ (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull (L.dual.pow ρ.den).isLB i) s
    ⟨z₁, (hs z₁ (fun _ => a) ((hmem _ _).2 hz₁.2)).2 (hV _ hz₁.1)⟩
    ⟨z₀, fun h => hnu (hz₀ ▸ (hs z₀ (fun _ => a) ((hmem _ _).2 (hz₀ ▸ ha))).1 h)⟩
  rw [GlobalTheory.NefHodgeTateAt.topSelf_pow hX.isProjOver _ _ Z i κ hd,
    GlobalTheory.NefDeRhamCover.topSelf_dual hX.isProjOver _ Z i κ hd, hdeg Z i κ hd] at hpos
  simp at hpos

set_option maxHeartbeats 800000 in

theorem exists_smul_mult_eq_ord : GlobalTheory.CovTop.Hypotheses2 → ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp (𝓞 F)) (e : ℕ),
    IsArithVar p e → IsArithVar (spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤)) 0 → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    ∀ (L : HermLB p) (r : L.B.ι → X.functionFieldˣ) (hr : GlobalTheory.Cartier.IsRatSec L.B r),
    (∀ z, (L.div hr).mult z ≠ 0 → (p z).asIdeal ≠ ⊥) →
    (∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ]
      [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → topSelfIntersection κ (L.B.pull i) 1 = 0) →
    ∃ (m : ℕ) (g : X.functionFieldˣ) (a b : Γ(X, ⊤)), 0 < m ∧ b ≠ 0 ∧
      (g : X.functionField) * algebraMap Γ(X, ⊤) X.functionField b = algebraMap Γ(X, ⊤) X.functionField a ∧
      ∀ z, (m • L.div hr).mult z = Scheme.ord (g : X.functionField) z := by
  intro hPr F _ _ X _ _ p e hX hA hN L r hr hvert hdeg
  classical
  haveI : IsDomain Γ(X, ⊤) := inferInstance
  haveI : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hN
  haveI : IsIntegrallyClosed Γ(X, ⊤) := inferInstance
  haveI : CharZero Γ(X, ⊤) := hX.charZero
  haveI : Module.Finite ℤ Γ(X, ⊤) := GlobalTheory.T.global_sections_finite_over_integers F X p hA
  obtain ⟨hDed, hCl⟩ := GlobalTheory.T.integrally_closed_finite_dedekind_class_finite Γ(X, ⊤)
  have hinj : Function.Injective (algebraMap Γ(X, ⊤) X.functionField) := X.germToFunctionField_injective ⊤
  have hunif : ∀ P : Ideal Γ(X, ⊤), P.IsPrime → P ≠ ⊥ → ∃ π ∈ P, π ∉ P ^ 2 := by
    intro P hP h0
    have hP1 : P ≠ ⊤ := hP.ne_top
    have hlt : P ^ 2 < P ^ 1 := Ideal.pow_right_strictAnti P h0 hP1 (by norm_num)
    rw [pow_one] at hlt
    obtain ⟨π, h1, h2⟩ := SetLike.exists_of_lt hlt
    exact ⟨π, h1, h2⟩
  choose! π hπP hπ2 using hunif
  have hπ0 : ∀ P : Ideal Γ(X, ⊤), P.IsPrime → P ≠ ⊥ → π P ≠ 0 := fun P hP h0 e =>
    hπ2 P hP h0 (e ▸ (P ^ 2).zero_mem)

  haveI := hX.isNoetherian
  have hq : ∀ P : Ideal Γ(X, ⊤), P.IsPrime → P ≠ ⊥ → ∃ q : ℚ, ∀ z : X, under z = P →
      ((L.div hr).mult z : ℚ) = q * Scheme.ord (algebraMap Γ(X, ⊤) X.functionField (π P)) z := by
    intro P hP h0
    have hPm : P.IsMaximal := hP.isMaximal h0
    have ht : π P ∈ P := hπP P hP h0
    have ht0 : π P ≠ 0 := hπ0 P hP h0
    obtain ⟨hZfin, hcov⟩ := GlobalTheory.T.fibre_over_maximal_codim_one_finite X P (π P) hPm ht ht0
    have hoff : ∀ z : X, Order.coheight z ≠ 1 → (L.div hr).mult z = 0 ∧
        Scheme.ord (algebraMap Γ(X, ⊤) X.functionField (π P)) z = 0 := fun z hc =>
      ⟨by_contra fun h => hc (GlobalTheory.Cartier.CartierDiv.coheight_eq_one_of_mult_ne_zero h),
        Scheme.ord_eq_zero_of_coheight_neq_one hc _⟩
    have hpos : ∀ z : X, under z = P → Order.coheight z = 1 →
        0 < Scheme.ord (algebraMap Γ(X, ⊤) X.functionField (π P)) z :=
      fun z hz hc => GlobalTheory.T.order_positive_along_fibre X z (π P) (hz ▸ ht) ht0 hc
    by_cases hne : {z : X | under z = P ∧ Order.coheight z = 1}.Nonempty
    swap
    · refine ⟨0, fun z hz => ?_⟩
      have hc : Order.coheight z ≠ 1 := fun h => hne ⟨z, hz, h⟩
      simp [(hoff z hc).1]
    obtain ⟨zi, hzi, hmax⟩ := hZfin.toFinset.exists_max_image
      (fun z => ((L.div hr).mult z : ℚ) / Scheme.ord (algebraMap Γ(X, ⊤) X.functionField (π P)) z)
      (by simpa using hne)
    rw [Set.Finite.mem_toFinset] at hzi
    set ρ0 : ℚ := ((L.div hr).mult zi : ℚ) / Scheme.ord (algebraMap Γ(X, ⊤) X.functionField (π P)) zi
      with hρ0
    have hle : ∀ z : X, under z = P → Order.coheight z = 1 →
        ((L.div hr).mult z : ℚ) ≤ ρ0 * Scheme.ord (algebraMap Γ(X, ⊤) X.functionField (π P)) z := by
      intro z hz hc
      have h1 := hmax z ((Set.Finite.mem_toFinset _).2 ⟨hz, hc⟩)
      have h2 : (0 : ℚ) < Scheme.ord (algebraMap Γ(X, ⊤) X.functionField (π P)) z := by
        exact_mod_cast hpos z hz hc
      rwa [div_le_iff₀ h2] at h1
    have hzi0 : ((L.div hr).mult zi : ℚ) = ρ0 * Scheme.ord (algebraMap Γ(X, ⊤) X.functionField (π P)) zi := by
      have h2 : (Scheme.ord (algebraMap Γ(X, ⊤) X.functionField (π P)) zi : ℚ) ≠ 0 := by
        exact_mod_cast (hpos zi hzi.1 hzi.2).ne'
      rw [hρ0, div_mul_cancel₀ _ h2]
    refine ⟨ρ0, fun z hz => ?_⟩
    by_cases hc : Order.coheight z = 1
    swap
    · simp [(hoff z hc).1, (hoff z hc).2]
    by_contra hneq
    have hsub : ∀ w ∈ hZfin.toFinset, closure {w} ⊆ {x : X | under x = P} := by
      intro w hw y hy
      rw [Set.Finite.mem_toFinset] at hw
      have h1 := under_le_of_specializes (specializes_iff_mem_closure.2 hy)
      rw [hw.1] at h1
      exact (hPm.eq_of_le (under_isPrime y).ne_top h1).symm
    obtain ⟨i, hi, k, hk, hi0, hk0, hik⟩ := GlobalTheory.T.preconnected_fibre_adjacent_components X {x : X | under x = P} hZfin.toFinset
      (fun w => ρ0 * Scheme.ord (algebraMap Γ(X, ⊤) X.functionField (π P)) w - (L.div hr).mult w)
      (GlobalTheory.T.stein_fibre_isPreconnected hPr F X p e hX hA P) hsub
      (fun x hx => by
        obtain ⟨w, hw1, hw2, hw3⟩ := hcov x hx
        exact ⟨w, (Set.Finite.mem_toFinset _).2 ⟨hw1, hw2⟩, specializes_iff_mem_closure.1 hw3⟩)
      (fun w hw => by
        rw [Set.Finite.mem_toFinset] at hw
        have := hle w hw.1 hw.2
        linarith)
      ⟨zi, (Set.Finite.mem_toFinset _).2 hzi, by rw [hzi0]; ring⟩
      ⟨z, (Set.Finite.mem_toFinset _).2 ⟨hz, hc⟩, by
        have := hle z hz hc
        exact lt_of_le_of_ne (by linarith) (fun h => hneq (by linarith))⟩
    rw [Set.Finite.mem_toFinset] at hi hk
    have := mult_eq_of_meets F X p e hX L r hr hvert hdeg P (π P) ρ0 i k hP h0 ht0 hle hi.1 hi.2 hk.2
      (by linarith) hik
    linarith
  choose! q hq using hq
  have hfin : (Function.support (L.div hr).mult).Finite := (L.div hr).finite_support_mult
  obtain ⟨m, a, b, hm, ha0, hb0, hab⟩ := GlobalTheory.T.prescribed_valuation_difference_elements Γ(X, ⊤) (hfin.toFinset.image under) q
  have hb' : algebraMap Γ(X, ⊤) X.functionField b ≠ 0 := (map_ne_zero_iff _ hinj).2 hb0
  have ha' : algebraMap Γ(X, ⊤) X.functionField a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha0
  let g : X.functionFieldˣ := Units.mk0 (algebraMap Γ(X, ⊤) X.functionField a /
    algebraMap Γ(X, ⊤) X.functionField b) (div_ne_zero ha' hb')
  refine ⟨m, g, a, b, hm, hb0, ?_, fun z => ?_⟩
  · simp only [g, Units.val_mk0]
    field_simp
  have hga : (g : X.functionField) * algebraMap Γ(X, ⊤) X.functionField b =
      algebraMap Γ(X, ⊤) X.functionField a := by
    simp only [g, Units.val_mk0]
    field_simp
  have hord : Scheme.ord (g : X.functionField) z = Scheme.ord (algebraMap Γ(X, ⊤) X.functionField a) z -
      Scheme.ord (algebraMap Γ(X, ⊤) X.functionField b) z := by
    have := Scheme.ord_mul (x := z) g.ne_zero hb'
    rw [hga] at this
    omega
  rw [GlobalTheory.SmallSecHeight.mult_nsmul, hord]
  by_cases hz : under z = ⊥
  · have h1 : (L.div hr).mult z = 0 := by
      by_contra hne
      exact hvert z hne (GlobalTheory.T.generic_fibre_maps_to_zero_ideal F X p e hX z hz)
    rw [h1, ord_eq_zero_of_under_eq_bot z a hz ha0, ord_eq_zero_of_under_eq_bot z b hz hb0]
    simp
  · set P := under z with hPdef
    have hP : P.IsPrime := under_isPrime z
    obtain ⟨na, nb, ha1, ha2, hb1, hb2, hn⟩ := hab P hP hz
    rw [GlobalTheory.T.uniformizer_order_multiplicative X z P (π P) a na hP hz rfl (hπP P hP hz) (hπ2 P hP hz) ha1 ha2,
      GlobalTheory.T.uniformizer_order_multiplicative X z P (π P) b nb hP hz rfl (hπP P hP hz) (hπ2 P hP hz) hb1 hb2]
    have key := hq P hP hz z rfl
    by_cases hS : P ∈ hfin.toFinset.image under
    · rw [if_pos hS] at hn
      have : ((m : ℤ) * (L.div hr).mult z : ℚ) = (((na : ℤ) * Scheme.ord (algebraMap Γ(X, ⊤) X.functionField (π P)) z
          - (nb : ℤ) * Scheme.ord (algebraMap Γ(X, ⊤) X.functionField (π P)) z : ℤ) : ℚ) := by
        push_cast
        rw [key]
        have : ((na : ℚ) - nb) * Scheme.ord (algebraMap Γ(X, ⊤) X.functionField (π P)) z =
          (m : ℚ) * q P * Scheme.ord (algebraMap Γ(X, ⊤) X.functionField (π P)) z := by rw [hn]
        linear_combination -this
      exact_mod_cast this
    · rw [if_neg hS, mul_zero, sub_eq_zero] at hn
      have hn' : na = nb := by exact_mod_cast hn
      have h1 : (L.div hr).mult z = 0 := by
        by_contra hne
        exact hS (Finset.mem_image.2 ⟨z, hfin.mem_toFinset.2 hne, rfl⟩)
      rw [h1, hn']
      simp

end GlobalTheory.SteinFibre
