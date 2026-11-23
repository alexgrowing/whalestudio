import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingClassHost
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmConjugationOmega
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteResidueField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCyclotomicUnramifiedCompletedIntegersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardPadicAlgClPadicComplexEqComplexStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivAlgClosedOverNumberFieldCompEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiniteExtPadicRingOfIntegersIffNormLeOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaximalIdealIffNormLtOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivFinExtIntegersPadicIntOfStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegersToCompletedUnramifiedCompositumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePrimitiveRootStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedHeckeCharIdeleValueUniformiserStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaTildeIsUnitArgAtCmTypePlacesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockValAeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientFieldLowerBoundsStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.TwRing

open GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

theorem clC_mono (l : ℕ) [Fact l.Prime] {F F' : IntermediateField ℚ_[l] (PadicAlgCl l)} (h : F ≤ F') :
    clC l F ≤ clC l F' :=
  inf_le_inf_right _ (Subring.topologicalClosure_mono fun _ ⟨y, hy, e⟩ => ⟨y, h hy, e⟩)

theorem exists_prime_mem (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    ∃ l : ℕ, l.Prime ∧ ((l : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 K ⧸ w.asIdeal)
  haveI := hp
  exact ⟨p, CharP.char_is_prime (𝓞 K ⧸ w.asIdeal) p,
    Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_natCast]; exact CharP.cast_eq_zero _ p)⟩

theorem placesOver_nonempty (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    (placesOver E p).Nonempty := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 E) := by
    intro hu
    have h1 := hu.map (Algebra.norm ℤ : 𝓞 E →* ℤ)
    rw [show ((p : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) by simp, Algebra.norm_algebraMap] at h1
    have h2 := Int.isUnit_iff_natAbs_eq.1 h1
    have h3 : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h2
    rcases Nat.pow_eq_one.1 h2 with h | h
    · exact hp.one_lt.ne' h
    · exact h3.ne' h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 E)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : ((p : ℕ) : 𝓞 E) ∈ M := hle (Ideal.subset_span rfl)
  refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, hmem⟩
  rw [h, Ideal.mem_bot] at hmem
  exact hp.ne_zero (by exact_mod_cast hmem)

theorem exists_ringEquiv_over (K Ω₁ Ω₂ : Type) [Field K] [NumberField K] [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁]
    [IsAlgClosed Ω₂] [CharZero Ω₁] [CharZero Ω₂] (a : K →+* Ω₁) (b : K →+* Ω₂)
    (hc : Cardinal.mk Ω₁ = Cardinal.mk Ω₂) (hu : Cardinal.aleph0 < Cardinal.mk Ω₁) :
    ∃ ι : Ω₁ ≃+* Ω₂, ∀ x, ι (a x) = b x :=
  GlobalTheory.T.exists_ringEquiv_algClosed_over_numberField_comp_eq K Ω₁ Ω₂ a b hc hu

theorem card_padicAlgCl (l : ℕ) [Fact l.Prime] : Cardinal.mk (PadicAlgCl l) = Cardinal.mk ℂ :=
  (GlobalTheory.T.card_padicAlgCl_padicComplex_eq_complex l).1

theorem card_padicComplex (l : ℕ) [Fact l.Prime] : Cardinal.mk ℂ_[l] = Cardinal.mk ℂ :=
  (GlobalTheory.T.card_padicAlgCl_padicComplex_eq_complex l).2

theorem mem_OL_iff (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) (x : ↥K.1) :
    x ∈ Loc.OL K ↔ ‖(x : PadicAlgCl l)‖ ≤ 1 :=
  GlobalTheory.T.mem_finiteExtPadic_ringOfIntegers_iff_norm_le_one l K x

theorem mem_maximalIdeal_OL_iff (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) [IsLocalRing ↥(Loc.OL K)]
    (y : ↥(Loc.OL K)) : y ∈ IsLocalRing.maximalIdeal ↥(Loc.OL K) ↔ ‖((y : ↥K.1) : PadicAlgCl l)‖ < 1 :=
  GlobalTheory.T.mem_maximalIdeal_OL_iff_norm_lt_one l K y

theorem exists_equiv_intOf (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) :
    ∃ e : ↥(Loc.OL K) ≃+* ↥(intOf l K.1), ∀ y, (e y : PadicAlgCl l) = ((y : ↥K.1) : PadicAlgCl l) :=
  GlobalTheory.T.exists_ringEquiv_finExtIntegers_padicIntOf l K

theorem exists_toClC (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) :
    ∃ f : ↥(Loc.OL K₀) →+* ↥(clC l (Kt l K₀ L)),
      ∀ y, (f y : ℂ_[l]) = algebraMap (PadicAlgCl l) ℂ_[l] ((y : ↥K₀.1) : PadicAlgCl l) :=
  GlobalTheory.T.exists_integers_to_completedUnramifiedCompositum l K₀ L

theorem ok_laws (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (k : ℕ) :
    letI := (Subring.inclusion (clC_mono l (le_sup_left : Kt l K₀ L ≤ Kt l K₀ L ⊔ muK l k))).toAlgebra
    Module.Finite ↥(clC l (Kt l K₀ L)) ↥(clC l (Kt l K₀ L ⊔ muK l k)) ∧
      ∃ z : (↥(clC l (Kt l K₀ L ⊔ muK l k)))ˣ, IsPrimitiveRoot (z : ↥(clC l (Kt l K₀ L ⊔ muK l k))) (l ^ k) ∧
        ∀ x : FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k)), ∃ p : Polynomial ↥(clC l (Kt l K₀ L)),
          ∃ d : ↥(clC l (Kt l K₀ L)), d ≠ 0 ∧
          x * algebraMap _ (FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k))) (algebraMap _ ↥(clC l (Kt l K₀ L ⊔ muK l k)) d) =
            algebraMap _ (FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k))) (Polynomial.aeval (z : ↥(clC l (Kt l K₀ L ⊔ muK l k))) p) :=
  GlobalTheory.T.finite_primitive_root_of_clC_le l K₀ L k _

theorem hc_at {E : Type} [Field E] [NumberField E] (χ : HChar E) (h : Formalism.L2.NC.HC E)
    (hh : h.χ = (χ : Ideles E →* ℂˣ)) (v : HeightOneSpectrum (𝓞 E)) :
    (χ.UnrAt v → h.At v (χ.val v)) ∧ (χ.UnrAt v ↔ h.Unr v) :=
  GlobalTheory.T.unramifiedHeckeChar_idele_value_uniformiser χ h hh v

end GlobalTheory.TwRing

namespace GlobalTheory.TwRing
open GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

theorem placesOver_inj (E : Type) [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : placesOver E p = placesOver E q) : p = q := by
  by_contra hne
  obtain ⟨v, hv⟩ := placesOver_nonempty E p hp
  have hv' : v ∈ placesOver E q := h ▸ hv
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * p + b * q = 1 := ⟨Nat.gcdA p q, Nat.gcdB p q, by
    have := Nat.gcd_eq_gcd_ab p q; rw [hc] at this; push_cast at this; linarith⟩
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have : ((a : 𝓞 E) * (p : 𝓞 E) + (b : 𝓞 E) * (q : 𝓞 E)) = 1 := by exact_mod_cast congrArg (Int.cast (R := 𝓞 E)) hab
  rw [← this]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hv')

theorem eta_unitArg {R : Ranks} (H : Host R) (χ : HChar H.E) (hχ : IsEtaT H χ) (h : Formalism.L2.NC.HC H.E)
    (hh : h.χ = (χ : Ideles H.E →* ℂˣ)) (g : R.Psi) :
    h.IsUnitArg (H.emb (g : R.GG)) :=
  GlobalTheory.T.etaTilde_isUnitArg_at_cmType_places H χ hχ h hh g

theorem vals_block {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (ε : K →+* ℂ) (μ η : HChar E)
    (hμ : AlmostIn ε μ) (hη : η.ValuesIn (1 / 2) ε) {r : ℕ} (hr : Odd r) (μH ηH : Formalism.L2.NC.HC E)
    (hμH : μH.χ = (μ : Ideles E →* ℂˣ)) (hηH : ηH.χ = (η : Ideles E →* ℂˣ)) :
    ∀ᶠ v in Filter.cofinite, (μH * ηH⁻¹).At v ((((block μ η r).val v : ℂˣ) : ℂ) *
      (Real.sqrt (normV v) : ℂ) ^ (-(r : ℤ))) ∧
      ∃ y : K, ε y = (((block μ η r).val v : ℂˣ) : ℂ)⁻¹ :=
  GlobalTheory.T.eventually_block_val_at_and_exists_inv_eq ε μ η hμ hη hr μH ηH hμH hηH

theorem vals_zero {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (ε : K →+* ℂ) (χ : HChar E)
    (hv : χ.ValuesIn 0 ε) (χH : Formalism.L2.NC.HC E) (hH : χH.χ = (χ : Ideles E →* ℂˣ)) :
    ∀ᶠ v in Filter.cofinite, χH.At v (((χ.val v : ℂˣ) : ℂ) * (Real.sqrt (normV v) : ℂ) ^ (0 : ℤ)) ∧
      ∃ y : K, ε y = ((χ.val v : ℂˣ) : ℂ)⁻¹ := by
  filter_upwards [unr_ae χ] with v hu
  refine ⟨by simpa using (hc_at χ χH hH v).1 hu, ?_⟩
  obtain ⟨y, hy⟩ := hv v hu
  exact ⟨y⁻¹, by rw [map_inv₀, hy]; simp [HChar.valTw]⟩

theorem frob_read {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
    {O : Type} [CommRing O] [IsDomain O] [TopologicalSpace O] {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art)
    {κ : FractionRing O →+* Qbar l} {ι : Qbar l ≃+* ℂ} {χ : HChar E} {n : (E →+* ℂ) → ℤ} {r : G E Ω →* Oˣ}
    (h : IsGal art κ ι χ n r) {L : Type} [Field L] (eL : L →+* FractionRing O) (embC : L →+* ℂ)
    (hL : ∀ x, ι (κ (eL x)) = embC x) {v : HeightOneSpectrum (𝓞 E)} (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∨ n = 0)
    (hu : χ.UnrAt v) {A : ValuationSubring Ω} (hA : IsPlaceOver A v) {σ : G E Ω}
    (hσ : IsFrob (F := E) A (normV v) σ) {y : L} (hy : embC y = ((χ.val v : ℂˣ) : ℂ)⁻¹) :
    algebraMap O (FractionRing O) (r σ : O) = eL y := by
  apply κ.injective
  apply ι.injective
  rw [hL, hy]
  exact h.frob ha hv hu hA hσ

theorem read_of_isGal {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
    {O : Type} [CommRing O] [IsDomain O] [TopologicalSpace O] {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art)
    {κ : FractionRing O →+* Qbar l} {ι : Qbar l ≃+* ℂ} {χ : HChar E} {n : (E →+* ℂ) → ℤ} {r : G E Ω →* Oˣ}
    (h : IsGal art κ ι χ n r) (pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω) (hpl : ∀ P, IsPlaceOver (pl P) P)
    {L : Type} [Field L] (eL : L →+* FractionRing O) (embC : L →+* ℂ) (hL : ∀ x, ι (κ (eL x)) = embC x)
    (χH : Formalism.L2.NC.HC E) (w : ℤ)
    (hχ : ∀ᶠ v in Filter.cofinite, χH.At v (((χ.val v : ℂˣ) : ℂ) * (Real.sqrt (normV v) : ℂ) ^ w) ∧
      ∃ y : L, embC y = ((χ.val v : ℂˣ) : ℂ)⁻¹) :
    Formalism.L2.NC.Read pl r (algebraMap O (FractionRing O)) eL embC χH w := by
  have hall := hχ.and ((unr_ae χ).and (away_ae (E := E) l (Fact.out : l.Prime).ne_zero))
  refine ⟨(Filter.eventually_cofinite.1 hall).toFinset, fun P hP => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hP
  obtain ⟨⟨hAt, y, hy⟩, hu, hl⟩ := hP
  refine ⟨_, hAt, y, ?_, fun σ hσ => frob_read ha h eL embC hL (Or.inl hl) hu (hpl P) hσ hy⟩
  have h0 : (Real.sqrt (normV P) : ℂ) ≠ 0 := by
    have := Formalism.L2.NC.normV_ne_zero P
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero this)).ne'
  rw [mul_inv, mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ h0), mul_one, hy]

end GlobalTheory.TwRing

namespace GlobalTheory.TwRing
open GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

theorem exists_padicBaseField_integral_places (D : D7) : ∃ c0 : Big D, ∀ (l : ℕ) [Fact l.Prime] (j : ↥D.LL0 →+* PadicAlgCl l),
    (∀ x, j x ∈ (c0 l j).1) ∧ muK l 1 ≤ (c0 l j).1 ∧
    ∀ K0 : Loc.FinExt l, (c0 l j).1 ≤ K0.1 → ∀ w ∈ placesOver D.host.E l,
      ∃ Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) ↥(Loc.OL K0),
        ∀ x, x ∈ D.nd.plOm.1 w ↔ ‖Bw.j x‖ ≤ 1 :=
  GlobalTheory.T.exists_coefficientField_lower_bounds D

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_ringSpec (hA : GlobalTheory.Published.GlobalArtinReciprocity) : ∀ (D : D7) (cf : CharFrame D) (J : ∀ (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 ↥D.LL0)), ((l : ℕ) : 𝓞 ↥D.LL0) ∈ w.asIdeal → (↥D.LL0 →+* PadicAlgCl l)), (∀ (l : ℕ) [Fact l.Prime] w h (x : 𝓞 ↥D.LL0), x ∈ w.asIdeal ↔ ‖J l w h x‖ < 1) → ValLL0 D cf → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → ∃ c0 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)), (∀ (l : ℕ) [Fact l.Prime] j, (c0 l j).1 ≤ (b0 l j).1) → ∃ (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T), ∀ i, Sp.j0 i = J (T.l i) (Sp.eTw i) (Sp.pl_emb i).1 ∧ Sp.K0 i = b0 (T.l i) (Sp.j0 i) ∧ Sp.Lw i = b1 (T.l i) (Sp.j0 i) := by
  intro D cf J hJ hV hstar hE
  obtain ⟨c0, hc0⟩ := exists_padicBaseField_integral_places D
  refine ⟨c0, fun b0 b1 Sx hb => ?_⟩
  choose lw hlw using fun w : HeightOneSpectrum (𝓞 ↥D.LL0) => exists_prime_mem ↥D.LL0 w
  haveI hF : ∀ w, Fact (lw w).Prime := fun w => ⟨(hlw w).1⟩
  set j0 : ∀ w, ↥D.LL0 →+* PadicAlgCl (lw w) := fun w => J (lw w) w (hlw w).2 with hj0
  set K0 : ∀ w, Loc.FinExt (lw w) := fun w => b0 (lw w) (j0 w) with hK0
  set Lw : ∀ w, Loc.FinExt (lw w) := fun w => b1 (lw w) (j0 w) with hLw
  have hco := fun w => GlobalTheory.CoefInt.integers_laws (lw w) (K0 w)
  haveI hdvr0 : ∀ w, IsDiscreteValuationRing ↥(Loc.OL (K0 w)) := fun w => (hco w).fst
  haveI hfin0 : ∀ w, Module.Finite ℤ_[lw w] ↥(Loc.OL (K0 w)) := fun w => (hco w).snd.1
  haveI hfr0 : ∀ w, IsFractionRing ↥(Loc.OL (K0 w)) ↥(K0 w).1 := fun w => (hco w).snd.2.2.2.2
  have hclc := fun w k => GlobalTheory.T.exists_cyclotomic_unramified_completed_integers (lw w) (K0 w) (Lw w) k
  have hmu0 : ∀ w, muK (lw w) 0 = ⊥ := fun w => (hclc w 0).snd.2.2.2.2.1
  have hkt : ∀ w, Kt (lw w) (K0 w) (Lw w) ⊔ muK (lw w) 0 = Kt (lw w) (K0 w) (Lw w) := fun w => by
    rw [hmu0 w, sup_bot_eq]
  have hclc0 := fun w => hkt w ▸ hclc w 0
  haveI hdvrO : ∀ w, IsDiscreteValuationRing ↥(clC (lw w) (Kt (lw w) (K0 w) (Lw w))) := fun w => (hclc0 w).fst
  haveI hdvrOk : ∀ w k, IsDiscreteValuationRing ↥(clC (lw w) (Kt (lw w) (K0 w) (Lw w) ⊔ muK (lw w) k)) :=
    fun w k => (hclc w k).fst
  choose toO htoO using fun w => exists_toClC (lw w) (K0 w) (Lw w)
  choose cc hcc using GlobalTheory.MemN.exists_isCMConjOm_nData D.R D.host D.what₂ D.nd

  obtain ⟨art, ha⟩ := hA D.host.E D.nd.Om
  let C : GlobalTheory.Mem.Chr.HFrame D.host (fun j => eExp D j) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  have hGal := galois_characters_of_artin D.R D.host D.nd.Om cc hcc (fun j => eExp D j) hE C D.nd.g_split art ha
  have hTw := hGal.1

  let φ : ∀ w, FractionRing ↥(Loc.OL (K0 w)) ≃ₐ[↥(Loc.OL (K0 w))] ↥(K0 w).1 := fun w =>
    IsLocalization.algEquiv (nonZeroDivisors ↥(Loc.OL (K0 w))) (FractionRing ↥(Loc.OL (K0 w))) ↥(K0 w).1
  have hj0K : ∀ w x, j0 w x ∈ (K0 w).1 := fun w x => hb (lw w) (j0 w) ((hc0 (lw w) (j0 w)).1 x)
  let jK : ∀ w, ↥D.LL0 →+* ↥(K0 w).1 := fun w => (j0 w).codRestrict (K0 w).1 (hj0K w)
  let κ : ∀ w, FractionRing ↥(Loc.OL (K0 w)) →+* PadicAlgCl (lw w) := fun w =>
    ((K0 w).1.val.toRingHom).comp (φ w).toRingEquiv.toRingHom
  let emb0 : ∀ w, ↥D.LL0 →+* FractionRing ↥(Loc.OL (K0 w)) := fun w => (φ w).symm.toRingEquiv.toRingHom.comp (jK w)
  let st : ↥D.LL0 → ↥D.LL0 := fun x => ⟨star (x : D.what₂.LL), hstar x⟩
  let stH : ↥D.LL0 →+* ↥D.LL0 :=
    { toFun := st
      map_one' := Subtype.ext (by simp [st])
      map_mul' := fun x y => Subtype.ext (by simp [st, star_mul'])
      map_zero' := Subtype.ext (by simp [st])
      map_add' := fun x y => Subtype.ext (by simp [st]) }
  let emb0b : ∀ w, ↥D.LL0 →+* FractionRing ↥(Loc.OL (K0 w)) := fun w => (emb0 w).comp stH
  have hκemb : ∀ w x, κ w (emb0 w x) = j0 w x := fun w x => by
    simp [κ, emb0, jK]
  have hcard : ∀ w, Cardinal.aleph0 < Cardinal.mk (PadicAlgCl (lw w)) := fun w => by
    rw [card_padicAlgCl, Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  choose ι hι using fun w => exists_ringEquiv_over ↥D.LL0 (PadicAlgCl (lw w)) ℂ (j0 w) (embLL0 D)
    ((card_padicAlgCl (lw w))) (hcard w)
  have hf : ∀ w x, ι w (κ w (emb0 w x)) = embLL0 D x := fun w x => by rw [hκemb, hι]
  have hf' : ∀ w x, ι w (κ w (emb0b w x)) = starRingEnd ℂ (embLL0 D x) := fun w x => by
    show ι w (κ w (emb0 w (st x))) = _
    rw [hf]
    exact D.starLL_cx (x : D.what₂.LL)
  have hκ : ∀ w (z : ℤ_[lw w]), κ w (algebraMap ↥(Loc.OL (K0 w)) (FractionRing ↥(Loc.OL (K0 w)))
      (algebraMap ℤ_[lw w] ↥(Loc.OL (K0 w)) z)) = algebraMap ℚ_[lw w] (PadicAlgCl (lw w)) (z : ℚ_[lw w]) := fun w z => by
    simp [κ, φ]
    rfl
  have hdel : ∀ w, (delAt D.host C (lw w)).ValuesIn 0 (embLL0 D) := fun w => by
    show (if lw w = D.host.pde then cf.del' else cf.del).ValuesIn 0 (embLL0 D)
    split_ifs
    · exact hV.del'
    · exact hV.del
  have hchar := fun w => hTw (lw w) ↥(Loc.OL (K0 w)) (hco w).snd.2.1 (κ w) (hκ w) (ι w) ↥D.LL0 (embLL0 D) (emb0 w) (emb0b w)
    (hf w) (hf' w) hV.mu0 hV.eta (hdel w) (pDC D.host (lw w)) (coe_pDC D.host (lw w))
  choose delta chi1 hdc using hchar

  choose RCG hgrp hfint art' res hRCG using GlobalTheory.RingCls.exists_ringClass_host hA D.R D.host D.what₂ D.nd cc
    (HeightOneSpectrum (𝓞 ↥D.LL0)) lw
  have hS0fin : ∀ w, ((placesOver D.host.E (lw w) ∪ (⋃ k, placesOver D.host.E (D.host.g k)) ∪
      placesOver D.host.E D.host.pde ∪ placesOver D.host.E D.host.pde') ∪ ↑Sx).Finite := fun w =>
    ((((placesOver_finite' D.host.E (lw w) (hF w).out.ne_zero).union (Set.finite_iUnion fun k =>
      placesOver_finite' D.host.E (D.host.g k) (D.host.g_prime k).ne_zero)).union
      (placesOver_finite' D.host.E D.host.pde D.host.pde_prime.ne_zero)).union
      (placesOver_finite' D.host.E D.host.pde' D.host.pde'_prime.ne_zero)).union Sx.finite_toSet
  let S0 : ∀ w, Finset (HeightOneSpectrum (𝓞 D.host.E)) := fun w => (hS0fin w).toFinset
  choose hOkfin zk hzk hOkgen using fun w k => ok_laws (lw w) (K0 w) (Lw w) k
  let T : TwR D.LL0 D.nd :=
    { cc := cc
      cc_cm := hcc
      Tw := HeightOneSpectrum (𝓞 ↥D.LL0)
      l := lw
      lPrime := hF
      O0 := fun w => ↥(Loc.OL (K0 w))
      crO0 := fun w => inferInstance
      twistBaseCoefficientRing_isDomain := fun w => inferInstance
      twistBaseCoefficientRing_isDVR := hdvr0
      algO0 := fun w => inferInstance
      twistBaseCoefficientRing_finite_padic := hfin0
      twistBaseCoefficientRing_residueField_finite := fun w => (hco w).snd.2.2.2.1
      topO0 := fun w => inferInstance
      twistBaseCoefficientRing_topologicalRing := fun w => inferInstance
      twistBaseCoefficientRing_isAdic := fun w => (hco w).snd.2.1
      emb0 := emb0
      emb0b := emb0b
      restX_coefficientEmbedding_conj := fun w x y h => by
        show emb0 w (st x) = emb0 w y
        congr 1
        exact Subtype.ext h.symm
      O := fun w => ↥(clC (lw w) (Kt (lw w) (K0 w) (Lw w)))
      crO := fun w => inferInstance
      domO := fun w => inferInstance
      dvrO := hdvrO
      algO := fun w => (toO w).toAlgebra
      O_inj := fun w y y' h => by
        have h1 : ((toO w y : ℂ_[lw w])) = (toO w y' : ℂ_[lw w]) := congrArg Subtype.val h
        rw [htoO, htoO] at h1
        exact Subtype.ext (Subtype.ext ((algebraMap (PadicAlgCl (lw w)) ℂ_[lw w]).injective h1))
      O_l := fun w => by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        rintro ⟨u, hu⟩
        have h1 : ((u⁻¹ : (↥(clC (lw w) (Kt (lw w) (K0 w) (Lw w))))ˣ) : ↥(clC (lw w) (Kt (lw w) (K0 w) (Lw w)))) *
            ((lw w : ℕ) : ↥(clC (lw w) (Kt (lw w) (K0 w) (Lw w)))) = 1 := by rw [← hu]; exact u.inv_mul
        have h2 := congrArg (fun z : ↥(clC (lw w) (Kt (lw w) (K0 w) (Lw w))) => ‖(z : ℂ_[lw w])‖) h1
        simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one, norm_mul, norm_one] at h2
        have hu1 : ‖(((u⁻¹ : (↥(clC (lw w) (Kt (lw w) (K0 w) (Lw w))))ˣ) : ↥(clC (lw w) (Kt (lw w) (K0 w) (Lw w)))) : ℂ_[lw w])‖ ≤ 1 := by
          have hm := ((u⁻¹ : (↥(clC (lw w) (Kt (lw w) (K0 w) (Lw w))))ˣ) : ↥(clC (lw w) (Kt (lw w) (K0 w) (Lw w)))).2.2
          change _ ∈ PadicComplexInt (lw w) at hm
          rw [PadicComplexInt, Valuation.mem_valuationSubring_iff] at hm
          rw [PadicComplex.norm_eq_norm]
          exact (Valued.toNormedField.norm_le_one_iff).2 hm
        have hl1 : ‖((lw w : ℕ) : ℂ_[lw w])‖ < 1 := by
          rw [← map_natCast (algebraMap ℚ_[lw w] ℂ_[lw w]), norm_algebraMap']
          exact Padic.norm_p_lt_one
        nlinarith [norm_nonneg (((u⁻¹ : (↥(clC (lw w) (Kt (lw w) (K0 w) (Lw w))))ˣ) : ↥(clC (lw w) (Kt (lw w) (K0 w) (Lw w)))) : ℂ_[lw w]), norm_nonneg ((lw w : ℕ) : ℂ_[lw w])]
      topO := fun w => inferInstance
      trO := fun w => inferInstance
      O_adic := fun w => (hclc0 w).snd.2.2.1
      resO_ac := fun w => (hclc0 w).snd.1
      O_complete := fun w => (hclc0 w).snd.2.1
      Ok := fun w k => ↥(clC (lw w) (Kt (lw w) (K0 w) (Lw w) ⊔ muK (lw w) k))
      crOk := fun w k => inferInstance
      domOk := fun w k => inferInstance
      dvrOk := hdvrOk
      algOk := fun w k => (Subring.inclusion (clC_mono (lw w) (le_sup_left : Kt (lw w) (K0 w) (Lw w) ≤ Kt (lw w) (K0 w) (Lw w) ⊔ muK (lw w) k))).toAlgebra
      Ok_inj := fun w k => Subring.inclusion_injective _
      Ok_fin := hOkfin
      zk := zk
      zk_prim := hzk
      Ok_gen := hOkgen
      pD := fun w => pDC D.host (lw w)
      pD_eq := fun w => coe_pDC D.host (lw w)
      delta := delta
      delta_open := fun w => (hdc w).2.2.1
      delta_anti := fun w => (hdc w).2.2.2.1
      delta_ram := fun w => (hdc w).2.2.2.2.1
      delta_15 := fun w => (hdc w).2.2.2.2.2.1
      delta_tame := fun w => (hdc w).2.2.2.2.2.2.1
      chi1 := chi1
      twistCharacterFamily_continuous := fun w => (hdc w).2.2.2.2.2.2.2.1
      twistCharacterFamily_unramified := fun w => (hdc w).2.2.2.2.2.2.2.2.1
      twistCharacterFamily_at_auxiliaryPlaces := fun w => (hdc w).2.2.2.2.2.2.2.2.2.1
      twistCharacterFamily_tame := fun w => (hdc w).2.2.2.2.2.2.2.2.2.2
      S0 := S0
      twistExcludedPlaces_contains_residueChar := fun w v hv => by
        show v ∈ ((hS0fin w).toFinset : Set _)
        rw [Set.Finite.coe_toFinset]
        exact Or.inl (Or.inl (Or.inl (Or.inl hv)))
      placesOver_subset_exceptional := fun w k v hv => by
        show v ∈ ((hS0fin w).toFinset : Set _)
        rw [Set.Finite.coe_toFinset]
        exact Or.inl (Or.inl (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨k, hv⟩))))
      primes_subset_exceptional := fun w v hv => by
        have h := coe_pDC D.host (lw w) ▸ (Finset.mem_coe.2 hv)
        rw [← Finset.mem_coe, Set.Finite.coe_toFinset]
        split_ifs at h
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl (Or.inr h))
      RCG := RCG
      grpRCG := hgrp
      finRCG := hfint
      RCG_l := hRCG.1
      art := art'
      art_surj := hRCG.2.1
      art_cont := hRCG.2.2.1
      art_anti := hRCG.2.2.2.1
      art_unr := hRCG.2.2.2.2.1
      art_univ := hRCG.2.2.2.2.2.1
      res := res
      res_art := hRCG.2.2.2.2.2.2 }

  choose eO0 heO0 using fun w => exists_equiv_intOf (lw w) (K0 w)
  choose br hbr using fun w (v : PlE D.host) (hv : v ∈ placesOver D.host.E (lw w)) =>
    (hc0 (lw w) (j0 w)).2.2 (K0 w) (hb _ _) v hv
  have hcardC : ∀ w, Cardinal.aleph0 < Cardinal.mk ℂ_[lw w] := fun w => by
    rw [card_padicComplex, Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  choose ι' hι' using fun w => exists_ringEquiv_over ↥D.LL0 ℂ_[lw w] ℂ
    ((algebraMap (PadicAlgCl (lw w)) ℂ_[lw w]).comp (j0 w)) (embLL0 D) (card_padicComplex (lw w)) (hcardC w)
  let toHC : HChar D.host.E → Formalism.L2.NC.HC D.host.E := fun χ => ⟨χ.1, χ.2.1, χ.2.2⟩
  let mu0H : ℕ → Formalism.L2.NC.HC D.host.E := fun n =>
    if h : 1 ≤ n ∧ n ≤ D.R.m then toHC (cf.mu0 ⟨n - 1, by omega⟩) else 1
  have hmu0H : ∀ j : Fin D.R.m, mu0H (j.1 + 1) = toHC (cf.mu0 j) := fun j => by
    simp only [mu0H]
    rw [dif_pos ⟨by omega, by omega⟩]
    congr 2
  let etaH := toHC cf.eta
  let delH : HeightOneSpectrum (𝓞 ↥D.LL0) → Formalism.L2.NC.HC D.host.E := fun w => toHC (cf.delAt (lw w))
  let mapO : ∀ w, FractionRing ↥(Loc.OL (K0 w)) →+* FractionRing ↥(clC (lw w) (Kt (lw w) (K0 w) (Lw w))) := fun w =>
    @IsFractionRing.map _ _ _ _ _ _ _ _ _ _ _ _ _ (toO w) (T.O_inj w)
  let liftC : ∀ w, FractionRing ↥(clC (lw w) (Kt (lw w) (K0 w) (Lw w))) →+* ℂ_[lw w] := fun w =>
    IsFractionRing.lift (g := (clC (lw w) (Kt (lw w) (K0 w) (Lw w))).subtype) Subtype.val_injective
  have hφalg : ∀ w (y : ↥(Loc.OL (K0 w))), φ w (algebraMap ↥(Loc.OL (K0 w)) (FractionRing ↥(Loc.OL (K0 w))) y) =
      (y : ↥(K0 w).1) := fun w y => by simp [φ]
  have hκy : ∀ w (y : ↥(Loc.OL (K0 w))), κ w (algebraMap ↥(Loc.OL (K0 w)) (FractionRing ↥(Loc.OL (K0 w))) y) =
      ((y : ↥(K0 w).1) : PadicAlgCl (lw w)) := fun w y => by
    show (((φ w) (algebraMap _ _ y) : ↥(K0 w).1) : PadicAlgCl (lw w)) = _
    rw [hφalg]
  have hemb0 : ∀ w x, φ w (emb0 w x) = jK w x := fun w x => by simp [emb0]
  have hlm : ∀ w z, liftC w (mapO w z) = algebraMap (PadicAlgCl (lw w)) ℂ_[lw w] (κ w z) := fun w z => by
    have h := IsLocalization.ringHom_ext (nonZeroDivisors ↥(Loc.OL (K0 w)))
      (j := (liftC w).comp (mapO w)) (k := (algebraMap (PadicAlgCl (lw w)) ℂ_[lw w]).comp (κ w)) (RingHom.ext fun y => by
        simp only [RingHom.comp_apply]
        rw [hκy]
        simp only [mapO, liftC, IsFractionRing.map, IsLocalization.map_eq, IsFractionRing.lift_algebraMap]
        erw [IsFractionRing.lift_algebraMap]
        exact htoO w y)
    exact DFunLike.congr_fun h z
  let Sp : RingSpec D cf b0 b1 Sx T :=
    { eTw := Equiv.refl _
      pl_emb := fun w => ⟨(hlw w).2, fun x => by
        show x ∈ w.asIdeal ↔ _
        rw [hJ (lw w) w (hlw w).2 x]
        constructor
        · intro hx
          let z : ↥(K0 w).1 := ⟨j0 w x, hj0K w x⟩
          have hz : z ∈ Loc.OL (K0 w) := (mem_OL_iff _ _ z).2 hx.le
          refine ⟨⟨z, hz⟩, (mem_maximalIdeal_OL_iff _ _ _).2 hx, ?_⟩
          apply (φ w).injective
          rw [hφalg, hemb0]
          rfl
        · rintro ⟨y, hy, e⟩
          have e2 : ((φ w (algebraMap _ _ y) : ↥(K0 w).1) : PadicAlgCl (lw w)) = ((φ w (emb0 w x) : ↥(K0 w).1) : PadicAlgCl (lw w)) :=
            congrArg (fun t => ((φ w t : ↥(K0 w).1) : PadicAlgCl (lw w))) e
          rw [hφalg, hemb0] at e2
          rw [(mem_maximalIdeal_OL_iff _ _ _)] at hy
          rw [← show ((jK w x : ↥(K0 w).1) : PadicAlgCl (lw w)) = j0 w x from rfl, ← e2]
          exact hy⟩
      K0 := K0
      eO0 := eO0
      j0 := j0
      Lw := Lw
      eO := fun w => RingEquiv.refl _
      eOk := fun w k => RingEquiv.refl _
      iCq := fun w => (ι' w).toRingHom.comp (liftC w)
      ringSpec_baseExtension_lowerBound := fun w => le_rfl
      Lw_big := fun w => le_rfl
      ringSpec_baseIntegersEquiv_algebraMap := fun w z => by
        rw [heO0, ← hκ w z, hκy]
      ringSpec_baseEmbedding_compatible := fun w x y z hz => by
        have key : ∀ a b : FractionRing ↥(Loc.OL (K0 w)), a = b ↔ ((φ w a : ↥(K0 w).1) : PadicAlgCl (lw w)) = ((φ w b : ↥(K0 w).1) : PadicAlgCl (lw w)) :=
          fun a b => ⟨fun h => h ▸ rfl, fun h => (φ w).injective (Subtype.ext h)⟩
        have hjK : ((jK w x : ↥(K0 w).1) : PadicAlgCl (lw w)) = j0 w x := rfl
        rw [key, map_mul, hemb0, hφalg, hφalg, heO0, heO0, IntermediateField.coe_mul, hjK]
      eO_alg := fun w y => by
        rw [RingEquiv.refl_apply, RingHom.algebraMap_toAlgebra, htoO, heO0]
      eOk_alg := fun w k x => by simp only [RingEquiv.refl_apply]; exact Subring.coe_inclusion _ x
      mu_g := fun w k _ => ((hc0 (lw w) (j0 w)).2.1.trans (hb _ _)).trans (le_sup_left.trans le_sup_left)
      ringSpec_excludedPlaces_eq := fun w => Set.Finite.coe_toFinset _
      br := br
      br_ind := hbr
      mu0H := mu0H
      etaH := etaH
      delH := delH
      embO := fun w b => (mapO w).comp (if b then emb0 w else emb0b w)
      del_fix := fun s s' h => by
        change pDC D.host (lw s) = pDC D.host (lw s') at h
        have h' := congrArg (fun F : Finset (PlE D.host) => (F : Set (PlE D.host))) h
        simp only [coe_pDC] at h'
        simp only [delH, CharFrame.delAt]
        split_ifs at h' ⊢ with h1 h2 h2
        · rfl
        · exact absurd (placesOver_inj _ D.host.pde'_prime D.host.pde_prime h') D.host.pde_ne.symm
        · exact absurd (placesOver_inj _ D.host.pde_prime D.host.pde'_prime h') D.host.pde_ne
        · rfl
      delta := fun s => read_of_isGal ha (hdc s).1 D.nd.plOm.1 D.nd.plOm.2 (emb0 s) (embLL0 D) (hf s) (delH s) 0
        (vals_zero (embLL0 D) _ (hdel s) (delH s) rfl)
      chi1 := fun s j b h1 h2 => by
        obtain ⟨j', rfl⟩ : ∃ j' : Fin D.R.m, j = j'.1 + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
        obtain ⟨n, hn⟩ := (hdc s).2.1 j' b
        show Formalism.L2.NC.Read D.nd.plOm.1 (chi1 s (j'.1 + 1) b) _ (if b then emb0 s else emb0b s) (embLL0 D) (mu0H (j'.1 + 1) * delH s * etaH⁻¹) _
        rw [hmu0H]
        refine read_of_isGal ha hn D.nd.plOm.1 D.nd.plOm.2 _ (embLL0 D) ?_ _ _
          (vals_block (embLL0 D) _ _ ((almostIn_of_valuesIn (hV.mu0 j')).mul (almostIn_of_valuesIn (hdel s))) hV.eta
            (GlobalTheory.TameLabels.odd_r D.R) _ _ rfl rfl)
        intro x
        cases b
        · rw [sideIso_false]
          simp only [Bool.false_eq_true, if_false]
          rw [hf', Complex.conj_conj]
        · exact hf s x
      ringSpec_sidedEmbedding_fixedField := fun s b x y h => by
        show mapO s ((if b then emb0 s else emb0b s) x) = _
        rw [← h]
        exact IsLocalization.map_eq _ _
      etaT_unr := fun P => ((hc_at cf.eta etaH rfl P).2).1 (cf.isEta.unr P)
      etaT_inf := eta_unitArg D.host cf.eta cf.isEta etaH rfl
      eta_eq := fun x => rfl
      ringSpec_normalisedCharacter_eq := fun j x => by rw [hmu0H]
      del_eq := fun s x => rfl
      iCq_embO := fun s x => by
        show ι' s (liftC s (mapO s (emb0 s x))) = _
        rw [hlm, hκemb, ← RingHom.comp_apply, hι']
        rfl
      embO_star := fun s x y h => by
        show mapO s (emb0 s (st x)) = mapO s (emb0 s y)
        congr 2
        exact Subtype.ext h.symm
      deltaRead := fun s v hv hu B σ hB hσ => by
        obtain ⟨y, hy⟩ := hdel s v hu
        refine ⟨y⁻¹, ?_, frob_read ha (hdc s).1 (emb0 s) (embLL0 D) (hf s) (Or.inl hv) hu hB hσ ?_⟩
        · show embLL0 D y⁻¹ = _
          rw [map_inv₀, hy, Units.val_inv_eq_inv_val]
          simp [HChar.valTw]
          rfl
        · rw [map_inv₀, hy]
          simp [HChar.valTw] }
  exact ⟨T, Sp, fun i => ⟨rfl, rfl, rfl⟩⟩
end GlobalTheory.TwRing
