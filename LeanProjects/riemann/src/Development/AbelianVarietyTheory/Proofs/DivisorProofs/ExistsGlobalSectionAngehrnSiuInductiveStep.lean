import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AngehrnSiuNotKltAtSeveralPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.H0LowerBoundIntersectionNumberClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLtBinomialBoundOfMulPowLtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueMapClosurePointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalEquationEffectiveQCartierDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalLocalEquationAddSmulDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsRestrictBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtFnOfOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocModelLocRingAndExistsTrBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceTopFormOrdersApi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalResidueFieldClosedPointProjectiveComplexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedPointLocalRingNormalSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasisMemOfIsLocalRingOfVarietyPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalEquationChangeFormPerturbedDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancySubQCartierCoeffNonposStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem unitAt_pow' {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (hf : UnitAt x f) :
    ∀ l : ℕ, UnitAt x (f ^ l)
  | 0 => by simpa using unitAt_one x
  | l + 1 => by rw [pow_succ]; exact (unitAt_pow' hf l).mul hf

theorem discrep_sub_ord_eq : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (n : ℕ), topologicalKrullDim X = n → ∀ (Δ D : X → ℚ)
    (η η' : RatForms p n) (x z : X) (m m' mD : ℕ) (gG g' fD : X.functionFieldˣ) (E : DivOver p),
    η ≠ 0 → η' ≠ 0 → 0 < m → 0 < m' → 0 < mD → IsLogEqn p Δ η x m gG →
    (∀ w, w ⤳ x → ∀ E : DivOver p, E.IsAt w → D w = (E.ord fD : ℚ) / mD) →
    z ⤳ x → E.Through z → IsLogEqn p (Δ + D) η' z m' g' →
    discrep E η m gG - E.ord fD / mD = discrep E η' m' g' := by
  intro X _ _ _ p _ n hn Δ D η η' x z m m' mD gG g' fD E hη hη' hm hm' hmD hG hD hzx hE h'
  obtain ⟨m'', g'', hm'', h'', hd⟩ := isLogEqn_add_smul X p n Δ D η x m mD gG fD 1 hm hmD hG hD
  rw [one_smul] at h''
  have hz : IsLogEqn p (Δ + D) η z m'' g'' := fun w hw F hF => h'' w (hw.trans hzx) F hF
  rw [← discrep_eq hn hη hη' hm'' hm' hz h' hE, hd E, one_mul]

theorem not_kltAt_of_local : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ : X → ℚ) (m : ℕ) (G A : CartierDiv X) (D : X → ℚ) (z x : X) (k l M r : ℕ) (h δ : ℚ)
      (f₀ : X.functionField) (aX : X.functionFieldˣ) (mD : ℕ) (fD : X.functionFieldˣ)
      {κ : Type} [Field κ] (π₀ : locRing z →+* κ) (hxz : locRing x ≤ locRing z)
      (w : Fin r → locRing x) (a : Fin r → ℂ),
    IsEffQDiv Δ → IsLogCanonicalMultiple p n Δ m G → 0 < m → IsQCart D → z ⤳ x → 0 < l → 0 ≤ h →
    0 ≤ δ → δ ≤ 1 → (∀ r, π₀ r = 0 ↔ ZeroAt z (r : X.functionField)) →
    A.IsEqn x aX → 0 < mD → RegAt x (fD : X.functionField) →
    (∀ w, w ⤳ x → ∀ E : DivOver p, E.IsAt w → D w = (E.ord fD : ℚ) / mD) →
    (∑ j, Cartier.constFn p (a j) * (w j : X.functionField)) = f₀ * (aX : X.functionField) ^ l →
    ((z = genericPoint X ∧ (k : ℚ) * l < h * M) ∨
      ∃ E : DivOver p, CentreAt E z ∧ (∃ (η' : RatForms p n) (m' : ℕ) (g' : X.functionFieldˣ), η' ≠ 0 ∧
        0 < m' ∧ IsLogEqn p (Δ + D) η' z m' g' ∧ discrep E η' m' g' ≤ -1) ∧
        (k : ℚ) + M * (δ * (E.ord fD / mD)) ≤ h / l * M) →
    (∀ (xi : Fin n → locRing x) (φ : locRing x →₀ ℚ) (u s : locRing x) (t : ℚ),
      TrBasis (Cartier.constFn p) (fun j => (xi j : X.functionField)) → (∀ g ∈ φ.support, g ≠ 0) →
      EffAt (Cartier.constFn p) n (locRing x) (dForm (Cartier.constFn p) (fun j => (xi j : X.functionField)))
        (Finsupp.mapDomain (fun g : locRing x => (g : X.functionField)) φ) →
      π₀.comp (Subring.inclusion hxz) u = 0 → 0 ≤ t →
      (s : X.functionField) = ∑ j, Cartier.constFn p (a j) * (w j : X.functionField) + u →
      (s : X.functionField) ≠ 0 →
      ((Function.Injective (π₀.comp (Subring.inclusion hxz)) ∧ (k : ℚ) ≤ t * M) ∨
        ∃ E : Place (Cartier.constFn p), E.Contains (locRing x) ∧
          (∀ r : locRing x, (r : X.functionField) ≠ 0 →
            (π₀.comp (Subring.inclusion hxz) r = 0 ↔ 0 < E.ord r)) ∧
          (k : ℚ) + M * (E.disc (dForm (Cartier.constFn p) (fun j => (xi j : X.functionField)))
            (Finsupp.mapDomain (fun g : locRing x => (g : X.functionField)) φ) + 1) ≤ t * M) →
      ¬ Klt (Cartier.constFn p) n (locRing x) (dForm (Cartier.constFn p) (fun j => (xi j : X.functionField)))
        (Finsupp.mapDomain (fun g : locRing x => (g : X.functionField)) φ +
          Finsupp.single (s : X.functionField) t)) →
    ∀ u ∈ (l • A).sections, (l • A).VanishesAt z u → ∀ g : X.functionFieldˣ, (g : X.functionField) = f₀ + u →
      ¬ KltAt p n (Δ + (1 - δ) • D + (h / l) • qWeil (CartierDiv.principal g + l • A) 1) x := by
  intro X _ _ _ p n hp hn Δ m G A D z x k l M r h δ f₀ aX mD fD κ _ π₀ hxz w a hΔ hG hm hD hzx hl hh
    hδ0 hδ1 hπ hA hmD hfD hDx hw hcase H u hu hvan g hg hK
  haveI := GlobalTheory.isProjOver_locallyOfFiniteType ℂ X p hp
  have hLM : IsLocModel (Cartier.constFn p) (locRing x) := isLocModel_locRing x
  obtain ⟨-, hx0⟩ := isLocModel_locRing_and_exists_trBasis X p n x hn
  obtain ⟨xi, hxi⟩ := GlobalTheory.T.exists_trBasis_mem_of_isLocalRingOfVarietyPoint (Cartier.constFn p) (locRing x) n hLM hx0
  have hfree := isFreeGen_dForm_of_trBasis (Cartier.constFn p) hxi
  have hω0 : dForm (Cartier.constFn p) (fun j => (xi j : X.functionField)) ≠ 0 := fun h0 =>
    one_ne_zero (hfree.1 (a₁ := 1) (a₂ := 0) (by simp [h0]))
  obtain ⟨η, hη, hGη⟩ := hG
  obtain ⟨gG, hgG⟩ := G.exists_isEqn x
  have hLE := hGη x gG hgG
  obtain ⟨F0, hF0⟩ := hfree.2 η
  replace hF0 : F0 • dForm (Cartier.constFn p) (fun j => (xi j : X.functionField)) = η := hF0
  have hF0ne : F0 ≠ 0 := fun h0 => hη (by rw [← hF0, h0, zero_smul])
  obtain ⟨m₂, g₂, hm₂, hLE₂, hdisc₂⟩ := GlobalTheory.T.isLogCanonicalEquation_changeForm_perturbed_divisor X p n hn Δ D η
    (dForm (Cartier.constFn p) (fun j => (xi j : X.functionField))) x m mD l gG fD g aX
    (Units.mk0 F0 hF0ne) A δ (h / l) hω0 hF0.symm hm hmD hLE hDx hA
  have hKlt := (kltAt_iff_klt (p := p) hn hω0 hm₂ hLE₂).1 hK

  have hAz : A.IsEqn z aX := by
    obtain ⟨U, hxU, hU⟩ := hA.exists_nhds
    exact hU z (hzx.mem_open U.isOpen hxU)
  have hAl := hA.nsmul l
  have hAlz := hAz.nsmul l

  have hsum : (f₀ * (aX : X.functionField) ^ l) ∈ locRing x := by
    rw [← hw]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hLM.const_mem _) (w j).2
  have hux : u * (aX : X.functionField) ^ l ∈ locRing x := by
    have := (hAl.regularAt_iff).1 ((CartierDiv.mem_sections).1 hu x)
    exact mem_locRing.2 (by simpa using this)
  have hgx : (g : X.functionField) * (aX : X.functionField) ^ l ∈ locRing x := by
    rw [hg, add_mul]; exact Subring.add_mem _ hsum hux
  have huz : ZeroAt z (u * (aX : X.functionField) ^ l) := by
    have := (hAlz.vanishesAt_iff).1 hvan
    simpa using this

  set ω := dForm (Cartier.constFn p) (fun j => (xi j : X.functionField)) with hω
  have hmR : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  set q : X.functionField := (gG : X.functionField) * (F0 ^ m)⁻¹ with hq
  have hq0 : q ≠ 0 := mul_ne_zero gG.ne_zero (inv_ne_zero (pow_ne_zero _ hF0ne))
  obtain ⟨a₁, ha₁, b₁, hb₁, hb0, hab⟩ := hLM.frac q
  have ha0 : a₁ ≠ 0 := by rw [← hab]; exact mul_ne_zero hq0 hb0
  let φ : locRing x →₀ ℚ := Finsupp.single ⟨a₁, ha₁⟩ (1 / m : ℚ) - Finsupp.single ⟨b₁, hb₁⟩ (1 / m : ℚ) +
    Finsupp.single ⟨(fD : X.functionField), hfD⟩ ((1 - δ) / mD)
  have hmap : Finsupp.mapDomain (fun g : locRing x => (g : X.functionField)) φ =
      Finsupp.single a₁ (1 / m : ℚ) - Finsupp.single b₁ (1 / m : ℚ) +
        Finsupp.single (fD : X.functionField) ((1 - δ) / mD) := by
    simp only [φ, Finsupp.mapDomain_add, Finsupp.mapDomain_sub, Finsupp.mapDomain_single]
  have hφ0 : ∀ g ∈ φ.support, g ≠ 0 := by
    rintro g hgs rfl
    apply Finsupp.mem_support_iff.1 hgs
    have e1 : (⟨a₁, ha₁⟩ : locRing x) ≠ 0 := fun e => ha0 (congrArg Subtype.val e)
    have e2 : (⟨b₁, hb₁⟩ : locRing x) ≠ 0 := fun e => hb0 (congrArg Subtype.val e)
    have e3 : (⟨(fD : X.functionField), hfD⟩ : locRing x) ≠ 0 := fun e => fD.ne_zero (congrArg Subtype.val e)
    simp [φ, Finsupp.single_apply, e1, e2, e3]
  have hord (E : Place (Cartier.constFn p)) : (E.ord a₁ : ℚ) - E.ord b₁ = E.ord gG - m * E.ord F0 := by
    have h1 : E.ord a₁ = E.ord q + E.ord b₁ := by rw [← hab, E.ord_mul hq0 hb0]
    have h2 : E.ord q = E.ord gG - m * E.ord F0 := by
      rw [hq, E.ord_mul gG.ne_zero (inv_ne_zero (pow_ne_zero _ hF0ne)), E.ord_inv, E.ord_pow]; ring
    rw [h1, h2]; push_cast; ring
  have hdψ (E : Place (Cartier.constFn p)) : E.disc ω (Finsupp.mapDomain (fun g : locRing x => (g : X.functionField)) φ) =
      E.formOrd η - E.ord gG / m - (1 - δ) * (E.ord fD / mD) := by
    rw [Place.disc, hmap, map_add, map_sub, Place.ordQ_single, Place.ordQ_single, Place.ordQ_single, ← hF0,
      E.formOrd_smul hxi hω0 hF0ne]
    have := hord E
    have e : (1 / (m : ℚ)) * E.ord a₁ - 1 / m * E.ord b₁ = E.ord gG / m - E.ord F0 := by
      rw [← mul_sub, this]; field_simp
    push_cast
    linear_combination -e
  have hdψs (E : Place (Cartier.constFn p)) (ψ : X.functionField →₀ ℚ) (s : X.functionField) (t : ℚ) :
      E.disc ω (ψ + Finsupp.single s t) = E.disc ω ψ - t * E.ord s := by
    rw [Place.disc, Place.disc, map_add, Place.ordQ_single]; ring
  have hs0 : (g : X.functionField) * (aX : X.functionField) ^ l ≠ 0 :=
    mul_ne_zero g.ne_zero (pow_ne_zero _ aX.ne_zero)
  have hψ0 : Finsupp.mapDomain (fun g : locRing x => (g : X.functionField)) φ 0 = 0 := by
    rw [hmap]; simp [Finsupp.single_apply, ha0, hb0, fD.ne_zero]

  have hK2 : Klt (Cartier.constFn p) n (locRing x) ω
      (Finsupp.mapDomain (fun g : locRing x => (g : X.functionField)) φ +
        Finsupp.single ((g : X.functionField) * (aX : X.functionField) ^ l) (h / l)) := by
    refine ⟨hω0, ?_, fun E hE => ?_⟩
    · rw [Finsupp.add_apply, hψ0]; simp [Finsupp.single_apply, hs0]
    · obtain ⟨E', rfl⟩ := (placeEquiv p).surjective E
      have h1 := hKlt.lt_disc hE
      rw [disc_placeEquiv, hdisc₂ E'] at h1
      rw [hdψs, hdψ, ← hF0, (placeEquiv p E').formOrd_smul hxi hω0 hF0ne]
      have e1 : (placeEquiv p E').ord ((g : X.functionField) * (aX : X.functionField) ^ l) =
          E'.ord (g * aX ^ l) := by rw [← ord_placeEquiv]; push_cast; rfl
      have e2 : (placeEquiv p E').ord F0 = E'.ord (Units.mk0 F0 hF0ne) := rfl
      have e3 : (placeEquiv p E').formOrd ω = E'.formOrd ω := rfl
      have e4 : (placeEquiv p E').ord (gG : X.functionField) = E'.ord gG := rfl
      have e5 : (placeEquiv p E').ord (fD : X.functionField) = E'.ord fD := rfl
      rw [e1, e2, e3, e4, e5]
      push_cast
      linarith
  have hEff : EffAt (Cartier.constFn p) n (locRing x) ω
      (Finsupp.mapDomain (fun g : locRing x => (g : X.functionField)) φ) := by
    refine ⟨hω0, hψ0, fun E hE => ?_⟩
    obtain ⟨E', rfl⟩ := (placeEquiv p).surjective E
    have h1 := GlobalTheory.T.discrepancy_sub_qCartier_coeff_nonpos X p n Δ D η x m mD gG fD δ hΔ hD hδ1 hm hmD hLE hDx E' hE
    rw [hdψ]
    exact h1
  refine H xi φ ⟨u * (aX : X.functionField) ^ l, hux⟩ ⟨(g : X.functionField) * (aX : X.functionField) ^ l, hgx⟩
    (h / l) hxi hφ0 hEff ((hπ _).2 huz) (div_nonneg hh (Nat.cast_nonneg _)) ?_ hs0 ?_ hK2
  · show (g : X.functionField) * (aX : X.functionField) ^ l = _ + u * (aX : X.functionField) ^ l
    rw [hw, hg]; ring
  rcases hcase with ⟨rfl, hkl⟩ | ⟨E, hC, ⟨η', m', g', hη', hm', hLE', hle⟩, hbd⟩
  · refine Or.inl ⟨(injective_iff_map_eq_zero _).2 fun r hr => ?_, ?_⟩
    · have hz := (hπ _).1 hr
      by_contra hr0
      have hr0' : (r : X.functionField) ≠ 0 := fun e => hr0 (Subtype.ext e)
      exact (zeroAt_iff.1 hz).2 (unitAt_genericPoint hr0')
    · have hlR : (0 : ℚ) < l := by exact_mod_cast hl
      rw [div_mul_eq_mul_div, le_div_iff₀ hlR]
      linarith
  · refine Or.inr ⟨placeEquiv p E, (contains_placeEquiv E x).2 (hC.1.of_specializes hzx), fun r hr0 => ?_, ?_⟩
    · have hrz : RegAt z (r : X.functionField) := hxz r.2
      change π₀ (Subring.inclusion hxz r) = 0 ↔ 0 < E.ord (Units.mk0 (r : X.functionField) hr0)
      rw [hπ]
      change ZeroAt z (r : X.functionField) ↔ _
      constructor
      · intro hz0
        have h0 : 0 ≤ E.ord (Units.mk0 (r : X.functionField) hr0) :=
          (E.ord_nonneg_iff _).2 (hC.1 _ hrz)
        rcases h0.lt_or_eq with h0 | h0
        · exact h0
        · exfalso
          have hi := hC.2 (Units.mk0 (r : X.functionField) hr0) hrz h0.symm
          have hU : UnitAt z (r : X.functionField) := (unitAt_iff hr0).2 ⟨hrz, by simpa using hi⟩
          exact (zeroAt_iff.1 hz0).2 hU
      · intro hpos
        refine zeroAt_iff.2 ⟨hrz, fun hU => ?_⟩
        have hi := hU.inv.regAt
        have h0 := (E.ord_nonneg_iff (Units.mk0 (r : X.functionField) hr0)⁻¹).2 (hC.1 _ (by simpa using hi))
        rw [E.ord_inv] at h0
        omega
    · rw [hdψ]
      have key := discrep_sub_ord_eq X p n hn Δ D η η' x z m m' mD gG g' fD E hη hη' hm hm' hmD hLE hDx hzx
        hC.1 hLE'
      have e3 : (placeEquiv p E).formOrd η = E.formOrd η := rfl
      have e4 : (placeEquiv p E).ord (gG : X.functionField) = E.ord gG := rfl
      have e5 : (placeEquiv p E).ord (fD : X.functionField) = E.ord fD := rfl
      rw [e3, e4, e5]
      have hd : (E.formOrd η : ℚ) - E.ord gG / m = discrep E η m gG := rfl
      have hM : (0 : ℚ) ≤ M := Nat.cast_nonneg _
      have hb : (E.formOrd η : ℚ) - E.ord gG / m - (1 - δ) * (E.ord fD / mD) + 1 ≤ δ * (E.ord fD / mD) := by
        rw [hd]; linarith
      nlinarith [mul_le_mul_of_nonneg_left hb hM]

theorem exists_global_step : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ),
  IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p;
  ∀ (Δ : X → ℚ) (m : ℕ) (G A : CartierDiv X) (D : X → ℚ) (P : Finset X) (z : X) (k : ℕ) (h : ℚ),
  IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB (toLB A) → IsQCart D →
  (∀ x ∈ P, IsClosed ({x} : Set X) ∧ z ⤳ x) → 1 ≤ k → topologicalKrullDim (closure ({z} : Set X)) = k →
  (z = genericPoint X ∨ IsNkltCentre p n (Δ + D) z) → 0 < h →
  (P.card : ℚ) * (k : ℚ) ^ k < h ^ k * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) →
  ∀ l₀ : ℕ, ∃ l : ℕ, l₀ ≤ l ∧ h < l ∧ ∃ f₀ ∈ (l • A).sections, (l • A).GeneratesAt z f₀ ∧
    ∃ δ₀ : ℚ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ u ∈ (l • A).sections, (l • A).VanishesAt z u →
      ∀ g : X.functionFieldˣ, (g : X.functionField) = f₀ + u → ∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ∀ x ∈ P,
        ¬ KltAt p n (Δ + (1 - δ) • D + (h / l) • qWeil (CartierDiv.principal g + l • A) 1) x := by
  intro hPr X _ _ _ p n hp hn Δ m G A D P z k h hΔ _ hm hG hA hD hP hk hZ hcase hh hnum l₀
  haveI := GlobalTheory.isProjOver_locallyOfFiniteType ℂ X p hp

  obtain ⟨q, hq, hnumq⟩ := GlobalTheory.T.exists_lt_binomial_bound_of_mul_pow_lt P.card k h _ hk hh hnum
  obtain ⟨l₁, hl₁⟩ := GlobalTheory.T.h0_lower_bound_of_isAmple_cartierDiv X p hp A z k q hA hZ hq
  obtain ⟨l₂, hl₂⟩ := exists_sections_restrict_basis X p hp A z hA
  obtain ⟨l, M, hl0, hM, hkl, hhl, hcl⟩ := hnumq (max l₀ (max l₁ l₂))
  obtain ⟨r, f, hfs, hr, hgen⟩ := hl₂ l ((le_max_right _ _).trans ((le_max_right _ _).trans hl0))
  have hq1 := hl₁ l ((le_max_left _ _).trans ((le_max_right _ _).trans hl0))
  have hcr : P.card * (M + k - 1).choose k < r := by
    have : ((P.card * (M + k - 1).choose k : ℕ) : ℚ) < r := by rw [hr]; exact lt_of_lt_of_le hcl hq1
    exact_mod_cast this

  obtain ⟨κ, _, _, π₀, -, hπ, hconst, hκ, hloc⟩ := GlobalTheory.T.exists_residueMap_closure_point X p hp z k hZ
  letI : Algebra ℂ X.functionField := (Cartier.constFn p).toAlgebra
  choose aX haX using fun x : X => A.exists_isEqn x
  obtain ⟨aZ, haZ⟩ := A.exists_isEqn z
  choose mD fD hmD hfD hDx using fun x : X => exists_localEqn_of_isQCart X p D hD x
  let e : Fin P.card ≃ P := P.equivFin.symm
  have hxz : ∀ i, locRing (e i : X) ≤ locRing z := fun i f hf =>
    regAt_of_specializes (hP _ (e i).2).2 hf
  have hAz : ∀ i, A.IsEqn z (aX (e i)) := fun i => by
    obtain ⟨U, hxU, hU⟩ := (haX (e i)).exists_nhds
    exact hU z ((hP _ (e i).2).2.mem_open U.isOpen hxU)
  have hunit : ∀ i, UnitAt z ((aX (e i) : X.functionField) ^ l / (aZ : X.functionField) ^ l) := fun i => by
    rw [← div_pow]
    exact unitAt_pow' ((haZ.iff_unitAt).1 (hAz i)) l
  have hwreg : ∀ i j, f j * (aX (e i) : X.functionField) ^ l ∈ locRing (e i : X) := fun i j => by
    have := ((haX (e i)).nsmul l).regularAt_iff.1 ((CartierDiv.mem_sections).1 (hfs j) _)
    exact mem_locRing.2 (by simpa using this)
  have hwbreg : ∀ j, f j * (aZ : X.functionField) ^ l ∈ locRing z := fun j => by
    have := (haZ.nsmul l).regularAt_iff.1 ((CartierDiv.mem_sections).1 (hfs j) _)
    exact mem_locRing.2 (by simpa using this)
  let π : ∀ i, locRing (e i : X) →+* κ := fun i => π₀.comp (Subring.inclusion (hxz i))
  let w : ∀ i, Fin r → locRing (e i : X) := fun i j => ⟨_, hwreg i j⟩
  let lam : Fin P.card → κ := fun i => π₀ ⟨_, (hunit i).regAt⟩
  let wb : Fin r → κ := fun j => π₀ ⟨_, hwbreg j⟩
  have hlamw : ∀ i, lam i ≠ 0 ∧ ∀ j, π i (w i j) = lam i * wb j := fun i => by
    refine ⟨fun h0 => (zeroAt_iff.1 ((hπ _).1 h0)).2 (hunit i), fun j => ?_⟩
    show π₀ (Subring.inclusion (hxz i) (w i j)) = _
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    show f j * (aX (e i) : X.functionField) ^ l =
      (aX (e i) : X.functionField) ^ l / (aZ : X.functionField) ^ l * (f j * (aZ : X.functionField) ^ l)
    have : (aZ : X.functionField) ^ l ≠ 0 := pow_ne_zero _ aZ.ne_zero
    field_simp

  obtain ⟨av, hav, hfam⟩ := GlobalTheory.T.angehrnSiu_not_klt_at_several_points hPr n k P.card r M (fun i => locRing (e i : X)) π w lam wb
    (isLocModel_locRing_and_exists_trBasis X p n z hn).2 hκ hk
    (fun i => ⟨isLocModel_locRing _, GlobalTheory.T.isIntegrallyClosed_pointLocalRing_normalScheme X _, GlobalTheory.T.rationalResidueField_closedPoint_projectiveComplex X p hp _ (hP _ (e i).2).1⟩)
    (fun i a h => hconst a (hxz i h)) (fun i f => (hloc _ (hxz i)).2.1 f)
    (fun i => ⟨(hloc _ (hxz i)).1, (hloc _ (hxz i)).2.2 (hP _ (e i).2).1⟩) hlamw hcr hM

  have hf₀ : (∑ j, Cartier.constFn p (av j) * f j) ∈ (l • A).sections := by
    rw [CartierDiv.mem_sections]
    intro x
    obtain ⟨g0, hg0⟩ := (l • A).exists_isEqn x
    rw [hg0.regularAt_iff, Finset.sum_mul]
    refine Subring.sum_mem (locRing x) fun j _ => ?_
    rw [mul_assoc]
    exact Subring.mul_mem _ ((isLocModel_locRing x).const_mem _)
      (mem_locRing.2 (hg0.regularAt_iff.1 ((CartierDiv.mem_sections).1 (hfs j) x)))
  have hMpos : (0 : ℚ) < M := by exact_mod_cast hM
  have hlpos : (0 : ℚ) < l := lt_trans hh hhl
  have hl : 0 < l := by exact_mod_cast hlpos
  have hgap : 0 < h / l * M - k := by
    rw [div_mul_eq_mul_div, sub_pos, lt_div_iff₀ hlpos]
    linarith
  have hwsum : ∀ i, (∑ j, Cartier.constFn p (av j) * (w i j : X.functionField)) =
      (∑ j, Cartier.constFn p (av j) * f j) * (aX (e i) : X.functionField) ^ l := fun i => by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    show Cartier.constFn p (av j) * (f j * (aX (e i) : X.functionField) ^ l) = _
    ring
  have hei : ∀ x (hx : x ∈ P), (e (P.equivFin ⟨x, hx⟩) : X) = x := fun x hx => by simp [e]
  refine ⟨l, (le_max_left _ _).trans hl0, hhl, _, hf₀, hgen av hav, ?_⟩
  rcases hcase with hgenz | ⟨E, η', m', g', hη', hm', hLE', hC, hdle⟩
  · refine ⟨1, one_pos, le_rfl, fun u hu hvan g hg δ hδ0 hδ1 x hx => ?_⟩
    have := not_kltAt_of_local X p n hp hn Δ m G A D z (e (P.equivFin ⟨x, hx⟩)) k l M r h δ _
      (aX _) (mD _) (fD _) π₀ (hxz _) (w _) av hΔ hG hm hD (hP _ (e _).2).2 hl hh.le hδ0 hδ1 hπ (haX _)
      (hmD _) (hfD _) (hDx _) (hwsum _) (Or.inl ⟨hgenz, hkl⟩) (hfam _) u hu hvan g hg
    rwa [hei x hx] at this
  · have hnn : ∀ x ∈ P, (0 : ℚ) ≤ E.ord (fD x) / mD x := fun x hx => by
      have h0 : 0 ≤ E.ord (fD x) :=
        (E.ord_nonneg_iff _).2 (hC.1.of_specializes (hP x hx).2 _ (hfD x))
      positivity
    set B : ℚ := ∑ x ∈ P, (E.ord (fD x) : ℚ) / mD x with hB
    have hB0 : 0 ≤ B := Finset.sum_nonneg hnn
    refine ⟨min 1 ((h / l * M - k) / (M * (B + 1))), lt_min one_pos (div_pos hgap (by positivity)),
      min_le_left _ _, fun u hu hvan g hg δ hδ0 hδ x hx => ?_⟩
    have hbx : (E.ord (fD x) : ℚ) / mD x ≤ B + 1 := by
      have := Finset.single_le_sum hnn hx
      linarith
    have h1 : δ * (M * (B + 1)) ≤ h / l * M - k :=
      (le_div_iff₀ (by positivity)).1 (hδ.trans (min_le_right _ _))
    have h2 : M * (δ * (E.ord (fD x) / mD x)) ≤ δ * (M * (B + 1)) := by
      have := mul_le_mul_of_nonneg_left hbx (mul_nonneg hMpos.le hδ0)
      nlinarith
    have hbd : (k : ℚ) + M * (δ * (E.ord (fD x) / mD x)) ≤ h / l * M := by linarith
    rw [← hei x hx] at hbd
    have := not_kltAt_of_local X p n hp hn Δ m G A D z (e (P.equivFin ⟨x, hx⟩)) k l M r h δ _
      (aX _) (mD _) (fD _) π₀ (hxz _) (w _) av hΔ hG hm hD (hP _ (e _).2).2 hl hh.le hδ0
      (hδ.trans (min_le_left _ _)) hπ (haX _) (hmD _) (hfD _) (hDx _) (hwsum _)
      (Or.inr ⟨E, hC, ⟨η', m', g', hη', hm', hLE', hdle⟩, hbd⟩) (hfam _) u hu hvan g hg
    rwa [hei x hx] at this

end GlobalTheory.PairStep
