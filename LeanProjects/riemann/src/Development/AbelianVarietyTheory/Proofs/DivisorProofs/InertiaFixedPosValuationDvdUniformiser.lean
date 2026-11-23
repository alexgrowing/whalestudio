import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransitiveOnValuationRings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardInertiaEqRamificationIdxOfPerfectResidueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationUniformizerIntegralClosureEqExpNegRamifStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeExpNegCardInertiaOfInertiaFixedStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

open IsDedekindDomain

namespace GlobalTheory.InertiaUnram

theorem valuationSubring_valuation_lt_one_iff {L : Type} [Field L] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (x : L) : v.valuationSubring.valuation x < 1 ↔ v x < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or,
    Valuation.mem_valuationSubring_iff]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [map_inv₀, not_le]
    constructor
    · rintro (h | h)
      · exact absurd h hx
      · exact (one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx))).1 h
    · intro h
      exact Or.inr ((one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx))).2 h)

theorem mem_iff_valuation_le_one (L S : Type) [Field L] [CommRing S] [IsDomain S] [IsDedekindDomain S]
    [Algebra S L] [IsFractionRing S L] (W : ValuationSubring L) (hS : ∀ s : S, algebraMap S L s ∈ W)
    (P : HeightOneSpectrum S) (hP : P.asIdeal = GlobalTheory.ProlongConj.primeBelow S W hS) (x : L) :
    x ∈ W ↔ P.valuation L x ≤ 1 := by
  have hS' : ∀ s : S, algebraMap S L s ∈ (P.valuation L).valuationSubring := fun s =>
    (Valuation.mem_valuationSubring_iff _ _).2 (P.valuation_le_one s)
  have key : ∀ s : S, W.valuation (algebraMap S L s) < 1 ↔
      (P.valuation L).valuationSubring.valuation (algebraMap S L s) < 1 := by
    intro s
    rw [valuationSubring_valuation_lt_one_iff, ← GlobalTheory.ProlongConj.mem_primeBelow S hS, ← hP]
    exact (P.valuation_lt_one_iff_mem s).symm
  have hW : W = (P.valuation L).valuationSubring :=
    le_antisymm (GlobalTheory.ProlongConj.le_of_valuation_lt_one_iff S hS hS' key)
      (GlobalTheory.ProlongConj.le_of_valuation_lt_one_iff S hS' hS fun s => (key s).symm)
  rw [hW, Valuation.mem_valuationSubring_iff]

theorem mem_inertia_of_mem_inertia (K L S : Type) [Field K] [Field L] [Algebra K L] [CommRing S] [IsDomain S]
    [IsDedekindDomain S] [Algebra S L] [IsFractionRing S L] [MulSemiringAction (L ≃ₐ[K] L) S]
    (hact : ∀ (g : L ≃ₐ[K] L) (s : S), algebraMap S L (g • s) = g (algebraMap S L s))
    (P : HeightOneSpectrum S) (W : ValuationSubring L) (hW : ∀ x, x ∈ W ↔ P.valuation L x ≤ 1)
    (σ : L ≃ₐ[K] L) (hσ : σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L)) : σ ∈ inertia K W := by
  set v := P.valuation L with hv
  have hWeq : W = v.valuationSubring := by
    ext x
    rw [hW, Valuation.mem_valuationSubring_iff]
  have hS : ∀ s : S, algebraMap S L s ∈ W := fun s => (hW _).2 (P.valuation_le_one s)
  have aux : ∀ τ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), ∀ x, v x ≤ 1 → v (τ x) ≤ 1 ∧ v (τ x - x) < 1 := by
    intro τ hτ x hx
    have hτ' := AddSubgroup.mem_inertia.mp hτ
    obtain ⟨s, t, hs1, e⟩ := GlobalTheory.ProlongConj.exists_den S W hS ((hW x).2 hx)
    have hsP : s ∉ P.asIdeal := by
      intro hm
      have h1 : W.valuation (algebraMap S L s) < 1 := by
        rw [hWeq, valuationSubring_valuation_lt_one_iff]
        exact (P.valuation_lt_one_iff_mem s).2 hm
      rw [hs1] at h1
      exact lt_irrefl _ h1
    have va : v (algebraMap S L s) = 1 :=
      le_antisymm (P.valuation_le_one s) (not_lt.1 fun h => hsP ((P.valuation_lt_one_iff_mem s).1 h))
    have hdiff : ∀ u : S, v (τ (algebraMap S L u) - algebraMap S L u) < 1 := by
      intro u
      rw [← hact, ← map_sub]
      exact (P.valuation_lt_one_iff_mem _).2 (hτ' u)
    have va' : v (τ (algebraMap S L s)) = 1 := by
      have h := Valuation.map_add_eq_of_lt_right v (x := τ (algebraMap S L s) - algebraMap S L s)
        (y := algebraMap S L s) (by rw [va]; exact hdiff s)
      rw [sub_add_cancel, va] at h
      exact h
    have hs0 : algebraMap S L s ≠ 0 := fun h => by rw [h, map_zero] at va; exact zero_ne_one va
    have hs0' : τ (algebraMap S L s) ≠ 0 := fun h => by rw [h, map_zero] at va'; exact zero_ne_one va'
    have hx' : x = algebraMap S L t / algebraMap S L s := by rw [← e]; field_simp
    have hτx : τ x = τ (algebraMap S L t) / τ (algebraMap S L s) := by rw [hx', map_div₀]
    constructor
    · rw [hτx, map_div₀, va', div_one, ← hact]
      exact P.valuation_le_one _
    · have : τ x - x = ((τ (algebraMap S L t) - algebraMap S L t) * algebraMap S L s -
          algebraMap S L t * (τ (algebraMap S L s) - algebraMap S L s)) /
          (τ (algebraMap S L s) * algebraMap S L s) := by
        rw [hτx, hx']; field_simp; ring
      rw [this, map_div₀, map_mul v (τ _), va, va', _root_.mul_one, div_one]
      refine Valuation.map_sub_lt v ?_ ?_
      · rw [map_mul, va, _root_.mul_one]; exact hdiff t
      · rw [map_mul]
        calc v (algebraMap S L t) * v (τ (algebraMap S L s) - algebraMap S L s)
            ≤ 1 * v (τ (algebraMap S L s) - algebraMap S L s) :=
              mul_le_mul_left (P.valuation_le_one t) _
          _ < 1 := by rw [_root_.one_mul]; exact hdiff s
  rw [mem_inertia_iff]
  refine ⟨?_, fun x hx => ?_⟩
  · ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, hW, hW]
    constructor
    · intro h
      have h2 := (aux σ hσ _ h).1
      rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h2
    · intro h
      exact (aux σ⁻¹ (inv_mem hσ) x h).1
  · rw [hWeq, valuationSubring_valuation_lt_one_iff]
    exact (aux σ hσ x ((hW x).1 hx)).2

theorem valuation_le_of_fixed (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L] [SMulCommClass (L ≃ₐ[K] L) R L]
    [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L]
    (P : HeightOneSpectrum (integralClosure R L)) (π : R) (hπ : Irreducible π) (y : L)
    (hy : ∀ σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), σ y = y) (hlt : P.valuation L y < 1) :
    P.valuation L y ≤ P.valuation L (algebraMap K L (algebraMap R K π)) := by
  rw [GlobalTheory.T.valuation_uniformizer_integralClosure_eq_exp_neg_ramificationIdx R K L P π hπ, ← GlobalTheory.T.card_inertia_eq_ramificationIdx_of_perfect_residue R K L P]
  exact GlobalTheory.T.valuation_le_exp_neg_card_inertia_of_inertia_fixed R K L P y hy hlt

theorem div_uniformiser_mem : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (W : ValuationSubring L), IsAbove R K W.toSubring →
    ∀ π : R, Irreducible π → ∀ y : L, (∀ τ ∈ inertia K W, τ y = y) → y ∈ W.nonunits →
    y / algebraMap K L (algebraMap R K π) ∈ W := by
  intro R K L _ _ _ _ _ _ _ _ _ _ _ W hW π hπ y hy hyW
  letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hc : SMulCommClass (L ≃ₐ[K] L) R L := ⟨fun g r x => by
    rw [← IsScalarTower.algebraMap_smul K r x, ← IsScalarTower.algebraMap_smul K r (g • x)]
    exact map_smul g _ _⟩
  haveI : IsDedekindDomain (integralClosure R L) := integralClosure.isDedekindDomain R K L
  haveI : IsFractionRing (integralClosure R L) L := integralClosure.isFractionRing_of_finite_extension K L
  have hR : ∀ r : R, algebraMap R L r ∈ W := by
    intro r
    have : algebraMap R K r ∈ W.toSubring.comap (algebraMap K L) := by rw [hW]; exact ⟨r, rfl⟩
    exact this
  have hS : ∀ s : integralClosure R L, algebraMap (integralClosure R L) L s ∈ W :=
    fun s => GlobalTheory.ProlongConj.mem_of_isIntegral W hR s.2
  set c : L := algebraMap K L (algebraMap R K π) with hc_def
  have hc0 : c ≠ 0 := by
    rw [hc_def, map_ne_zero_iff _ (algebraMap K L).injective,
      map_ne_zero_iff _ (IsFractionRing.injective R K)]
    exact hπ.ne_zero
  have hcW : W.valuation c < 1 := by
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
    right
    intro hinv
    have h1 : (algebraMap R K π)⁻¹ ∈ W.toSubring.comap (algebraMap K L) := by
      change algebraMap K L _ ∈ W
      rw [map_inv₀]; exact hinv
    rw [hW] at h1
    obtain ⟨s, hs⟩ := h1
    apply hπ.not_isUnit
    refine IsUnit.of_mul_eq_one s (IsFractionRing.injective R K ?_)
    rw [map_mul, hs, map_one, mul_inv_cancel₀]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).1 (by rw [← hc_def]; exact hc0)
  set P0 := GlobalTheory.ProlongConj.primeBelow (integralClosure R L) W hS
  have hP0 : P0 ≠ ⊥ := by
    intro h
    have hm : algebraMap R (integralClosure R L) π ∈ P0 := by
      rw [GlobalTheory.ProlongConj.mem_primeBelow, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply R K L]
      exact hcW
    rw [h, Ideal.mem_bot] at hm
    apply hc0
    rw [hc_def, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R (integralClosure R L) L, hm,
      map_zero]
  let P : HeightOneSpectrum (integralClosure R L) := ⟨P0, inferInstance, hP0⟩
  have hWv := mem_iff_valuation_le_one L (integralClosure R L) W hS P rfl
  have hI : ∀ σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), σ ∈ inertia K W :=
    mem_inertia_of_mem_inertia K L (integralClosure R L) (fun _ _ => rfl) P W hWv
  have hlt : P.valuation L y < 1 := by
    rcases (ValuationSubring.mem_nonunits_iff_or W).1 hyW with h | h
    · rw [h, map_zero]; exact zero_lt_one
    · by_contra hge
      push_neg at hge
      apply h
      rw [hWv, map_inv₀]
      have h1 : P.valuation L y ≤ 1 := (hWv y).1 ((W.valuation_le_one_iff y).1 (le_of_lt (W.mem_nonunits_iff.1 hyW)))
      rw [le_antisymm h1 hge, inv_one]
  have key := valuation_le_of_fixed R K L P π hπ y (fun σ hσ => hy σ (hI σ hσ)) hlt
  rw [hWv, map_div₀]
  have hv0 : P.valuation L c ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  rw [div_le_one₀ (zero_lt_iff.2 hv0)]
  exact key

end GlobalTheory.InertiaUnram
