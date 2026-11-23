import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicRingEquivAdicCompletionPlaceUnramifiedDegreStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfRootCongrOfDerivUnitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowApplySubPowLtOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotMemSqOfDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotientEqOfPowSubSelfMemStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTotallyComplexOfPrimitiveRootThreeLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TotallyComplexOfRootQuadraticNegDiscStatement
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

noncomputable section
namespace GlobalTheory.UnrCycExt

variable {Ω : Type} [Field Ω]

theorem val_le_one_of_int {K : Type} [Field K] [NumberField K] [Algebra K Ω] (A : ValuationSubring Ω)
    (x : 𝓞 K) : A.valuation (algebraMap K Ω (x : K)) ≤ 1 := by
  refine (A.valuation_le_one_iff _).mpr (ReciprocityTheory.Gal.mem_of_isIntegral_int A ?_)
  exact x.2.map (IsScalarTower.toAlgHom ℤ K Ω)

def idealBelow (K : Type) [Field K] [NumberField K] [Algebra K Ω] (A : ValuationSubring Ω) : Ideal (𝓞 K) where
  carrier := {x | A.valuation (algebraMap K Ω (x : K)) < 1}
  add_mem' {a b} ha hb := by
    show A.valuation (algebraMap K Ω ((a + b : 𝓞 K) : K)) < 1
    simp only [map_add]
    exact Valuation.map_add_lt _ ha hb
  zero_mem' := by show A.valuation (algebraMap K Ω ((0 : 𝓞 K) : K)) < 1; simp
  smul_mem' c b hb := by
    show A.valuation (algebraMap K Ω ((c * b : 𝓞 K) : K)) < 1
    simp only [map_mul, Valuation.map_mul]
    calc A.valuation (algebraMap K Ω (c : K)) * A.valuation (algebraMap K Ω (b : K))
        ≤ 1 * A.valuation (algebraMap K Ω (b : K)) := mul_le_mul_left (val_le_one_of_int A c) _
      _ < 1 := by rw [one_mul]; exact hb

theorem mem_idealBelow {K : Type} [Field K] [NumberField K] [Algebra K Ω] {A : ValuationSubring Ω} {x : 𝓞 K} :
    x ∈ idealBelow K A ↔ A.valuation (algebraMap K Ω (x : K)) < 1 := Iff.rfl

instance isPrime_idealBelow (K : Type) [Field K] [NumberField K] [Algebra K Ω] (A : ValuationSubring Ω) :
    (idealBelow K A).IsPrime where
  ne_top' h := by
    have : (1 : 𝓞 K) ∈ idealBelow K A := h ▸ Submodule.mem_top
    rw [mem_idealBelow] at this
    simp at this
  mem_or_mem' {a b} hab := by
    rw [mem_idealBelow, mem_idealBelow]
    rw [mem_idealBelow] at hab
    by_contra hn
    simp only [not_or, not_lt] at hn
    have ha := le_antisymm (val_le_one_of_int A a) hn.1
    have hb := le_antisymm (val_le_one_of_int A b) hn.2
    simp only [map_mul, Valuation.map_mul, ha, hb, one_mul] at hab
    exact lt_irrefl _ hab

def placeBelow (K : Type) [Field K] [NumberField K] [Algebra K Ω] (A : ValuationSubring Ω) (x₀ : 𝓞 K)
    (h0 : x₀ ≠ 0) (hv : A.valuation (algebraMap K Ω (x₀ : K)) < 1) : HeightOneSpectrum (𝓞 K) where
  asIdeal := idealBelow K A
  isPrime := isPrime_idealBelow K A
  ne_bot h := h0 (by
    have : x₀ ∈ idealBelow K A := hv
    rw [h] at this
    simpa using this)

theorem isPlaceOver_placeBelow (K : Type) [Field K] [NumberField K] [Algebra K Ω] (A : ValuationSubring Ω)
    (x₀ : 𝓞 K) (h0 : x₀ ≠ 0) (hv : A.valuation (algebraMap K Ω (x₀ : K)) < 1) :
    IsPlaceOver A (placeBelow K A x₀ h0 hv) := fun _ => Iff.rfl

theorem fix_adjoin {E : Type} [Field E] [Algebra E Ω] (β : Ω) (hβ : IsIntegral E β) (τ : Ω ≃ₐ[E] Ω)
    (hτ : τ β = β) : ∀ x ∈ IntermediateField.adjoin E ({β} : Set Ω), τ x = x := by
  intro x hx
  rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβ.isAlgebraic] at hx
  have hle : Algebra.adjoin E ({β} : Set Ω) ≤ AlgHom.equalizer (τ : Ω →ₐ[E] Ω) (AlgHom.id E Ω) :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hτ)
  exact hle hx

theorem aeval_apply_eq_zero {E : Type} [Field E] [Algebra E Ω] (τ : Ω ≃ₐ[E] Ω) (f : ℤ[X]) {β : Ω}
    (h : aeval β f = 0) : aeval (τ β) f = 0 := by
  have := Polynomial.aeval_algHom_apply ((τ : Ω →ₐ[E] Ω).restrictScalars ℤ) β f
  simp only [AlgHom.coe_restrictScalars', AlgHom.coe_coe] at this
  exact this.trans (by rw [h, map_zero])

theorem adjoin_gen_eq_top (E : Type) [Field E] [Algebra E Ω] (β : Ω) (hβ : IsIntegral E β) :
    Algebra.adjoin E {(IntermediateField.AdjoinSimple.gen E β : IntermediateField.adjoin E ({β} : Set Ω))} = ⊤ := by
  apply Subalgebra.map_injective (f := (IntermediateField.adjoin E ({β} : Set Ω)).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Set.image_singleton, Algebra.map_top, IntermediateField.range_val,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβ.isAlgebraic]
  rfl

open IntermediateField in

theorem core {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] {g : ℕ} [Fact g.Prime]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
    (hg1 : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (hg2 : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2) (hN : normV w = g)
    (n : ℕ) (hn : 0 < n) (β : Ω) (f : ℤ[X]) (hf : f.Monic) (hfβ : aeval β f = 0)
    (hu : ¬ A.valuation (aeval β (derivative f)) < 1) (hq : A.valuation (β ^ (g ^ n) - β) < 1)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (g ^ n - 1)) (hζβ : ζ ∈ IntermediateField.adjoin E ({β} : Set Ω))
    (hTC : 3 ≤ g ^ n - 1 ∨ ∃ a b : ℤ, β ^ 2 + (a : Ω) * β + (b : Ω) = 0 ∧ a ^ 2 < 4 * b) :
    ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : IsTotallyComplex E') (_ : Algebra E E')
      (_ : Algebra E' Ω) (_ : IsScalarTower E E' Ω) (_ : IsAlgClosure E' Ω) (w' : HeightOneSpectrum (𝓞 E'))
      (_ : IsPlaceOver A w'), ((g : ℕ) : 𝓞 E') ∈ w'.asIdeal ∧ ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 ∧
      normV w' = g ^ n ∧ (∃ ζ : E', IsPrimitiveRoot ζ (g ^ n - 1)) ∧
      ∀ t ∈ Ine (F := E) A, ∀ e : E', t (algebraMap E' Ω e) = algebraMap E' Ω e := by
  classical
  have hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hgp : g.Prime := Fact.out
  have hq2 : 2 ≤ g ^ n := le_trans hgp.two_le (Nat.le_self_pow hn.ne' g)
  have hβint : IsIntegral ℤ β := ⟨f, hf, by rw [← aeval_def]; exact hfβ⟩
  have hβA : A.valuation β ≤ 1 :=
    (A.valuation_le_one_iff β).mpr (ReciprocityTheory.Gal.mem_of_isIntegral_int A hβint)
  have hβE : IsIntegral E β := Algebra.IsIntegral.isIntegral β
  let E' := IntermediateField.adjoin E ({β} : Set Ω)
  have hfd : FiniteDimensional E E' := IntermediateField.adjoin.finiteDimensional hβE
  have : FiniteDimensional ℚ E' := Module.Finite.trans E E'
  haveI hNF : NumberField E' := ⟨⟩
  haveI hAC' : IsAlgClosure E' Ω := ⟨hAC, Algebra.IsAlgebraic.tower_top (K := E) E'⟩

  have hroot : ∀ τ : Ω ≃ₐ[E] Ω, τ ∈ ReciprocityTheory.Gal.Dec (F := E) A → A.valuation (τ β - β) < 1 → τ β = β := by
    intro τ hτ hlt
    have hτA : A.valuation (τ β) ≤ 1 := by
      rw [A.valuation_le_one_iff, ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hτ, ← A.valuation_le_one_iff]
      exact hβA
    refine (GlobalTheory.T.eq_of_roots_congr_of_derivative_unit A f β (τ β) hβA hτA hfβ (aeval_apply_eq_zero τ f hfβ) hu ?_).symm
    rw [Valuation.map_sub_swap]; exact hlt

  have hine : ∀ t ∈ Ine (F := E) A, ∀ e : E', t (algebraMap E' Ω e) = algebraMap E' Ω e := by
    intro t ht e
    have htβ : t β = β := hroot t ht.1 (ht.2 β hβA)
    exact fix_adjoin β hβE t htβ _ e.2

  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob (F := E) h
  rw [hN] at hσ
  have hσn : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation ((σ ^ n) x - x ^ (g ^ n)) < 1 :=
    GlobalTheory.T.frobenius_pow_apply_sub_pow_lt_one A g σ hσ n
  have hσnD : σ ^ n ∈ ReciprocityTheory.Gal.Dec (F := E) A := Subgroup.pow_mem _ hσ.1 n
  have hσβ : (σ ^ n) β = β := by
    refine hroot _ hσnD ?_
    have e1 : (σ ^ n) β - β = ((σ ^ n) β - β ^ (g ^ n)) + (β ^ (g ^ n) - β) := by ring
    rw [e1]
    exact Valuation.map_add_lt _ (hσn β hβA) hq
  have hfix : ∀ x ∈ E', (σ ^ n) x = x := fix_adjoin β hβE (σ ^ n) hσβ
  have hpowq : ∀ y : 𝓞 E', A.valuation (algebraMap E' Ω ((y : E') ^ (g ^ n) - (y : E'))) < 1 := by
    intro y
    have hyA := val_le_one_of_int A y
    have := hσn _ hyA
    have hy2 : (σ ^ n) (algebraMap E' Ω (y : E')) = algebraMap E' Ω (y : E') := hfix _ (y : E').2
    rw [hy2] at this
    rw [map_sub, map_pow, Valuation.map_sub_swap]
    exact this

  have hg0 : ((g : ℕ) : 𝓞 E') ≠ 0 := by exact_mod_cast hgp.ne_zero
  have hgΩ : A.valuation ((g : ℕ) : Ω) < 1 := by
    have := (h ((g : ℕ) : 𝓞 E)).mpr hg1
    simpa using this
  have hgv : A.valuation (algebraMap E' Ω (((g : ℕ) : 𝓞 E') : E')) < 1 := by
    simpa using hgΩ
  let w' := placeBelow E' A ((g : ℕ) : 𝓞 E') hg0 hgv
  have hw' : IsPlaceOver A w' := isPlaceOver_placeBelow E' A _ hg0 hgv

  let ζE : E' := ⟨ζ, hζβ⟩
  have hζE : IsPrimitiveRoot ζE (g ^ n - 1) :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap E' Ω) hζ (algebraMap E' Ω).injective
  refine ⟨E', inferInstance, hNF, ?_, inferInstance, inferInstance, inferInstance, hAC', w', hw', hgv,
    ?_, ?_, ⟨ζE, hζE⟩, hine⟩
  ·
    rcases hTC with h3 | ⟨a, b, hab, hlt⟩
    · exact GlobalTheory.T.isTotallyComplex_of_primitiveRoot_three_le E' ζE (g ^ n - 1) hζE h3
    · refine GlobalTheory.T.isTotallyComplex_of_root_quadratic_neg_disc E' (AdjoinSimple.gen E β) a b ?_ hlt
      apply (algebraMap E' Ω).injective
      simpa using hab
  ·
    have hβ'int : IsIntegral ℤ (AdjoinSimple.gen E β) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ E' Ω) (algebraMap E' Ω).injective).mp hβint
    let β' : 𝓞 E' := ⟨AdjoinSimple.gen E β, hβ'int⟩
    have hmap : ∀ p : ℤ[X], algebraMap E' Ω ((aeval β' p : 𝓞 E') : E') = aeval β p := by
      intro p
      have h1 : ((aeval β' p : 𝓞 E') : E') = aeval (β' : E') p :=
        (Polynomial.aeval_algebraMap_apply E' β' p).symm
      rw [h1, ← Polynomial.aeval_algebraMap_apply]
      rfl
    have hfβ' : aeval β' f = 0 := by
      have h2 := hmap f
      rw [hfβ, ← map_zero (algebraMap E' Ω)] at h2
      exact_mod_cast (algebraMap E' Ω).injective h2
    have hover : ∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 E') x ∈ w'.asIdeal ↔ x ∈ w.asIdeal := by
      intro x
      rw [← h x]
      show A.valuation (algebraMap E' Ω ((algebraMap (𝓞 E) (𝓞 E') x : 𝓞 E') : E')) < 1 ↔ _
      rw [show ((algebraMap (𝓞 E) (𝓞 E') x : 𝓞 E') : E') = algebraMap E E' (x : E) from rfl,
        ← IsScalarTower.algebraMap_apply]
    have hder : aeval β' (derivative f) ∉ w'.asIdeal := fun hm => hu (by
      rw [← hmap]; exact hm)
    have := GlobalTheory.T.algebraMap_not_mem_sq_of_derivative_not_mem E E' w w' β' f hf hfβ' (adjoin_gen_eq_top E β hβE) hover hder _ hg2
    simpa using this
  ·
    show Nat.card (𝓞 E' ⧸ w'.asIdeal) = g ^ n
    have hqΩ : A.valuation ((g ^ n : ℕ) : Ω) < 1 := by
      rw [Nat.cast_pow, Valuation.map_pow]
      exact pow_lt_one₀ zero_le hgΩ hn.ne'
    have hN' : ¬ A.valuation (((g ^ n - 1 : ℕ)) : Ω) < 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one, ← neg_sub, Valuation.map_neg,
        Valuation.map_one_sub_of_lt _ hqΩ]
      exact lt_irrefl 1
    have hζint : IsIntegral ℤ ζE := hζE.isIntegral (by omega)
    let ζ' : 𝓞 E' := ⟨ζE, hζint⟩
    haveI : w'.asIdeal.IsMaximal := w'.isMaximal
    refine GlobalTheory.T.card_quotient_eq_of_pow_sub_self_mem' w'.asIdeal (g ^ n) ζ' hq2 ?_ ?_ ?_
    · apply FaithfulSMul.algebraMap_injective (𝓞 E') E'
      rw [map_pow, map_one]
      exact hζE.pow_eq_one
    · intro j hj0 hjq hm
      have hm1 : A.valuation (algebraMap E' Ω (algebraMap (𝓞 E') E' (ζ' ^ j - 1))) < 1 := hm
      rw [map_sub, map_pow, map_one, map_sub, map_pow, map_one] at hm1
      have hm' : A.valuation (ζ ^ j - 1) < 1 := hm1
      have := ReciprocityTheory.Gal.eq_of_pow_eq_one A hN' (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
        (one_pow _) hm'
      have hd := hζ.dvd_of_pow_eq_one j this
      exact absurd (Nat.le_of_dvd hj0 hd) (by omega)
    · intro y
      have := hpowq y
      show A.valuation (algebraMap E' Ω (((y ^ (g ^ n) - y : 𝓞 E')) : E')) < 1
      simpa using this

theorem exists_unramified_ext : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (g : ℕ)
    [Fact g.Prime] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (n : ℕ) (hn : 0 < n),
    ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : IsTotallyComplex E') (_ : Algebra E E')
      (_ : Algebra E' Ω) (_ : IsScalarTower E E' Ω) (_ : IsAlgClosure E' Ω) (w' : HeightOneSpectrum (𝓞 E'))
      (_ : IsPlaceOver A w'), ((g : ℕ) : 𝓞 E') ∈ w'.asIdeal ∧ ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 ∧
      normV w' = g ^ n ∧ (∃ ζ : E', IsPrimitiveRoot ζ (g ^ n - 1)) ∧
      ∀ t ∈ Ine (F := E) A, ∀ e : E', t (algebraMap E' Ω e) = algebraMap E' Ω e := by
  intro E Ω _ _ _ _ _ g _ A w h i hi n hn
  obtain ⟨hg1, hg2, hN⟩ := GlobalTheory.T.padic_ringEquiv_adicCompletion_place_unramified_degree_one E g w i hi
  have hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hgp : g.Prime := Fact.out
  have hgΩ : A.valuation ((g : ℕ) : Ω) < 1 := by
    have := (h ((g : ℕ) : 𝓞 E)).mpr hg1
    simpa using this
  by_cases h4 : 4 ≤ g ^ n
  ·
    have hqΩ : A.valuation ((g ^ n : ℕ) : Ω) < 1 := by
      rw [Nat.cast_pow, Valuation.map_pow]; exact pow_lt_one₀ zero_le hgΩ hn.ne'
    have hN' : A.valuation (((g ^ n - 1 : ℕ)) : Ω) = 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one, ← neg_sub, Valuation.map_neg,
        Valuation.map_one_sub_of_lt _ hqΩ]
    haveI : NeZero (((g ^ n - 1 : ℕ)) : Ω) := ⟨by exact_mod_cast (show g ^ n - 1 ≠ 0 by omega)⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (g ^ n - 1)
    have hζ1 : A.valuation ζ = 1 := ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A (by omega) hζ.pow_eq_one
    refine GlobalTheory.UnrCycExt.core h hg1 hg2 hN n hn ζ (X ^ (g ^ n - 1) - C 1) (monic_X_pow_sub_C 1 (by omega)) ?_ ?_ ?_
      ζ hζ (IntermediateField.mem_adjoin_simple_self E ζ) (Or.inl (by omega))
    · simp [hζ.pow_eq_one]
    · rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_mul, aeval_C, map_pow, aeval_X,
        Valuation.map_mul, Valuation.map_pow, hζ1, one_pow, mul_one]
      have e : algebraMap ℤ Ω (((g ^ n - 1 : ℕ) : ℤ)) = (((g ^ n - 1 : ℕ)) : Ω) := by simp
      rw [e, hN']
      exact lt_irrefl 1
    · have e : ζ ^ (g ^ n) = ζ := by
        rw [show g ^ n = (g ^ n - 1) + 1 by omega, pow_succ, hζ.pow_eq_one, one_mul]
      rw [e, sub_self, Valuation.map_zero]
      exact zero_lt_one
  · have hn1 : n = 1 := by
      by_contra hne
      have h2 : g ^ 2 ≤ g ^ n := Nat.pow_le_pow_right hgp.pos (by omega)
      have h3 : 4 ≤ g ^ 2 := by nlinarith [hgp.two_le]
      omega
    subst hn1
    have hg3 : g < 4 := by simpa using (show ¬ 4 ≤ g ^ 1 from h4)
    have hg23 : g = 2 ∨ g = 3 := by
      have := hgp.two_le
      omega
    rcases hg23 with rfl | rfl
    ·
      let f : ℤ[X] := X ^ 2 - X + C 2
      have hfm : f.Monic := by
        show (X ^ 2 - X + C 2 : ℤ[X]).Monic
        monicity!
      have hfd : (f.map (algebraMap ℤ Ω)).degree ≠ 0 := by
        rw [degree_map_eq_of_leadingCoeff_ne_zero _ (by rw [hfm.leadingCoeff]; simp)]
        have e : (X ^ 2 - X + C 2 : ℤ[X]).degree = 2 := by compute_degree!
        show (X ^ 2 - X + C 2 : ℤ[X]).degree ≠ 0
        rw [e]; decide
      obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hfd
      have hαf : aeval α f = 0 := by rw [aeval_def, ← eval_map]; exact hα
      have hα' : α ^ 2 - α + 2 = 0 := by simpa [f, map_ofNat] using hαf
      have h2Ω : A.valuation (2 : Ω) < 1 := by simpa using hgΩ
      refine GlobalTheory.UnrCycExt.core h hg1 hg2 hN 1 hn α f hfm hαf ?_ ?_ 1 (by simpa using IsPrimitiveRoot.one)
        (IntermediateField.one_mem _) (Or.inr ⟨-1, 2, by rw [← hα']; push_cast; ring, by norm_num⟩)
      · have hd : aeval α (derivative f) = -(1 - 2 * α) := by
          simp [f, derivative_X_pow, map_ofNat]
        rw [hd, Valuation.map_neg]
        have hαA : A.valuation α ≤ 1 := (A.valuation_le_one_iff α).mpr
          (ReciprocityTheory.Gal.mem_of_isIntegral_int A ⟨f, hfm, by rw [← aeval_def]; exact hαf⟩)
        have h2α : A.valuation (2 * α) < 1 := by
          rw [Valuation.map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_right' hαA) h2Ω
        rw [Valuation.map_one_sub_of_lt _ h2α]
        exact lt_irrefl 1
      · have e : α ^ (2 ^ 1) - α = -2 := by linear_combination hα'
        rw [e, Valuation.map_neg]
        exact h2Ω
    ·
      let f : ℤ[X] := X ^ 2 + C 2
      have hfm : f.Monic := by
        show (X ^ 2 + C 2 : ℤ[X]).Monic
        monicity!
      have hfd : (f.map (algebraMap ℤ Ω)).degree ≠ 0 := by
        rw [degree_map_eq_of_leadingCoeff_ne_zero _ (by rw [hfm.leadingCoeff]; simp)]
        have e : (X ^ 2 + C 2 : ℤ[X]).degree = 2 := by compute_degree!
        show (X ^ 2 + C 2 : ℤ[X]).degree ≠ 0
        rw [e]; decide
      obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hfd
      have hαf : aeval α f = 0 := by rw [aeval_def, ← eval_map]; exact hα
      have hα' : α ^ 2 + 2 = 0 := by simpa [f, map_ofNat] using hαf
      have h3Ω : A.valuation (3 : Ω) < 1 := by simpa using hgΩ
      have h2Ω : A.valuation (2 : Ω) = 1 := by
        rw [show (2 : Ω) = -(1 - 3) by ring, Valuation.map_neg, Valuation.map_one_sub_of_lt _ h3Ω]
      have hαA : A.valuation α ≤ 1 := (A.valuation_le_one_iff α).mpr
        (ReciprocityTheory.Gal.mem_of_isIntegral_int A ⟨f, hfm, by rw [← aeval_def]; exact hαf⟩)
      refine GlobalTheory.UnrCycExt.core h hg1 hg2 hN 1 hn α f hfm hαf ?_ ?_ (-1)
        (by simpa using IsPrimitiveRoot.neg_one 0 (by norm_num))
        (neg_mem (IntermediateField.one_mem _)) (Or.inr ⟨0, 2, by rw [← hα']; push_cast; ring, by norm_num⟩)
      · have hd : aeval α (derivative f) = 2 * α := by
          simp [f, derivative_X_pow, map_ofNat]
        rw [hd]
        intro hlt
        have hsq := pow_lt_one₀ zero_le hlt (two_ne_zero)
        rw [← Valuation.map_pow, show (2 * α) ^ 2 = -(2 * 2 * 2) by linear_combination 4 * hα',
          Valuation.map_neg, Valuation.map_mul, Valuation.map_mul, h2Ω] at hsq
        simp at hsq
      · have e : α ^ (3 ^ 1) - α = -(3 * α) := by linear_combination α * hα'
        rw [e, Valuation.map_neg, Valuation.map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' hαA) h3Ω

end GlobalTheory.UnrCycExt
