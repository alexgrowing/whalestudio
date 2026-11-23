import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Objects

variable {F : Type*} [Field F] {n : ℕ}

def incIdeal (P : Ideal (MvPolynomial (Fin n) F)) (k : ℕ) : Ideal (MvPolynomial (Fin k × Fin n) F) :=
  ⨅ v ∈ incidence P k,
    RingHom.ker (aeval v : MvPolynomial (Fin k × Fin n) F →ₐ[F] AlgebraicClosure F)

def genPt (P : Ideal (MvPolynomial (Fin n) F)) : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P) :=
  fun j => algebraMap (MvPolynomial (Fin n) F ⧸ P) _ (Ideal.Quotient.mk P (X j))

def genSubst {R : Type*} [CommRing R] {k : ℕ} (ζ c : Fin n → R) (ij : Fin k × Fin n) :
    MvPolynomial (Fin k × Fin n) R :=
  X ij - (∑ l, X (ij.1, l) * C (ζ l)) * C (c ij.2)

end Objects

def FGNullstellensatz.Statement : Prop :=
  ∀ (F : Type) [Field F] (D : Type) [CommRing D] [IsReduced D] [Algebra F D]
    [Algebra.FiniteType F D] (r : D), (∀ φ : D →ₐ[F] AlgebraicClosure F, φ r = 0) → r = 0

def ProjNullstellensatz.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (P : Ideal (MvPolynomial (Fin n) F)), IsProjPrime P →
    ∃ x : Fin n → AlgebraicClosure F, x ≠ 0 ∧ ∀ g ∈ P, aeval x g = 0

def IncidenceGeneric.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
    (c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P)), ∑ j, c j * genPt P j = 1 →
      ∀ g : MvPolynomial (Fin k × Fin n) F,
        g ∈ incIdeal P k ↔ aeval (genSubst (genPt P) c) g = 0

def IncIdealPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (P : Ideal (MvPolynomial (Fin n) F)), P.IsPrime → IsRelevant P →
    (incIdeal P k).IsPrime

def ChowFormMultiHomog.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (P : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin k × Fin n) F), IsProjPrime P → IsChowForm P k f →
      ∃ δ, 1 ≤ δ ∧ IsMultiHomog δ f

def ConeDimOfChowForm.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (P : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin k × Fin n) F), IsProjPrime P → IsChowForm P k f →
      ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ((k : ℕ) : WithBot ℕ∞)

def MinimalPrimeHomog.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (J W : Ideal (MvPolynomial (Fin n) F)), IsHomogIdeal J →
    W ∈ J.minimalPrimes → IsHomogIdeal W

def ConeDimComponent.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F)) (u : Fin n → F),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((e + 1 : ℕ) : WithBot ℕ∞) →
      linForm u ∉ I → W ∈ relComps (I ⊔ Ideal.span {linForm u}) →
        IsProjPrime W ∧ ringKrullDim (MvPolynomial (Fin n) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞)

def ChowFormExists.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (P : Ideal (MvPolynomial (Fin n) F)), IsProjPrime P →
    ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ((k : ℕ) : WithBot ℕ∞) → ∃ g, IsChowForm P k g

def LengthQuotientDet.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (M : Type) [AddCommGroup M]
    [Module O M] [Module.Free O M] [Module.Finite O M] (φ : M →ₗ[O] M), LinearMap.det φ ≠ 0 →
      Module.length O (M ⧸ LinearMap.range φ) = Ring.ord O (LinearMap.det φ)

def OrdPolynomialLocalization.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (σ : Type) (p : Ideal R) [p.IsPrime]
    [(Ideal.map (C : R →+* MvPolynomial σ R) p).IsPrime] (x : R),
    Ring.ord (Localization.AtPrime (Ideal.map (C : R →+* MvPolynomial σ R) p))
        (algebraMap (MvPolynomial σ R) _ (C x)) =
      Ring.ord (Localization.AtPrime p) (algebraMap R _ x)

open Classical in

def SectionOrder.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I →
      specFirst f u ≠ 0 ∧ ∀ q : MvPolynomial (Fin e × Fin n) F, Irreducible q →
        emultiplicity q (specFirst f u) =
          ∑ W ∈ (divCycle I u).support with Ideal.span {q} = incIdeal W e,
            ((divCycle I u W : ℕ) : ℕ∞)

section Inhabitants

theorem FGNullstellensatz.hypotheses_inhabited : IsReduced ℚ ∧ Algebra.FiniteType ℚ ℚ :=
  ⟨inferInstance, inferInstance⟩

theorem ProjNullstellensatz.hypotheses_inhabited : IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) :=
  isProjPrime_point ℚ

theorem genPt_bot_zero_ne_zero : genPt (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 0 ≠ 0 := by
  unfold genPt
  rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
  exact X_ne_zero 0

theorem IncidenceGeneric.hypotheses_inhabited :
    (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)).IsPrime ∧
      ∑ j, (fun _ => (genPt (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 0)⁻¹) j *
        genPt (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) j = 1 := by
  refine ⟨Ideal.isPrime_bot, ?_⟩
  rw [Fin.sum_univ_one]
  exact inv_mul_cancel₀ genPt_bot_zero_ne_zero

theorem IncIdealPrime.hypotheses_inhabited :
    (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)).IsPrime ∧ IsRelevant (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) :=
  ⟨Ideal.isPrime_bot, (isProjPrime_point ℚ).isRelevant⟩

theorem ChowFormMultiHomog.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 1 (X (0, 0)) :=
  ⟨isProjPrime_point ℚ, isChowForm_point ℚ⟩

theorem ConeDimOfChowForm.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 1 (X (0, 0)) :=
  ⟨isProjPrime_point ℚ, isChowForm_point ℚ⟩

theorem MinimalPrimeHomog.hypotheses_inhabited :
    IsHomogIdeal (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∈ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)).minimalPrimes :=
  ⟨(isProjPrime_point ℚ).isHomog, by
    have : (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)).IsPrime := Ideal.isPrime_bot
    rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl⟩

theorem ringKrullDim_quot_bot (F : Type*) [Field F] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) F ⧸ (⊥ : Ideal (MvPolynomial (Fin n) F))) =
      ((n : ℕ) : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (MvPolynomial (Fin n) F)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem span_X_zero_mem_relComps (F : Type*) [Field F] :
    Ideal.span {X 0} ∈ relComps ((⊥ : Ideal (MvPolynomial (Fin 2) F)) ⊔
      Ideal.span {linForm (fun j : Fin 2 => if j = 0 then (1 : F) else 0)}) := by
  have hl : linForm (fun j : Fin 2 => if j = 0 then (1 : F) else 0) = X 0 := by
    simp [linForm]
  rw [hl, bot_sup_eq]
  have : (Ideal.span {(X 0 : MvPolynomial (Fin 2) F)}).IsPrime :=
    (Ideal.span_singleton_prime (X_ne_zero 0)).mpr X_prime
  refine ⟨by rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl, 1, ?_⟩
  rw [Ideal.mem_span_singleton]
  intro h
  have := (X_dvd_X (R := F)).mp h
  exact absurd this (by decide)

theorem ConeDimComponent.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      ringKrullDim (MvPolynomial (Fin 2) ℚ ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ))) =
        ((1 + 1 : ℕ) : WithBot ℕ∞) ∧
      linForm (fun j : Fin 2 => if j = 0 then (1 : ℚ) else 0) ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      Ideal.span {X 0} ∈ relComps ((⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ⊔
        Ideal.span {linForm (fun j : Fin 2 => if j = 0 then (1 : ℚ) else 0)}) := by
  refine ⟨⟨Ideal.isPrime_bot, fun f hf d => ?_, ⟨0, ?_⟩⟩, ringKrullDim_quot_bot ℚ 2, ?_,
    span_X_zero_mem_relComps ℚ⟩
  · rw [Ideal.mem_bot] at hf ⊢; simp [hf]
  · rw [Ideal.mem_bot]; exact X_ne_zero 0
  · rw [Ideal.mem_bot]; simp [linForm, X_ne_zero]

theorem ChowFormExists.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      ringKrullDim (MvPolynomial (Fin 1) ℚ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))) =
        ((1 : ℕ) : WithBot ℕ∞) :=
  ⟨isProjPrime_point ℚ, ringKrullDim_quot_bot ℚ 1⟩

theorem LengthQuotientDet.hypotheses_inhabited :
    LinearMap.det ((2 : ℤ_[2]) • LinearMap.id : ℤ_[2] →ₗ[ℤ_[2]] ℤ_[2]) ≠ 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_self, pow_one]
  exact two_ne_zero

theorem OrdPolynomialLocalization.hypotheses_inhabited :
    (⊥ : Ideal ℤ).IsPrime ∧ (Ideal.map (C : ℤ →+* MvPolynomial Unit ℤ) ⊥).IsPrime := by
  rw [Ideal.map_bot]
  exact ⟨Ideal.isPrime_bot, Ideal.isPrime_bot⟩

theorem SectionOrder.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) ∧
      linForm (fun _ => (1 : ℚ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) :=
  ChowFormSection.hypotheses_inhabited

end Inhabitants

end

end GroundTheory.Heights₂.Heights
