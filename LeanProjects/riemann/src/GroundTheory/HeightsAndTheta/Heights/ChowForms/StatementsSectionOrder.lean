import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LineInhabitant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Chart

variable {F : Type} [Field F] {n : ℕ}

def chartIncIdeal (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) :
    Ideal (MvPolynomial (Fin n ⊕ Fin e × Fin n) F) :=
  (I ⊔ Ideal.span {linForm t - 1}).map (rename Sum.inl) ⊔
    Ideal.span (Set.range fun i : Fin e => ∑ m, X (Sum.inr (i, m)) * X (Sum.inl m))

def ChartInc (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) : Type :=
  MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e

instance (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) : CommRing (ChartInc I t e) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e))

def chartIncHom (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) :
    MvPolynomial (Fin e × Fin n) F →+* ChartInc I t e :=
  (Ideal.Quotient.mk (chartIncIdeal I t e)).comp (rename Sum.inr).toRingHom

instance (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) :
    Algebra (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) :=
  (chartIncHom I t e).toAlgebra

def chartX (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) :
    MvPolynomial (Fin n) F →+* ChartInc I t e :=
  (Ideal.Quotient.mk (chartIncIdeal I t e)).comp (rename Sum.inl).toRingHom

def chartLin (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ) (u : Fin n → F) :
    ChartInc I t e :=
  chartX I t e (linForm u)

abbrev ChartLoc (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime] : Type :=
  Localization (Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl)

def chartIdeal (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime] (W : Ideal (MvPolynomial (Fin n) F)) :
    Ideal (ChartLoc I t e p) :=
  (W.map (chartX I t e)).map (algebraMap (ChartInc I t e) (ChartLoc I t e p))

end Chart

def IncIdealBelow.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F), IsProjPrime I → IsChowForm I (e + 1) f →
      incIdeal I e = ⊥

def SpecFirstMemIncIdeal.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F), IsChowForm I (e + 1) f → I ≤ W →
      linForm t ∈ W → specFirst f t ∈ incIdeal W e

def ChartChoice.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (q : MvPolynomial (Fin e × Fin n) F),
    IsProjPrime I → IsChowForm I (e + 1) f → Prime q → ∃ t : Fin n → F, ¬ q ∣ specFirst f t

def SpecFirstNe.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → specFirst f u ≠ 0

def LocalizationPrimeDVR.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R]
    (q : R) (p : Ideal R) [p.IsPrime], Prime q → p = Ideal.span {q} →
      IsDiscreteValuationRing (Localization.AtPrime p)

def EmultiplicityOrd.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R]
    (q x : R) (p : Ideal R) [p.IsPrime], Prime q → p = Ideal.span {q} → x ≠ 0 →
      emultiplicity q x = Ring.ord (Localization.AtPrime p) (algebraMap R _ x)

def ChartFinite.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → specFirst f t ∉ p →
      Module.Finite (Localization.AtPrime p) (ChartLoc I t e p)

def ChartLocDomain.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm t ∉ I →
      IsDomain (ChartLoc I t e p) ∧
        Function.Injective (algebraMap (Localization.AtPrime p) (ChartLoc I t e p)) ∧
        ∀ u : Fin n → F, linForm u ∉ I →
          algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u) ≠ 0

def ChartNorm.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → (p = ⊥ ∨ ∃ q, Prime q ∧ p = Ideal.span {q}) →
      specFirst f t ∉ p → ∀ u : Fin n → F,
        algebraMap _ (Localization.AtPrime p) (specFirst f u) =
          algebraMap _ (Localization.AtPrime p) (specFirst f t) *
            LinearMap.det (LinearMap.mulLeft (Localization.AtPrime p)
              (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u)))

open Classical in

def ChartLength.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → Prime q → p = Ideal.span {q} →
      ¬ q ∣ specFirst f t →
        Module.length (Localization.AtPrime p) (ChartLoc I t e p ⧸ LinearMap.range
            (LinearMap.mulLeft (Localization.AtPrime p)
              (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u)))) =
          ∑ W ∈ (divCycle I u).support with Ideal.span {q} = incIdeal W e,
            ((divCycle I u W : ℕ) : ℕ∞)

def LengthFiniteAlgebra.Statement : Prop :=
  ∀ (O B : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing B] [Algebra O B]
    [Module.Finite O B] (θ : B),
    Module.length O (B ⧸ LinearMap.range (LinearMap.mulLeft O θ)) =
      ∑ᶠ 𝔓 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔓.asIdeal) (algebraMap B _ θ) * Module.length O (B ⧸ 𝔓.asIdeal)

def ChartMaxIdeals.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → Prime q → p = Ideal.span {q} →
      ¬ q ∣ specFirst f t →
        Set.BijOn (chartIdeal I t e p)
          {W | W ∈ (divCycle I u).support ∧ Ideal.span {q} = incIdeal W e}
          {𝔓 | 𝔓.IsMaximal ∧
            algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u) ∈ 𝔓}

def ChartLocalOrder.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → Prime q → p = Ideal.span {q} →
      ¬ q ∣ specFirst f t → W ∈ relComps (I ⊔ Ideal.span {linForm u}) → q ∈ incIdeal W e →
        linForm t ∉ W →
          ∃ _ : (chartIdeal I t e p W).IsPrime,
            Ring.ord (Localization.AtPrime (chartIdeal I t e p W))
                (algebraMap (ChartLoc I t e p) _
                  (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u))) =
              (localMult (I ⊔ Ideal.span {linForm u}) W : ℕ∞)

def ChartResidueDegree.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → Prime q → p = Ideal.span {q} →
      ¬ q ∣ specFirst f t → W ∈ relComps (I ⊔ Ideal.span {linForm u}) → q ∈ incIdeal W e →
        linForm t ∉ W →
          Module.length (Localization.AtPrime p) (ChartLoc I t e p ⧸ chartIdeal I t e p W) = 1

section Inhabitants

open LineChowForm

def uLine : Fin 2 → ℚ := fun j => if j = 0 then 1 else 0

def tLine : Fin 2 → ℚ := fun j => if j = 0 then 0 else 1

def qLine : MvPolynomial (Fin 1 × Fin 2) ℚ := X (0, 1)

theorem linForm_uLine : linForm uLine = (X 0 : MvPolynomial (Fin 2) ℚ) := by
  simp [linForm, uLine]

theorem linForm_tLine : linForm tLine = (X 1 : MvPolynomial (Fin 2) ℚ) := by
  simp [linForm, tLine, Fin.sum_univ_two]

theorem prime_qLine : Prime qLine := X_prime

theorem isPrime_span_qLine : (Ideal.span {qLine}).IsPrime :=
  (Ideal.span_singleton_prime prime_qLine.ne_zero).mpr prime_qLine

theorem specialize_det_lineForm_eq :
    specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine = -X (0, 0) := by
  simp [specFirst, D2, specFirstVar, tLine]
  rfl

theorem not_dvd_specFirst_tLine :
    ¬ qLine ∣ specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine := by
  rw [specialize_det_lineForm_eq, dvd_neg, qLine, X_dvd_X]
  decide

theorem specFirst_tLine_not_mem :
    specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine ∉ Ideal.span {qLine} := by
  rw [Ideal.mem_span_singleton]
  exact not_dvd_specFirst_tLine

theorem qLine_mem_incIdeal : qLine ∈ incIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 := by
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]
  rintro v ⟨x, hx0, hxW, hv⟩
  have h0 : x 0 = 0 := by simpa using hxW (X 0) (Ideal.mem_span_singleton_self _)
  have h1 : x 1 ≠ 0 := fun h1 => hx0 (funext fun j => by fin_cases j <;> simp [h0, h1])
  have h := hv 0
  rw [Fin.sum_univ_two, h0, mul_zero, zero_add] at h
  simp [qLine, (mul_eq_zero.mp h).resolve_right h1]

theorem linearFormLine_not_mem_span_X0 : linForm tLine ∉ Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} := by
  rw [linForm_tLine, Ideal.mem_span_singleton, X_dvd_X]
  decide

theorem linForm_tLine_not_mem_bot : linForm tLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) := by
  rw [linForm_tLine, Ideal.mem_bot]
  exact X_ne_zero 1

theorem linForm_uLine_not_mem_bot : linForm uLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) :=
  linForm_line

theorem line_chow :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) :=
  ⟨isProjPrime_line, isChowForm_line⟩

theorem IncIdealBelow.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) :=
  line_chow

theorem SpecFirstMemIncIdeal.hypotheses_inhabited :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ≤ Ideal.span {X 0} ∧
      linForm uLine ∈ Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} :=
  ⟨isChowForm_line, bot_le, by rw [linForm_uLine]; exact Ideal.mem_span_singleton_self _⟩

theorem ChartChoice.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      Prime qLine :=
  ⟨isProjPrime_line, isChowForm_line, prime_qLine⟩

theorem SpecFirstNe.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      linForm uLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) :=
  ⟨isProjPrime_line, isChowForm_line, linForm_uLine_not_mem_bot⟩

theorem LocalizationPrimeDVR.hypotheses_inhabited :
    (Ideal.span {(2 : ℤ)}).IsPrime ∧ Prime (2 : ℤ) :=
  ⟨(Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two, Int.prime_two⟩

theorem EmultiplicityOrd.hypotheses_inhabited :
    (Ideal.span {(2 : ℤ)}).IsPrime ∧ Prime (2 : ℤ) ∧ (4 : ℤ) ≠ 0 :=
  ⟨(Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two, Int.prime_two, by norm_num⟩

theorem ChartFinite.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      (Ideal.span {qLine}).IsPrime ∧
      specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine ∉ Ideal.span {qLine} :=
  ⟨isProjPrime_line, isChowForm_line, isPrime_span_qLine, specFirst_tLine_not_mem⟩

theorem ChartLocDomain.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      (Ideal.span {qLine}).IsPrime ∧ linForm tLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) :=
  ⟨isProjPrime_line, isChowForm_line, isPrime_span_qLine, linForm_tLine_not_mem_bot⟩

theorem ChartNorm.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      (Ideal.span {qLine}).IsPrime ∧
      (Ideal.span {qLine} = ⊥ ∨ ∃ q, Prime q ∧ Ideal.span {qLine} = Ideal.span {q}) ∧
      specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine ∉ Ideal.span {qLine} :=
  ⟨isProjPrime_line, isChowForm_line, isPrime_span_qLine, Or.inr ⟨qLine, prime_qLine, rfl⟩,
    specFirst_tLine_not_mem⟩

theorem line_section :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      linForm uLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧ Prime qLine ∧
      (Ideal.span {qLine}).IsPrime ∧
      ¬ qLine ∣ specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine :=
  ⟨isProjPrime_line, isChowForm_line, linForm_uLine_not_mem_bot, prime_qLine, isPrime_span_qLine,
    not_dvd_specFirst_tLine⟩

theorem ChartLength.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      linForm uLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧ Prime qLine ∧
      (Ideal.span {qLine}).IsPrime ∧
      ¬ qLine ∣ specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine :=
  line_section

theorem ChartMaxIdeals.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      linForm uLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧ Prime qLine ∧
      (Ideal.span {qLine}).IsPrime ∧
      ¬ qLine ∣ specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine :=
  line_section

theorem line_component :
    Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} ∈
        relComps ((⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ⊔ Ideal.span {linForm uLine}) ∧
      qLine ∈ incIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 ∧
      linForm tLine ∉ Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} :=
  ⟨span_X_zero_mem_relComps ℚ, qLine_mem_incIdeal, linearFormLine_not_mem_span_X0⟩

theorem ChartLocalOrder.hypotheses_inhabited :
    (IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      linForm uLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧ Prime qLine ∧
      (Ideal.span {qLine}).IsPrime ∧
      ¬ qLine ∣ specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine) ∧
    (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} ∈
        relComps ((⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ⊔ Ideal.span {linForm uLine}) ∧
      qLine ∈ incIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 ∧
      linForm tLine ∉ Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) :=
  ⟨line_section, line_component⟩

theorem ChartResidueDegree.hypotheses_inhabited :
    (IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      linForm uLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧ Prime qLine ∧
      (Ideal.span {qLine}).IsPrime ∧
      ¬ qLine ∣ specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine) ∧
    (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} ∈
        relComps ((⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ⊔ Ideal.span {linForm uLine}) ∧
      qLine ∈ incIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 ∧
      linForm tLine ∉ Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) :=
  ⟨line_section, line_component⟩

theorem LengthFiniteAlgebra.hypotheses_inhabited :
    IsLocalRing ℤ_[2] ∧ IsNoetherianRing ℤ_[2] ∧ Module.Finite ℤ_[2] ℤ_[2] :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights
