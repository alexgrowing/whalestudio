import Mathlib

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.RelativeDifferentValues

noncomputable def idealVal_vp {E : Type} [Field E] [NumberField E] (p : ℕ)
    (P : HeightOneSpectrum (𝓞 E)) (I : Ideal (𝓞 E)) : ℚ :=
  (multiplicity P.asIdeal I : ℚ) / (multiplicity P.asIdeal (Ideal.span {(p : 𝓞 E)}) : ℚ)

noncomputable def vd_vp {E : Type} [Field E] [NumberField E] (p : ℕ)
    (P : HeightOneSpectrum (𝓞 E)) : ℚ :=
  idealVal_vp p P (differentIdeal ℤ (𝓞 E))

noncomputable def rootDiscrVal_vp (E : Type) [Field E] [NumberField E] (p : ℕ) : ℚ :=
  (padicValInt p (discr E) : ℚ) / (Module.finrank ℚ E : ℚ)

def DiscrFormula : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ), p.Prime →
    ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → vd_vp p P = rootDiscrVal_vp E p

def hostGens (e q₁ d : ℕ) : Set ℂ :=
  {Complex.exp (2 * Real.pi * Complex.I / ((4 * 2 ^ e : ℕ) : ℂ)) +
      (Complex.exp (2 * Real.pi * Complex.I / ((4 * 2 ^ e : ℕ) : ℂ)))⁻¹,
    Complex.I * (Real.sqrt q₁ : ℂ), Complex.I * (Real.sqrt d : ℂ)}

noncomputable def hostField (e q₁ d : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (hostGens e q₁ d)

def HostNumbers (e q₁ d : ℕ) : Prop :=
  4 ≤ 2 ^ e ∧ q₁.Prime ∧ q₁ % 8 = 3 ∧ 11 ≤ q₁ ∧ d.Prime ∧ d % 16 = 7 ∧
    jacobiSym (-(d : ℤ)) q₁ = 1

def IsHostField (E : Type) [Field E] (e q₁ d : ℕ) : Prop :=
  Nonempty (E ≃+* hostField e q₁ d)

def HostValues : Prop :=
  ∀ (e q₁ d : ℕ), HostNumbers e q₁ d →
    ∀ (E : Type) [Field E] [NumberField E], IsHostField E e q₁ d →
      (∀ P : HeightOneSpectrum (𝓞 E), ((2 : ℕ) : 𝓞 E) ∈ P.asIdeal →
        vd_vp 2 P = (e : ℚ) + 1 - 1 / (2 : ℚ) ^ e) ∧
      (∀ P : HeightOneSpectrum (𝓞 E), (q₁ : 𝓞 E) ∈ P.asIdeal → vd_vp q₁ P = 1 / 2) ∧
      (∀ P : HeightOneSpectrum (𝓞 E), (d : 𝓞 E) ∈ P.asIdeal → vd_vp d P = 1 / 2)

def HostDiscrValues : Prop :=
  ∀ (e q₁ d : ℕ), HostNumbers e q₁ d →
    ∀ (E : Type) [Field E] [NumberField E], IsHostField E e q₁ d →
      rootDiscrVal_vp E 2 = (e : ℚ) + 1 - 1 / (2 : ℚ) ^ e ∧
      rootDiscrVal_vp E q₁ = 1 / 2 ∧ rootDiscrVal_vp E d = 1 / 2

def HostRelativeValues : Prop :=
  ∀ (e q₁ d : ℕ), HostNumbers e q₁ d →
    ∀ (E : Type) [Field E] [NumberField E], IsHostField E e q₁ d →
    ∀ (K : Type) [Field K] [NumberField K] [Algebra K E],
      Module.finrank ℚ K = 2 → (∃ b : K, b ^ 2 = -(d : K)) →
      (∀ P : HeightOneSpectrum (𝓞 E), ((2 : ℕ) : 𝓞 E) ∈ P.asIdeal →
        idealVal_vp 2 P (differentIdeal (𝓞 K) (𝓞 E)) = vd_vp 2 P) ∧
      (∀ P : HeightOneSpectrum (𝓞 E), (q₁ : 𝓞 E) ∈ P.asIdeal →
        idealVal_vp q₁ P (differentIdeal (𝓞 K) (𝓞 E)) = 1 / 2) ∧
      (∀ P : HeightOneSpectrum (𝓞 E), (d : 𝓞 E) ∈ P.asIdeal →
        idealVal_vp d P (differentIdeal (𝓞 K) (𝓞 E)) = 0)

def DifferentExponents : Prop := DiscrFormula ∧ HostValues

theorem finite_of_ne_bot {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) : FiniteMultiplicity P.asIdeal I :=
  FiniteMultiplicity.of_prime_left P.prime hI

theorem finite_different {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    FiniteMultiplicity P.asIdeal (differentIdeal ℤ (𝓞 E)) :=
  finite_of_ne_bot P differentIdeal_ne_bot

theorem finite_span {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    {p : ℕ} (hp : p.Prime) : FiniteMultiplicity P.asIdeal (Ideal.span {(p : 𝓞 E)}) :=
  finite_of_ne_bot P (by simpa using hp.ne_zero)

theorem multiplicity_span_pos {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    {p : ℕ} (h : (p : 𝓞 E) ∈ P.asIdeal) :
    0 < multiplicity P.asIdeal (Ideal.span {(p : 𝓞 E)}) :=
  multiplicity_pos_of_dvd (Ideal.dvd_span_singleton.mpr h)

theorem idealVal_vp_self {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    {p : ℕ} (h : (p : 𝓞 E) ∈ P.asIdeal) : idealVal_vp p P (Ideal.span {(p : 𝓞 E)}) = 1 :=
  div_self (by exact_mod_cast (multiplicity_span_pos P h).ne')

theorem isIntegral_I_mul_sqrt (m : ℕ) : IsIntegral ℚ (Complex.I * (Real.sqrt m : ℂ)) := by
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  have : (Complex.I * (Real.sqrt m : ℂ)) ^ 2 = algebraMap ℚ ℂ (-(m : ℚ)) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    simp
  rw [this]
  exact isIntegral_algebraMap

instance (e q₁ d : ℕ) : NumberField (hostField e q₁ d) where
  to_finiteDimensional := by
    have : Finite (hostGens e q₁ d) := by
      unfold hostGens; infer_instance
    refine IntermediateField.finiteDimensional_adjoin ?_
    have hz : IsIntegral ℚ (Complex.exp (2 * Real.pi * Complex.I / ((4 * 2 ^ e : ℕ) : ℂ))) :=
      ((Complex.isPrimitiveRoot_exp (4 * 2 ^ e) (by positivity)).isIntegral
        (by positivity)).tower_top
    rintro x (rfl | rfl | rfl)
    · exact hz.add hz.inv
    · exact isIntegral_I_mul_sqrt _
    · exact isIntegral_I_mul_sqrt _

theorem isHostField_hostField (e q₁ d : ℕ) : IsHostField (hostField e q₁ d) e q₁ d :=
  ⟨RingEquiv.refl _⟩

theorem hostNumbers_example : HostNumbers 2 11 7 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

end GlobalTheory.IndefiniteRowSideFullHecke.RelativeDifferentValues
