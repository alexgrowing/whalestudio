import Mathlib

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

noncomputable def ord_vw {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K)) : ℕ :=
  multiplicity la.asIdeal I

noncomputable def conjDifferent {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) : Ideal (𝓞 K) :=
  (differentIdeal ℤ (𝓞 E)).map (RingOfIntegers.mapRingHom σ)

theorem conjDifferent_ne_bot {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) : conjDifferent σ ≠ ⊥ := by
  have hinj : Function.Injective (RingOfIntegers.mapRingHom σ) := by
    intro x y h
    apply RingOfIntegers.ext
    apply σ.injective
    simpa using congrArg (fun z : 𝓞 K => (z : K)) h
  unfold conjDifferent
  rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
  exact differentIdeal_ne_bot

theorem span_natCast_ne_bot {K : Type} [Field K] [NumberField K] (n' : ℕ+) :
    Ideal.span {((n' : ℕ) : 𝓞 K)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast n'.ne_zero

noncomputable def defectAt_vw {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K)) : ℕ :=
  a * max (ord_vw la (conjDifferent σ)) (ord_vw la (Ideal.span {((n' : ℕ) : 𝓞 K)}))

noncomputable def defect_vw (E : Type) {K : Type} [Field E] [NumberField E] [Field K]
    [NumberField K] (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Finset.univ.sup fun σ : E →+* K => defectAt_vw σ n' a la

noncomputable def lrd (E : Type) [Field E] [NumberField E] : ℝ :=
  Real.log (rootDiscr E)

noncomputable def logNorm {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm la.asIdeal)

noncomputable def normSum {K : Type} [Field K] [NumberField K]
    (b : HeightOneSpectrum (𝓞 K) → ℕ) : ℝ :=
  (∑ᶠ la, (b la : ℝ) * logNorm la) / (Module.finrank ℚ K : ℝ)

def DefectAtSumBound : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) (n' : ℕ+) (a : ℕ) (κ : ℝ), (a : ℝ) ≤ κ →
    (Function.support (defectAt_vw σ n' a)).Finite ∧
      normSum (defectAt_vw σ n' a) ≤ (lrd E + Real.log ((n' : ℕ) : ℝ)) * κ

def DefectSumBound : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K],
    Nonempty (E →+* K) → ∀ (n' : ℕ+) (a : ℕ) (κ : ℝ), (a : ℝ) ≤ κ →
    (Function.support (defect_vw E (K := K) n' a)).Finite ∧
      normSum (defect_vw E (K := K) n' a) ≤ (lrd E + Real.log ((n' : ℕ) : ℝ)) * κ

theorem defectAt_vw_eq_mul {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K)) (e : ℝ) (he : 0 < e) :
    (defectAt_vw σ n' a la : ℝ) = e * a * max ((ord_vw la (conjDifferent σ) : ℝ) / e)
      ((ord_vw la (Ideal.span {((n' : ℕ) : 𝓞 K)}) : ℝ) / e) := by
  rw [max_div_div_right he.le, defectAt_vw]
  push_cast
  field_simp

theorem defectAt_vw_le {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K)) :
    defectAt_vw σ n' a la ≤ defect_vw E n' a la :=
  Finset.le_sup (f := fun σ : E →+* K => defectAt_vw σ n' a la) (Finset.mem_univ σ)

theorem le_defectAt_vw_of_mem {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K))
    (h : ((n' : ℕ) : 𝓞 K) ∈ la.asIdeal) : a ≤ defectAt_vw σ n' a la := by
  have h1 : 0 < ord_vw la (Ideal.span {((n' : ℕ) : 𝓞 K)}) :=
    dvd_iff_multiplicity_pos.mpr (Ideal.dvd_span_singleton.mpr h)
  exact Nat.le_mul_of_pos_right _ (lt_of_lt_of_le h1 (le_max_right _ _))

end GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
