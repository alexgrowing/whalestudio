import Mathlib

open MeasureTheory NumberField MvPolynomial
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure

abbrev UnitSphere (N : ℕ) : Type :=
  Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1

def sphereSurface (N : ℕ) : Measure (UnitSphere N) :=
  (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere

def sphereMeasure (N : ℕ) : Measure (UnitSphere N) :=
  (sphereSurface N Set.univ)⁻¹ • sphereSurface N

instance sphereSurface_finite (N : ℕ) : IsFiniteMeasure (sphereSurface N) := by
  unfold sphereSurface; infer_instance

instance sphereSurface_neZero (N : ℕ) : NeZero (sphereSurface N) := by
  refine ⟨fun h => ?_⟩
  have := (Measure.toSphere_eq_zero_iff _).1 h
  exact not_subsingleton _ this

instance sphereMeasure_isProbabilityMeasure (N : ℕ) : IsProbabilityMeasure (sphereMeasure N) := by
  unfold sphereMeasure; infer_instance

def sphereMap {N : ℕ}
    (e : EuclideanSpace ℂ (Fin (N + 1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (N + 1)))
    (z : UnitSphere N) : UnitSphere N :=
  ⟨e z.1, by simpa using z.2⟩

theorem sphereMeasure_map_unitary {N : ℕ}
    (e : EuclideanSpace ℂ (Fin (N + 1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (N + 1))) :
    (sphereMeasure N).map (sphereMap e) = sphereMeasure N := by
  have hc : Continuous (sphereMap e) :=
    Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) _
  let e' : EuclideanSpace ℂ (Fin (N + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin (N + 1)) :=
    { e.toLinearEquiv.restrictScalars ℝ with norm_map' := e.norm_map }
  have hs : (sphereSurface N).map (sphereMap e) = sphereSurface N := by
    ext s hs
    rw [Measure.map_apply hc.measurable hs, sphereSurface,
      Measure.toSphere_apply' _ (hc.measurable hs), Measure.toSphere_apply' _ hs]
    congr 1
    rw [← e'.measurePreserving.measure_preimage_emb e'.toHomeomorph.measurableEmbedding
      (Set.Ioo (0 : ℝ) 1 • ((Subtype.val : UnitSphere N → EuclideanSpace ℂ (Fin (N + 1))) '' s))]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_smul, Set.mem_image]
    constructor
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨r, hr, _, ⟨_, hz, rfl⟩, (e'.map_smul r z.1).symm⟩
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, hx⟩
      refine ⟨r, hr, _, ⟨sphereMap e.symm z, ?_, rfl⟩, ?_⟩
      · have : sphereMap e (sphereMap e.symm z) = z := Subtype.ext (e.apply_symm_apply z.1)
        simpa [this] using hz
      · apply e'.injective
        rw [← hx, e'.map_smul]
        congr 1
        exact e.apply_symm_apply z.1
  rw [sphereMeasure, Measure.map_smul, hs]

def blockSphereMeasure (B N : ℕ) : Measure (Fin B → UnitSphere N) :=
  Measure.pi fun _ => sphereMeasure N

instance blockSphereMeasure_isProbabilityMeasure (B N : ℕ) :
    IsProbabilityMeasure (blockSphereMeasure B N) := by
  unfold blockSphereMeasure; infer_instance

def sphereLogAbs {N : ℕ} (f : MvPolynomial (Fin (N + 1)) ℂ) (z : UnitSphere N) : ℝ :=
  Real.log ‖eval (fun j => z.1 j) f‖

def sphereLogMean {N : ℕ} (f : MvPolynomial (Fin (N + 1)) ℂ) : ℝ :=
  ∫ z, sphereLogAbs f z ∂sphereMeasure N

def blockLogAbs {B N : ℕ} (P : MvPolynomial (Fin B × Fin (N + 1)) ℂ)
    (T : Fin B → UnitSphere N) : ℝ :=
  Real.log ‖eval (fun i => (T i.1).1 i.2) P‖

def blockLogMean {B N : ℕ} (P : MvPolynomial (Fin B × Fin (N + 1)) ℂ) : ℝ :=
  ∫ T, blockLogAbs P T ∂blockSphereMeasure B N

def IsBlockHomogeneous {R : Type} [CommSemiring R] {B n : ℕ}
    (ω : MvPolynomial (Fin B × Fin n) R) (a : Fin B → ℕ) : Prop :=
  ∀ d : Fin B × Fin n →₀ ℕ, coeff d ω ≠ 0 → ∀ b : Fin B, ∑ j : Fin n, d (b, j) = a b

section NumberField

variable {K : Type} [Field K] [NumberField K]

def gaussAbsValue {ι : Type} (w : FinitePlace K) (ω : MvPolynomial ι K) : ℝ :=
  ((ω.support.sup fun d => Real.toNNReal (w (coeff d ω)) : ℝ≥0) : ℝ)

theorem finitePlace_eq_absNorm_zpow (w : FinitePlace K) {c : K} (hc : c ≠ 0) :
    w c = (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ) ^
      (WithZero.log (w.maximalIdeal.valuation K c)) := by
  have h0 : w.maximalIdeal.valuation K c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  rw [← FinitePlace.norm_embedding_eq, FinitePlace.norm_embedding',
    WithZeroMulInt.toNNReal_neg_apply _ h0]
  obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.1 h0
  simp only [← hk, WithZero.unzero_coe]
  push_cast
  rfl

theorem le_gaussAbsValue {ι : Type} (w : FinitePlace K) (ω : MvPolynomial ι K) (d : ι →₀ ℕ) :
    w (coeff d ω) ≤ gaussAbsValue w ω := by
  by_cases h : d ∈ ω.support
  · have := Finset.le_sup (f := fun d => Real.toNNReal (w (coeff d ω))) h
    exact Real.toNNReal_le_iff_le_coe.1 this
  · rw [notMem_support_iff.1 h]
    simp [gaussAbsValue]

theorem exists_gaussAbsValue_eq {ι : Type} (w : FinitePlace K) {ω : MvPolynomial ι K}
    (h : ω ≠ 0) : ∃ d ∈ ω.support, gaussAbsValue w ω = w (coeff d ω) := by
  obtain ⟨d, hd, e⟩ := Finset.exists_mem_eq_sup ω.support (support_nonempty.2 h)
    fun d => Real.toNNReal (w (coeff d ω))
  exact ⟨d, hd, by rw [gaussAbsValue, e, Real.coe_toNNReal _ (apply_nonneg w _)]⟩

theorem gaussAbsValue_pos {ι : Type} (w : FinitePlace K) {ω : MvPolynomial ι K}
    (h : ω ≠ 0) : 0 < gaussAbsValue w ω := by
  obtain ⟨d, hd, e⟩ := exists_gaussAbsValue_eq w h
  rw [e]
  exact FinitePlace.pos_iff.2 (mem_support_iff.1 hd)

theorem finite_support_log_gaussAbsValue {ι : Type} {ω : MvPolynomial ι K} (h : ω ≠ 0) :
    (Function.support fun w : FinitePlace K => Real.log (gaussAbsValue w ω)).Finite := by
  have hf : (⋃ d ∈ ω.support, Function.mulSupport fun w : FinitePlace K => w (coeff d ω)).Finite :=
    ω.support.finite_toSet.biUnion fun d hd =>
      FinitePlace.hasFiniteMulSupport (mem_support_iff.1 hd)
  refine hf.subset fun w hw => ?_
  obtain ⟨d, hd, e⟩ := exists_gaussAbsValue_eq w h
  refine Set.mem_biUnion hd fun h1 => hw ?_
  simp only at h1
  simp [e, h1]

def heightZero {B N : ℕ} (ω : MvPolynomial (Fin B × Fin (N + 1)) K) : ℝ :=
  ((∑ᶠ w : FinitePlace K, Real.log (gaussAbsValue w ω)) +
    ∑ σ : K →+* ℂ, blockLogMean (MvPolynomial.map σ ω)) / (Module.finrank ℚ K : ℝ)

end NumberField

def hermitianLinearForm {N : ℕ} (u : EuclideanSpace ℂ (Fin (N + 1))) :
    MvPolynomial (Fin (N + 1)) ℂ :=
  ∑ j, X j * C (starRingEnd ℂ (u j))

def LogAbsIntegrable : Prop :=
  (∀ (N a : ℕ) (f : MvPolynomial (Fin (N + 1)) ℂ), f ≠ 0 → f.IsHomogeneous a →
    (∀ᵐ z ∂sphereMeasure N, eval (fun j => z.1 j) f ≠ 0) ∧
      Integrable (sphereLogAbs f) (sphereMeasure N)) ∧
  ∀ (B N : ℕ) (a : Fin B → ℕ) (P : MvPolynomial (Fin B × Fin (N + 1)) ℂ), P ≠ 0 →
    IsBlockHomogeneous P a →
    (∀ᵐ T ∂blockSphereMeasure B N, eval (fun i => (T i.1).1 i.2) P ≠ 0) ∧
      Integrable (blockLogAbs P) (blockSphereMeasure B N)

def GaussAbsValueMul : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B N : ℕ) (w : FinitePlace K)
    (ω ω' : MvPolynomial (Fin B × Fin (N + 1)) K),
    gaussAbsValue w (ω * ω') = gaussAbsValue w ω * gaussAbsValue w ω'

def HeightZeroAdditive : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B N : ℕ) (a a' : Fin B → ℕ)
    (ω ω' : MvPolynomial (Fin B × Fin (N + 1)) K), ω ≠ 0 → ω' ≠ 0 →
    IsBlockHomogeneous ω a → IsBlockHomogeneous ω' a' →
    heightZero (ω * ω') = heightZero ω + heightZero ω'

def HeightZeroScaleInvariant : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B N : ℕ) (a : Fin B → ℕ) (c : K)
    (ω : MvPolynomial (Fin B × Fin (N + 1)) K), c ≠ 0 → ω ≠ 0 → IsBlockHomogeneous ω a →
    heightZero (C c * ω) = heightZero ω

def HeightZeroOnFractions : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B N : ℕ) (a b a' b' : Fin B → ℕ)
    (p q p' q' : MvPolynomial (Fin B × Fin (N + 1)) K), p ≠ 0 → q ≠ 0 → p' ≠ 0 → q' ≠ 0 →
    IsBlockHomogeneous p a → IsBlockHomogeneous q b →
    IsBlockHomogeneous p' a' → IsBlockHomogeneous q' b' → p * q' = p' * q →
    heightZero p - heightZero q = heightZero p' - heightZero q'

def SphericalJensen : Prop :=
  ∀ N : ℕ,
    (∀ (a : ℕ) (f : MvPolynomial (Fin (N + 1)) ℂ) (u : EuclideanSpace ℂ (Fin (N + 1))),
      f.IsHomogeneous a → ‖u‖ = 1 → eval (fun j => u j) f ≠ 0 →
      Integrable (sphereLogAbs f) (sphereMeasure N) ∧
        Real.log ‖eval (fun j => u j) f‖ - (a : ℝ) / 2 * (harmonic N : ℝ) ≤ sphereLogMean f) ∧
    (∀ (a : ℕ) (u : EuclideanSpace ℂ (Fin (N + 1))), ‖u‖ = 1 →
      sphereLogMean (hermitianLinearForm u ^ a) =
        Real.log ‖eval (fun j => u j) (hermitianLinearForm u ^ a)‖ -
          (a : ℝ) / 2 * (harmonic N : ℝ)) ∧
    ∀ u : EuclideanSpace ℂ (Fin (N + 1)), u ≠ 0 →
      sphereLogMean (hermitianLinearForm u) = Real.log ‖u‖ - (harmonic N : ℝ) / 2

def HeightZeroLowerBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (B N : ℕ) (a : Fin B → ℕ)
    (ω : MvPolynomial (Fin B × Fin (N + 1)) K), ω ≠ 0 → IsBlockHomogeneous ω a →
    -∑ b, (a b : ℝ) * (Real.log (N + 1 : ℕ) + 1 / 2) ≤ heightZero ω ∧
    -((B : ℝ) * ((Finset.univ.sup a : ℕ) : ℝ) * (Real.log (N + 1 : ℕ) + 1 / 2)) ≤
      -∑ b, (a b : ℝ) * (Real.log (N + 1 : ℕ) + 1 / 2)

def HeightZeroStatements : Prop :=
  LogAbsIntegrable ∧ GaussAbsValueMul ∧ HeightZeroAdditive ∧ HeightZeroScaleInvariant ∧
    HeightZeroOnFractions ∧ SphericalJensen ∧ HeightZeroLowerBound

theorem heightZeroOnFractions_of_additive (h : HeightZeroAdditive) : HeightZeroOnFractions := by
  intro K _ _ B N a b a' b' p q p' q' hp hq hp' hq' ha hb ha' hb' e
  have h1 := h K B N a b' p q' hp hq' ha hb'
  have h2 := h K B N a' b p' q hp' hq ha' hb
  rw [e] at h1
  linarith

theorem eval_hermitianLinearForm {N : ℕ} (u z : EuclideanSpace ℂ (Fin (N + 1))) :
    eval (fun j => z j) (hermitianLinearForm u) = inner ℂ u z := by
  simp [hermitianLinearForm, PiLp.inner_apply]

example (B n : ℕ) (b₀ : Fin B) (j₀ : Fin n) :
    IsBlockHomogeneous (X (b₀, j₀) : MvPolynomial (Fin B × Fin n) ℚ) (Pi.single b₀ 1) := by
  intro d hd b
  rw [coeff_X'] at hd
  have : Finsupp.single (b₀, j₀) 1 = d := by
    by_contra h; exact hd (if_neg h)
  subst this
  by_cases hb : b = b₀
  · subst hb; simp [Finsupp.single_apply, eq_comm]
  · simp [Finsupp.single_apply, hb, Ne.symm hb]

example (K : Type) [Field K] [NumberField K] (B N : ℕ) :
    heightZero (1 : MvPolynomial (Fin B × Fin (N + 1)) K) = 0 := by
  have h : ∀ w : FinitePlace K,
      gaussAbsValue w (1 : MvPolynomial (Fin B × Fin (N + 1)) K) = 1 := by
    intro w
    obtain ⟨d, hd, e⟩ := exists_gaussAbsValue_eq w
      (one_ne_zero : (1 : MvPolynomial (Fin B × Fin (N + 1)) K) ≠ 0)
    rw [mem_support_iff, coeff_one] at hd
    rw [e, coeff_one, if_pos (by by_contra h; exact hd (if_neg h)), map_one]
  simp [heightZero, h, blockLogMean, blockLogAbs]

end GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
