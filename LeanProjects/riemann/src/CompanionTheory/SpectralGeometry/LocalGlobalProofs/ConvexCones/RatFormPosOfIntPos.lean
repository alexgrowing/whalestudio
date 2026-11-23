import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

open Matrix in

theorem ratForm_pos_of_int_pos {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ)
    (hQ : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ i, ∑ j, Q i j * v i * v j)
    (w : Fin n → ℚ) (hw : w ≠ 0) : 0 < ∑ i, ∑ j, Q i j * w i * w j := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) w
  choose v hv using hb
  have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast nonZeroDivisors.ne_zero b.2
  have hv' : ∀ i, (v i : ℚ) = (b : ℤ) * w i := by
    intro i
    have := hv i
    simpa [Algebra.smul_def] using this
  have hv0 : v ≠ 0 := by
    intro h
    apply hw
    funext i
    have h1 := hv' i
    rw [h] at h1
    simp only [Pi.zero_apply, Int.cast_zero] at h1
    have := (mul_eq_zero.1 h1.symm).resolve_left hb0
    simpa using this
  have h := hQ v hv0
  have h2 : ∑ i, ∑ j, Q i j * (v i : ℚ) * (v j : ℚ)
      = ((b : ℤ) : ℚ) ^ 2 * ∑ i, ∑ j, Q i j * w i * w j := by
    simp only [Finset.mul_sum, hv']
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h2] at h
  have hb2 : 0 < ((b : ℤ) : ℚ) ^ 2 := by positivity
  exact (pos_iff_pos_of_mul_pos h).1 hb2

open Matrix in

theorem posDef_of_int_pos (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℚ) (hs : Q.IsSymm)
    (hQ : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ i, ∑ j, Q i j * v i * v j) :
    (Q.map (Rat.cast : ℚ → ℝ)).PosDef := by
  have hrat := ratForm_pos_of_int_pos Q hQ
  set R : Matrix (Fin n) (Fin n) ℝ := Q.map (Rat.cast : ℚ → ℝ) with hR
  have hRh : R.IsHermitian := by
    ext i j
    simpa [hR] using congrArg (Rat.cast : ℚ → ℝ) (hs.apply i j)
  have hform : ∀ x : Fin n → ℝ, x ⬝ᵥ (R *ᵥ x) = ∑ i, ∑ j, R i j * x i * x j := by
    intro x
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hcast : ∀ w : Fin n → ℚ, ((fun i => (w i : ℝ)) ⬝ᵥ (R *ᵥ fun i => (w i : ℝ)))
      = ((∑ i, ∑ j, Q i j * w i * w j : ℚ) : ℝ) := by
    intro w
    rw [hform]
    push_cast
    simp [hR]
  have hdense : DenseRange (fun (w : Fin n → ℚ) (i : Fin n) => (w i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hcont : Continuous fun x : Fin n → ℝ => x ⬝ᵥ (R *ᵥ x) := by
    simp only [hform]
    fun_prop
  have hnonneg : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (R *ᵥ x) := by
    have hcl : IsClosed {x : Fin n → ℝ | 0 ≤ x ⬝ᵥ (R *ᵥ x)} :=
      isClosed_le continuous_const hcont
    intro x
    refine hdense.induction_on (p := fun x => 0 ≤ x ⬝ᵥ (R *ᵥ x)) x hcl fun w => ?_
    show 0 ≤ (fun i => (w i : ℝ)) ⬝ᵥ (R *ᵥ fun i => (w i : ℝ))
    rw [hcast]
    by_cases hw : w = 0
    · simp [hw]
    · exact_mod_cast (hrat w hw).le
  have hpsd : R.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hRh fun x => ?_
    simpa using hnonneg x
  rw [hpsd.posDef_iff_det_ne_zero]
  intro h0
  have hRQ : R = (Rat.castHom ℝ).mapMatrix Q := by
    ext i j
    simp [hR]
  rw [hRQ, ← RingHom.map_det, map_eq_zero] at h0
  obtain ⟨w, hw, hQw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 := hrat w hw
  have h2 : ∑ i, ∑ j, Q i j * w i * w j = w ⬝ᵥ (Q *ᵥ w) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h2, hQw, dotProduct_zero] at h1
  exact lt_irrefl _ h1

end GlobalTheory.CompanionTheory.Ar.Fan
