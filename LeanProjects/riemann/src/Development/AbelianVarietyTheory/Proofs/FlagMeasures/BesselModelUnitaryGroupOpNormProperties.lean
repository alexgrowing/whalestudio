import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.OpNormU

theorem eucl_eq {N : ℕ} (v : Fin N → ℂ) : eucl v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [eucl, Complex.normSq_eq_norm_sq]

theorem eucl_nonneg {N : ℕ} (v : Fin N → ℂ) : 0 ≤ eucl v := Real.sqrt_nonneg _

theorem eucl_mulVec_le {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    eucl (x *ᵥ v) ≤ opn x * eucl v := by
  rw [eucl_eq, eucl_eq, ← Matrix.toEuclideanCLM_toLp]
  exact ContinuousLinearMap.le_opNorm _ _

theorem continuous_opn {N : ℕ} : Continuous fun x : Matrix (Fin N) (Fin N) ℂ => opn x :=
  (LinearMap.continuous_of_finiteDimensional
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N)).toAlgEquiv.toLinearMap).norm

theorem opn_conjTranspose {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) : opn xᴴ = opn x := by
  unfold opn
  rw [← Matrix.star_eq_conjTranspose, map_star, norm_star]

theorem norm_entry_le {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) : ‖x i j‖ ≤ opn x := by
  have h := eucl_mulVec_le x (Pi.single j 1)
  have h1 : eucl (Pi.single j (1 : ℂ) : Fin N → ℂ) = 1 := by
    rw [eucl_eq]; simpa using (EuclideanSpace.norm_single (𝕜 := ℂ) j (1 : ℂ))
  have h2 : ‖x i j‖ ≤ eucl (x *ᵥ Pi.single j 1) := by
    rw [eucl_eq]
    have := PiLp.norm_apply_le (p := 2) (WithLp.toLp 2 (x *ᵥ Pi.single j (1 : ℂ)) : EuclideanSpace ℂ (Fin N)) i
    simpa [Matrix.mulVec_single] using this
  rw [h1, mul_one] at h
  exact h2.trans h

theorem herm_le {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (u v : Fin N → ℂ) :
    ‖herm H u v‖ ≤ opn H * eucl u * eucl v := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N)) (WithLp.toLp 2 (H *ᵥ u))
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, ← eucl_eq, ← eucl_eq, mul_comm] at h
  exact h.trans (mul_le_mul_of_nonneg_right (eucl_mulVec_le H u) (eucl_nonneg _))

theorem eucl_mulVec_le_hs {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (w : Fin N → ℂ) :
    eucl (x *ᵥ w) ≤ Real.sqrt (Formalism.REAL.hs x) * eucl w := by
  unfold eucl
  have hnn : 0 ≤ Formalism.REAL.hs x := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [← Real.sqrt_mul hnn]
  apply Real.sqrt_le_sqrt
  simp only [Complex.normSq_eq_norm_sq, Formalism.REAL.hs, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(x *ᵥ w) i‖ ≤ ∑ j, ‖x i j‖ * ‖w j‖ := by
    rw [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_mul]
  calc ‖(x *ᵥ w) i‖ ^ 2 ≤ (∑ j, ‖x i j‖ * ‖w j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ j, ‖x i j‖ ^ 2) * ∑ j, ‖w j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = _ := Finset.sum_mul _ _ _

theorem opn_le_sqrt_hs {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) : opn x ≤ Real.sqrt (Formalism.REAL.hs x) := by
  unfold opn
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
  obtain ⟨w, rfl⟩ : ∃ w : Fin N → ℂ, v = WithLp.toLp 2 w := ⟨v.ofLp, rfl⟩
  rw [Matrix.toEuclideanCLM_toLp, ← eucl_eq, ← eucl_eq]
  exact eucl_mulVec_le_hs x w

theorem sqrt_hs_le {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) :
    Real.sqrt (Formalism.REAL.hs x) ≤ (N : ℝ) * opn x := by
  rw [Real.sqrt_le_iff]
  refine ⟨mul_nonneg (Nat.cast_nonneg _) (opn_nonneg _), ?_⟩
  calc Formalism.REAL.hs x ≤ ∑ _i : Fin N, ∑ _j : Fin N, opn x ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (norm_entry_le x i j) 2
    _ = ((N : ℝ) * opn x) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

variable {k r : ℕ}

theorem opn_Hpk (k r : ℕ) : opn (Hpk k r) = 1 := by
  have h : opn ((Hpk k r)ᴴ * Hpk k r) = opn (Hpk k r) * opn (Hpk k r) := by
    unfold opn
    rw [← Matrix.star_eq_conjTranspose, map_mul, map_star, CStarRing.norm_star_mul_self]
  rw [GBasic.Hpk_herm, GBasic.Hpk_sq, opn_one] at h
  rcases mul_self_eq_one_iff.mp h.symm with h1 | h1
  · exact h1
  · have := opn_nonneg (Hpk k r); linarith

theorem left_inv {g : Mat k r} (hg : g ∈ GG k r) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', GBasic.Hpk_sq]

theorem inv_eq {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r :=
  Matrix.inv_eq_left_inv (left_inv hg)

theorem inv_mul {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ * g = 1 := by
  rw [inv_eq hg]; exact left_inv hg

theorem mul_inv {g : Mat k r} (hg : g ∈ GG k r) : g * g⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (left_inv hg))

theorem opn_inv_le {g : Mat k r} (hg : g ∈ GG k r) : opn g⁻¹ ≤ opn g := by
  rw [inv_eq hg]
  calc opn (Hpk k r * gᴴ * Hpk k r) ≤ opn (Hpk k r) * opn gᴴ * opn (Hpk k r) :=
        (opn_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opn_mul_le _ _) (opn_nonneg _))
    _ = opn g := by rw [opn_Hpk, opn_conjTranspose]; ring

theorem le_opn_inv {g : Mat k r} (hg : g ∈ GG k r) : opn g ≤ opn g⁻¹ := by
  have e : g = Hpk k r * (g⁻¹)ᴴ * Hpk k r := by
    rw [inv_eq hg]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, GBasic.Hpk_herm, ← Matrix.mul_assoc,
      GBasic.Hpk_sq, Matrix.one_mul]
    rw [Matrix.mul_assoc, GBasic.Hpk_sq, Matrix.mul_one]
  calc opn g = opn (Hpk k r * (g⁻¹)ᴴ * Hpk k r) := congrArg opn e
    _ ≤ opn (Hpk k r) * opn (g⁻¹)ᴴ * opn (Hpk k r) :=
        (opn_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opn_mul_le _ _) (opn_nonneg _))
    _ = opn g⁻¹ := by rw [opn_Hpk, opn_conjTranspose]; ring

theorem opn_inv {g : Mat k r} (hg : g ∈ GG k r) : opn g⁻¹ = opn g :=
  le_antisymm (opn_inv_le hg) (le_opn_inv hg)

theorem one_le_opn {g : Mat k r} (hg : g ∈ GG k r) : 1 ≤ opn g := by
  have h : (1 : ℝ) ≤ opn g * opn g := by
    have := opn_mul_le g g⁻¹
    rwa [mul_inv hg, opn_one, opn_inv hg] at this
  by_contra h'
  have h0 := opn_nonneg g
  nlinarith

theorem opn_pos {g : Mat k r} (hg : g ∈ GG k r) : 0 < opn g := lt_of_lt_of_le one_pos (one_le_opn hg)

theorem div_le_opn_mul {x y : Mat k r} (hx : x ∈ GG k r) (hy : y ∈ GG k r) :
    opn x / opn y ≤ opn (x * y) ∧ opn y / opn x ≤ opn (x * y) := by
  constructor
  · rw [div_le_iff₀ (opn_pos hy)]
    calc opn x = opn (x * y * y⁻¹) := by rw [Matrix.mul_assoc, mul_inv hy, Matrix.mul_one]
      _ ≤ opn (x * y) * opn y⁻¹ := opn_mul_le _ _
      _ = opn (x * y) * opn y := by rw [opn_inv hy]
  · rw [div_le_iff₀ (opn_pos hx)]
    calc opn y = opn (x⁻¹ * (x * y)) := by rw [← Matrix.mul_assoc, inv_mul hx, Matrix.one_mul]
      _ ≤ opn x⁻¹ * opn (x * y) := opn_mul_le _ _
      _ = opn (x * y) * opn x := by rw [opn_inv hx, mul_comm]

end GlobalTheory.SgInf.OpNormU

namespace GlobalTheory.SgInf

theorem opn_facts : ∀ (k r : ℕ) , (∀ g ∈ GG k r, opn g⁻¹ = opn g ∧ 1 ≤ opn g) ∧
    (∀ x y : Mat k r, opn (x * y) ≤ opn x * opn y) ∧ Continuous (fun x : Mat k r => opn x) ∧
    (∀ (x : Mat k r) i j, ‖x i j‖ ≤ opn x) ∧
    (∀ (x : Mat k r) (v : Fin (2 * r + k + 1) → ℂ), eucl (x *ᵥ v) ≤ opn x * eucl v) ∧
    (∀ u v : Fin (2 * r + k + 1) → ℂ, ‖herm (Hpk k r) u v‖ ≤ eucl u * eucl v) ∧
    (∀ x ∈ GG k r, ∀ y ∈ GG k r, opn x / opn y ≤ opn (x * y) ∧ opn y / opn x ≤ opn (x * y)) ∧
    (∀ x : Mat k r, opn x ≤ Real.sqrt (Formalism.REAL.hs x) ∧
      Real.sqrt (Formalism.REAL.hs x) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * opn x) := by
  intro k r
  refine ⟨fun g hg => ⟨OpNormU.opn_inv hg, OpNormU.one_le_opn hg⟩, fun x y => opn_mul_le x y,
    OpNormU.continuous_opn, OpNormU.norm_entry_le, OpNormU.eucl_mulVec_le, fun u v => ?_,
    fun x hx y hy => OpNormU.div_le_opn_mul hx hy,
    fun x => ⟨OpNormU.opn_le_sqrt_hs x, OpNormU.sqrt_hs_le x⟩⟩
  simpa [OpNormU.opn_Hpk] using OpNormU.herm_le (Hpk k r) u v

end GlobalTheory.SgInf
