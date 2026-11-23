import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ThetaQuasiPeriods.Change

noncomputable section

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def periodCoordFst (τ : Matrix ι ι ℂ) (w : ι → ℂ) : ι → ℝ :=
  (τ.map Complex.im)⁻¹ *ᵥ fun i => (w i).im

def periodCoordSnd (τ : Matrix ι ι ℂ) (w : ι → ℂ) : ι → ℝ :=
  (fun i => (w i).re) - τ.map Complex.re *ᵥ periodCoordFst τ w

theorem continuous_periodCoordFst (τ : Matrix ι ι ℂ) : Continuous (periodCoordFst τ) := by
  unfold periodCoordFst
  exact continuous_const.matrix_mulVec (by fun_prop)

theorem continuous_periodCoordSnd (τ : Matrix ι ι ℂ) : Continuous (periodCoordSnd τ) := by
  unfold periodCoordSnd
  exact Continuous.sub (by fun_prop)
    (continuous_const.matrix_mulVec (continuous_periodCoordFst τ))

omit [DecidableEq ι] in
theorem im_mulVec_ofRealVec_add (τ : Matrix ι ι ℂ) (u v : ι → ℝ) :
    (fun i => ((τ *ᵥ ofRealVec u + ofRealVec v) i).im) = τ.map Complex.im *ᵥ u := by
  ext i
  simp [ofRealVec, Matrix.mulVec, dotProduct, Complex.im_sum]

omit [DecidableEq ι] in
theorem re_mulVec_ofRealVec_add (τ : Matrix ι ι ℂ) (u v : ι → ℝ) :
    (fun i => ((τ *ᵥ ofRealVec u + ofRealVec v) i).re) = τ.map Complex.re *ᵥ u + v := by
  ext i
  simp [ofRealVec, Matrix.mulVec, dotProduct, Complex.re_sum]

theorem periodCoordFst_apply {τ : Matrix ι ι ℂ} (hτ : IsUnit (τ.map Complex.im).det)
    (u v : ι → ℝ) : periodCoordFst τ (τ *ᵥ ofRealVec u + ofRealVec v) = u := by
  unfold periodCoordFst
  rw [im_mulVec_ofRealVec_add, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hτ,
    Matrix.one_mulVec]

theorem periodCoordSnd_apply {τ : Matrix ι ι ℂ} (hτ : IsUnit (τ.map Complex.im).det)
    (u v : ι → ℝ) : periodCoordSnd τ (τ *ᵥ ofRealVec u + ofRealVec v) = v := by
  unfold periodCoordSnd
  rw [periodCoordFst_apply hτ, re_mulVec_ofRealVec_add]
  abel

theorem mulVec_periodCoordFst_add_periodCoordSnd {τ : Matrix ι ι ℂ}
    (hτ : IsUnit (τ.map Complex.im).det) (w : ι → ℂ) :
    τ *ᵥ ofRealVec (periodCoordFst τ w) + ofRealVec (periodCoordSnd τ w) = w := by
  ext i
  apply Complex.ext
  · have h := congrFun
      (re_mulVec_ofRealVec_add τ (periodCoordFst τ w) (periodCoordSnd τ w)) i
    rw [h]
    simp [periodCoordSnd]
  · have h := congrFun
      (im_mulVec_ofRealVec_add τ (periodCoordFst τ w) (periodCoordSnd τ w)) i
    rw [h]
    unfold periodCoordFst
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hτ, Matrix.one_mulVec]

omit [Fintype ι] [DecidableEq ι] in
theorem ofIntVec_eq_ofRealVec (n : ι → ℤ) : ofIntVec n = ofRealVec fun i => (n i : ℝ) := by
  ext i; simp [ofIntVec, ofRealVec]

theorem isUnit_det_im_of_mem_siegelH {τ : Matrix ι ι ℂ} (hτ : τ ∈ SiegelH ι) :
    IsUnit (τ.map Complex.im).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 hτ.2.isUnit

theorem intVec_eq_zero_of_periodCoord_lt_one {τ : Matrix ι ι ℂ}
    (hτ : IsUnit (τ.map Complex.im).det) (n n' : ι → ℤ)
    (h₁ : ∀ i, |periodCoordFst τ (τ *ᵥ ofIntVec n + ofIntVec n') i| < 1)
    (h₂ : ∀ i, |periodCoordSnd τ (τ *ᵥ ofIntVec n + ofIntVec n') i| < 1) :
    n = 0 ∧ n' = 0 := by
  rw [ofIntVec_eq_ofRealVec n, ofIntVec_eq_ofRealVec n'] at h₁ h₂
  rw [periodCoordFst_apply hτ] at h₁
  rw [periodCoordSnd_apply hτ] at h₂
  constructor
  · ext i
    have := h₁ i
    exact Int.abs_lt_one_iff.1 (by exact_mod_cast this)
  · ext i
    have := h₂ i
    exact Int.abs_lt_one_iff.1 (by exact_mod_cast this)

theorem periodCoordFst_zero (τ : Matrix ι ι ℂ) : periodCoordFst τ 0 = 0 := by
  ext i; simp [periodCoordFst, Matrix.mulVec, dotProduct]

theorem periodCoordSnd_zero (τ : Matrix ι ι ℂ) : periodCoordSnd τ 0 = 0 := by
  ext i; simp [periodCoordSnd, periodCoordFst_zero]

theorem discreteTopology_periodLattice_of_isUnit {τ : Matrix ι ι ℂ}
    (hτ : IsUnit (τ.map Complex.im).det) : DiscreteTopology (periodLattice τ) := by
  apply discreteTopology_of_isOpen_singleton_zero
  have hO : IsOpen ((⋂ i, {w : ι → ℂ | |periodCoordFst τ w i| < 1}) ∩
      ⋂ i, {w : ι → ℂ | |periodCoordSnd τ w i| < 1}) := by
    refine IsOpen.inter (isOpen_iInter_of_finite fun i => ?_)
      (isOpen_iInter_of_finite fun i => ?_)
    · exact isOpen_lt (((continuous_apply i).comp (continuous_periodCoordFst τ)).abs)
        continuous_const
    · exact isOpen_lt (((continuous_apply i).comp (continuous_periodCoordSnd τ)).abs)
        continuous_const
  convert hO.preimage (continuous_subtype_val (p := fun w => w ∈ periodLattice τ)) using 1
  ext ⟨w, hw⟩
  simp only [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_setOf_eq]
  constructor
  · intro h
    have h0 : w = 0 := congrArg Subtype.val h
    subst h0
    simp [periodCoordFst_zero, periodCoordSnd_zero]
  · rintro ⟨h₁, h₂⟩
    obtain ⟨n, n', rfl⟩ := hw
    obtain ⟨rfl, rfl⟩ := intVec_eq_zero_of_periodCoord_lt_one hτ n n' h₁ h₂
    apply Subtype.ext
    simp [ofIntVec_zero]

omit [DecidableEq ι] in
theorem mulVec_ofRealVec_add_mem_span_periodLattice (τ : Matrix ι ι ℂ) (u v : ι → ℝ) :
    τ *ᵥ ofRealVec u + ofRealVec v ∈
      Submodule.span ℝ (periodLattice τ : Set (ι → ℂ)) := by
  classical
  have e : ∀ u : ι → ℝ, ofRealVec u = ∑ j, u j • ofIntVec (Pi.single j (1 : ℤ)) := by
    intro u
    ext i
    simp [ofRealVec, ofIntVec, Finset.sum_apply, Pi.single_apply]
  refine Submodule.add_mem _ ?_ ?_
  · rw [e u, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Matrix.mulVec_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨Pi.single j 1, 0, ?_⟩)
    rw [ofIntVec_zero, add_zero]
  · rw [e v]
    refine Submodule.sum_mem _ fun j _ => ?_
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, Pi.single j 1, ?_⟩)
    rw [ofIntVec_zero, Matrix.mulVec_zero, zero_add]

theorem span_periodLattice_eq_top_of_isUnit {τ : Matrix ι ι ℂ}
    (hτ : IsUnit (τ.map Complex.im).det) :
    Submodule.span ℝ (periodLattice τ : Set (ι → ℂ)) = ⊤ := by
  rw [eq_top_iff]
  intro w _
  rw [← mulVec_periodCoordFst_add_periodCoordSnd hτ w]
  exact mulVec_ofRealVec_add_mem_span_periodLattice τ _ _

theorem intVec_eq_zero_of_period_eq_zero {τ : Matrix ι ι ℂ}
    (hτ : IsUnit (τ.map Complex.im).det) (n n' : ι → ℤ)
    (h : τ *ᵥ ofIntVec n + ofIntVec n' = 0) : n = 0 ∧ n' = 0 := by
  apply intVec_eq_zero_of_periodCoord_lt_one hτ n n'
  · intro i; simp [h, periodCoordFst_zero]
  · intro i; simp [h, periodCoordSnd_zero]

theorem periodLattice_isLattice_of_mem_siegelH :
    ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) →
      DiscreteTopology (periodLattice τ) ∧
      Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤ ∧
      ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0 := by
  intro g τ hτ
  have h := isUnit_det_im_of_mem_siegelH hτ
  exact ⟨discreteTopology_periodLattice_of_isUnit h, span_periodLattice_eq_top_of_isUnit h,
    intVec_eq_zero_of_period_eq_zero h⟩

end GlobalTheory
