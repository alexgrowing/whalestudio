import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LengthCont

variable {n ι : Type} [Fintype n] [DecidableEq n]

def dst (x : n → ℂ) (f : ι → n → ℂ) (s : Set ι) (A : Matrix n n ℂ) : ℝ :=
  Metric.infDist (WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℂ n)
    (Submodule.span ℂ ((fun b => (WithLp.toLp 2 (A *ᵥ f b) : EuclideanSpace ℂ n)) '' s) : Set _)

def opn (M : Matrix n n ℂ) : ℝ := ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M‖

lemma opn_cont : Continuous (opn (n := n)) := by

  let L : Matrix n n ℂ →ₗ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
    { toFun := fun M => Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M
      map_add' := fun M N => map_add _ M N
      map_smul' := fun c M => map_smul _ c M }
  exact continuous_norm.comp (LinearMap.continuous_of_finiteDimensional L)

lemma opn_one [Nonempty n] : opn (1 : Matrix n n ℂ) = 1 := by
  unfold opn
  rw [map_one]
  exact norm_one

private lemma infDist_image_le_opNorm_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (y : E) (K : Set E) (hK : K.Nonempty) :
    Metric.infDist (T y) (T '' K) ≤ ‖T‖ * Metric.infDist y K := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / (‖T‖ + 1) := by positivity
  obtain ⟨p, hp, hd⟩ := (Metric.infDist_lt_iff hK).1 (lt_add_of_pos_right (Metric.infDist y K) hδ)
  have hTε : ‖T‖ * (ε / (‖T‖ + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg T]
  calc Metric.infDist (T y) (T '' K) ≤ dist (T y) (T p) :=
        Metric.infDist_le_dist_of_mem (Set.mem_image_of_mem T hp)
    _ ≤ ‖T‖ * dist y p := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]; exact T.le_opNorm _
    _ ≤ ‖T‖ * (Metric.infDist y K + ε / (‖T‖ + 1)) := by gcongr
    _ ≤ ‖T‖ * Metric.infDist y K + ε := by rw [mul_add]; linarith

lemma dst_mul_le (x : n → ℂ) (f : ι → n → ℂ) (s : Set ι) (M A : Matrix n n ℂ) :
    dst x f s (M * A) ≤ opn M * dst x f s A := by
  unfold dst
  set T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M
  have key : ∀ v : n → ℂ, (WithLp.toLp 2 ((M * A) *ᵥ v) : EuclideanSpace ℂ n) =
      T (WithLp.toLp 2 (A *ᵥ v)) := fun v => by
    rw [← Matrix.mulVec_mulVec]; rfl
  simp only [key]
  set S : Set (EuclideanSpace ℂ n) := (fun b => (WithLp.toLp 2 (A *ᵥ f b) : EuclideanSpace ℂ n)) '' s
  have himg : (fun b => T (WithLp.toLp 2 (A *ᵥ f b))) '' s = T '' S := (Set.image_image _ _ _).symm
  rw [himg]

  have hsub : T '' (Submodule.span ℂ S : Set _) ⊆ (Submodule.span ℂ (T '' S) : Set _) := by
    rintro _ ⟨p, hp, rfl⟩
    exact Submodule.apply_mem_span_image_of_mem_span (T : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) hp
  calc Metric.infDist (T (WithLp.toLp 2 (A *ᵥ x))) (Submodule.span ℂ (T '' S) : Set _)
      ≤ Metric.infDist (T (WithLp.toLp 2 (A *ᵥ x))) (T '' (Submodule.span ℂ S : Set _)) :=
        Metric.infDist_le_infDist_of_subset hsub ⟨T 0, 0, Submodule.zero_mem _, rfl⟩
    _ ≤ ‖T‖ * Metric.infDist (WithLp.toLp 2 (A *ᵥ x)) (Submodule.span ℂ S : Set _) :=
        infDist_image_le_opNorm_mul T _ _ ⟨0, Submodule.zero_mem _⟩
    _ = opn M * Metric.infDist (WithLp.toLp 2 (A *ᵥ x)) (Submodule.span ℂ S : Set _) := rfl

lemma dst_inv_continuousOn [Nonempty n] (x : n → ℂ) (f : ι → n → ℂ) (s : Set ι) :
    ContinuousOn (fun g : Matrix n n ℂ => dst x f s g⁻¹) {g | IsUnit g.det} := by
  set U : Set (Matrix n n ℂ) := {g | IsUnit g.det}

  have hinv : ContinuousOn (fun g : Matrix n n ℂ => g⁻¹) U := by
    have h : (fun g : Matrix n n ℂ => g⁻¹) = fun g => (g.det)⁻¹ • g.adjugate := by
      funext g; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h]
    exact (continuous_id.matrix_det.continuousOn.inv₀ fun g hg => hg.ne_zero).smul
      continuous_id.matrix_adjugate.continuousOn
  intro g0 hg0
  have hg0' : IsUnit g0.det := hg0
  set a0 := dst x f s g0⁻¹

  have hu : Filter.Tendsto (fun g => opn (g⁻¹ * g0)) (nhdsWithin g0 U) (nhds 1) := by
    have hc : ContinuousWithinAt (fun g => opn (g⁻¹ * g0)) U g0 :=
      opn_cont.continuousAt.comp_continuousWithinAt ((hinv g0 hg0).mul continuousWithinAt_const)
    have h1 : opn (g0⁻¹ * g0) = 1 := by rw [Matrix.nonsing_inv_mul _ hg0', opn_one]
    have := hc.tendsto
    rwa [h1] at this
  have hv : Filter.Tendsto (fun g => opn (g0⁻¹ * g)) (nhdsWithin g0 U) (nhds 1) := by
    have hc : Continuous fun g => opn (g0⁻¹ * g) := opn_cont.comp (continuous_const.mul continuous_id)
    have h1 : opn (g0⁻¹ * g0) = 1 := by rw [Matrix.nonsing_inv_mul _ hg0', opn_one]
    have := hc.continuousWithinAt (s := U) (x := g0) |>.tendsto
    rwa [h1] at this
  have hup : ∀ g ∈ U, dst x f s g⁻¹ ≤ opn (g⁻¹ * g0) * a0 := by
    intro g _
    have h := dst_mul_le x f s (g⁻¹ * g0) g0⁻¹
    rwa [mul_assoc, Matrix.mul_nonsing_inv _ hg0', mul_one] at h
  have hlow : ∀ g ∈ U, a0 ≤ opn (g0⁻¹ * g) * dst x f s g⁻¹ := by
    intro g hg
    have h := dst_mul_le x f s (g0⁻¹ * g) g⁻¹
    rwa [mul_assoc, Matrix.mul_nonsing_inv _ (show IsUnit g.det from hg), mul_one] at h
  have hpos : ∀ᶠ g in nhdsWithin g0 U, 0 < opn (g0⁻¹ * g) := hv.eventually (lt_mem_nhds one_pos)
  have hL : Filter.Tendsto (fun g => a0 / opn (g0⁻¹ * g)) (nhdsWithin g0 U) (nhds a0) := by
    have := (tendsto_const_nhds (x := a0)).div hv one_ne_zero
    rwa [div_one] at this
  have hR : Filter.Tendsto (fun g => opn (g⁻¹ * g0) * a0) (nhdsWithin g0 U) (nhds a0) := by
    have := hu.mul_const a0
    rwa [one_mul] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hR ?_ (eventually_nhdsWithin_of_forall hup)
  filter_upwards [hpos, eventually_nhdsWithin_of_forall hlow] with g hg1 hg2
  rw [div_le_iff₀ hg1, mul_comm]
  exact hg2

theorem lenA_continuousOn : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z →
    0 < Formalism.QuantumDeterminants.Tz k r z → ∀ a, ContinuousOn (fun g => lenA k r z g a) (GG k r) := by
  intro k r z _ _ a

  have hsub : GG k r ⊆ {g : Mx k r | IsUnit g.det} := by
    intro g hg
    have h1 : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
    have hdet : (Formalism.QuantumDeterminants.Hpk k r).det * (Formalism.QuantumDeterminants.Hpk k r).det = 1 := by
      rw [← Matrix.det_mul, Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.det_one]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    show IsUnit g.det
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at h2
    rw [← h2, mul_zero] at hdet
    exact zero_ne_one hdet
  exact (dst_inv_continuousOn (Formalism.QuantumDeterminants.fvec k r z a) (Formalism.QuantumDeterminants.fvec k r z) {b | b < a}).mono hsub

end GlobalTheory.LengthCont
