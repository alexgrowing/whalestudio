import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeFibre
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjDegreeChow
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntPoly
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.GaussNormEqCoeffGaussNorm
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

noncomputable section

namespace ConeFibreDegree

theorem ae_eval_ne_zero_univ {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) :
    ∀ᵐ u : ι → ℂ, eval u g ≠ 0 := by
  have hU : (⋃ r : ℕ, LogInt.polydisc ι r) = Set.univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    obtain ⟨r, hr⟩ := exists_nat_ge ‖u‖
    refine Set.mem_iUnion.mpr ⟨r, Set.mem_univ_pi.mpr fun i => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_pi_norm u i).trans hr
  have h := (ae_restrict_iUnion_iff (fun r : ℕ => LogInt.polydisc ι r) (fun u => eval u g ≠ 0)).mpr
    fun r => LogInt.ae_eval_ne_zero g hg r
  rwa [hU, Measure.restrict_univ] at h

theorem ae_eval_matrix_ne_zero {k n : ℕ} (g : MvPolynomial (Fin k × Fin n) ℂ) (hg : g ≠ 0) :
    ∀ᵐ π : Fin k → Fin n → ℂ, eval (fun ij => π ij.1 ij.2) g ≠ 0 := by
  have hmap : (volume : Measure (Fin k → Fin n → ℂ)) =
      (volume : Measure (Fin k × Fin n → ℂ)).map (MeasurableEquiv.curry (Fin k) (Fin n) ℂ) := by
    rw [ObjectsHeight.map_curry_volume]
    rfl
  rw [hmap, (MeasurableEquiv.curry (Fin k) (Fin n) ℂ).measurableEmbedding.ae_map_iff]
  exact ae_eval_ne_zero_univ g hg

theorem ae_eval_euclid_ne_zero {m : ℕ} (g : MvPolynomial (Fin m) ℂ) (hg : g ≠ 0) :
    ∀ᵐ w : EuclideanSpace ℂ (Fin m), eval (WithLp.ofLp w) g ≠ 0 := by
  let L : EuclideanSpace ℂ (Fin m) ≃L[ℝ] (Fin m → ℂ) :=
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin m => ℂ)
  have hac : (volume : Measure (EuclideanSpace ℂ (Fin m))).map L ≪ volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have h : ∀ᵐ u ∂(volume : Measure (EuclideanSpace ℂ (Fin m))).map L, eval u g ≠ 0 :=
    hac.ae_le (ae_eval_ne_zero_univ g hg)
  rw [ae_map_iff L.continuous.measurable.aemeasurable] at h
  · exact h
  · exact (isClosed_eq (continuous_eval g) continuous_const).isOpen_compl.measurableSet

theorem fibreCount_eq {k n : ℕ} (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (π : Fin k → Fin n → ℂ) (w : EuclideanSpace ℂ (Fin k)) :
    fibreCount h W π w =
      (ComplexSets.fibre W (Matrix.of π * (h.matᵀ)⁻¹) (WithLp.ofLp w)).encard := by
  have hu : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  have hinj : Function.Injective h.pointOf := by
    intro y y' hyy
    have hv := congrArg (fun v => (h.matᵀ)⁻¹ *ᵥ v) hyy
    simp only [HermNorm.pointOf, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec] at hv
    exact WithLp.ofLp_injective 2 hv
  have hπ : ∀ y : EuclideanSpace ℂ (Fin n),
      (Matrix.of π * (h.matᵀ)⁻¹) *ᵥ h.pointOf y = WithLp.ofLp (linProj π y) := by
    intro y
    rw [HermNorm.pointOf, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
    ext i
    simp [linProj, mulVec, dotProduct]
  rw [fibreCount, ← hinj.injOn.encard_image]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, ComplexSets.fibre, ComplexSets.zeroSet, coneSet]
  constructor
  · rintro ⟨y, ⟨hy, rfl⟩, rfl⟩
    exact ⟨hy, hπ y⟩
  · rintro ⟨hx, hxw⟩
    have hpt : h.pointOf (WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) = x := by
      simp [HermNorm.pointOf, mulVec_mulVec, mul_nonsing_inv _ hu]
    refine ⟨WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x), ⟨?_, ?_⟩, hpt⟩
    · rw [hpt]; exact hx
    · apply WithLp.ofLp_injective 2
      rw [← hπ, hpt, hxw]

theorem proof (hD : ConeDimOfChowForm.Statement)
    (hG : ComplexSets.GenericProjectionFinite.Statement)
    (hC : ComplexSets.DiscriminantCover.Statement) (hP : ProjDegreeChow.Statement) :
    ConeFibreDegree.Statement := by
  intro n e δ h W f hW hf hδ
  have hdim := hD ℂ n (e + 1) W f hW hf
  obtain ⟨⟨U, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hUfin⟩, -, -, -⟩ := hG n (e + 1) W hW.isPrime hdim
  rw [hS] at hA₀
  obtain ⟨p, hpS, hp⟩ := hA₀
  have hu : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  set B := (h.matᵀ)⁻¹ with hB
  set q : MvPolynomial (Fin (e + 1) × Fin n) ℂ :=
    bind₁ (fun ij => ∑ k, X (ij.1, k) * C (B k ij.2)) p with hqdef
  have hq : ∀ π : Fin (e + 1) → Fin n → ℂ,
      eval (fun ij => π ij.1 ij.2) q = eval (fun ij => (Matrix.of π * B) ij.1 ij.2) p := by
    intro π
    show eval₂Hom (RingHom.id ℂ) _ q = eval₂Hom (RingHom.id ℂ) _ p
    rw [hqdef, eval₂Hom_bind₁]
    congr 2
    funext ij
    simp [Matrix.mul_apply]
  have hq0 : q ≠ 0 := by
    intro h0
    have h1 := hq fun i j => (A₀ * h.matᵀ) i j
    have hA : Matrix.of (fun i j => (A₀ * h.matᵀ) i j) * B = A₀ := by
      rw [hB, show Matrix.of (fun i j => (A₀ * h.matᵀ) i j) = A₀ * h.matᵀ from rfl, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    rw [h0, map_zero, hA] at h1
    exact hp h1.symm
  filter_upwards [ae_eval_matrix_ne_zero q hq0] with π hπ
  have hfin : ComplexSets.IsFiniteProjection W (Matrix.of π * B) := by
    have hmem : Matrix.of π * B ∈ {A : Matrix (Fin (e + 1)) (Fin n) ℂ |
        ∃ p ∈ S, eval (fun ij => A ij.1 ij.2) p ≠ 0} := ⟨p, hpS, by rw [← hq]; exact hπ⟩
    rw [← hS] at hmem
    exact hUfin _ hmem
  obtain ⟨P, hP0, hPy⟩ := hC n (e + 1) W (Matrix.of π * B) hW.isPrime hdim hfin
  filter_upwards [ae_eval_euclid_ne_zero P hP0] with w hw
  obtain ⟨hfinite, hcard, -⟩ := hPy _ hw
  rw [fibreCount_eq, ← hfinite.cast_ncard_eq, hcard, hP n e δ W f _ hW hf hδ hfin]

end ConeFibreDegree

end

end GroundTheory.Heights₂.Heights
