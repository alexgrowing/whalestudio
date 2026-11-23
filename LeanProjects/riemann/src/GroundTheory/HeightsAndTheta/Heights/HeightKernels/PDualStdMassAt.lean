import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.DualProjApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix

noncomputable section

namespace StandardDualMassAtPoint

variable {K : Type} [Field K] [NumberField K] {T : Type} [Fintype T] [DecidableEq T]

omit [Fintype T] [DecidableEq T] in
theorem segre_const (z : (Σ _ : Unit, T) → ℂ) (t : T) :
    segre (ι := dualBlocks T) z (fun _ => t) = z ⟨(), t⟩ := by
  simp [segre]

omit [Fintype T] [DecidableEq T] in
open Classical in

theorem recover_planePt {i : ℕ} {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (v : Fin i → ℂ) :
    dualRecover b hb (fun t => dualPlanePt b σ v ⟨(), t⟩) =
      fun p => if p.1 = σ then v p.2 else 0 := by
  rw [dualRecover, LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply]
  funext t
  simp [Matrix.mulVec, dotProduct, dualEmbMatrix, dualPlanePt,
    Fintype.sum_prod_type]

omit [Fintype T] [DecidableEq T] in

theorem proj_segre_planePt {i : ℕ} {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (v : Fin i → ℂ) :
    dualProj b hb (segre (dualPlanePt b σ v)) = v := by
  funext j
  simp only [dualProj_apply, segre_const, recover_planePt]
  rw [Finset.sum_eq_single σ (fun τ _ hτ => if_neg hτ) (by simp)]
  exact if_pos rfl

theorem h_eq (hOn : DualPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (hF : ∀ σ, F.metric σ = 1) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) {z : (Σ _ : Unit, T) → ℂ}
    (hz : z ∈ mcPts (dualIdeal b)) :
    (dualLine F b hb).h z = Real.sqrt (∑ j, ‖dualProj b hb (segre z) j‖ ^ 2) := by
  obtain ⟨σ, hσ⟩ := hOn K (D + 1) F T b hb z hz
  have hp : ∀ j, dualProj b hb (segre z) j = dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j) := by
    intro j
    simp only [dualProj_apply, segre_const]
    exact Finset.sum_eq_single σ (fun τ _ hτ => hσ τ hτ j) (by simp)
  show Real.sqrt (dualNormSq b hb _) = _
  congr 1
  rw [dualNormSq, Finset.sum_eq_single σ]
  · rw [hF, one_mulVec, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq, hp]
  · intro τ _ hτ
    have h0 : (fun j => dualRecover b hb (fun t => z ⟨(), t⟩) (τ, j)) = 0 := funext (hσ τ hτ)
    rw [h0]
    simp
  · simp

theorem sheetDensity_eq (hOn : DualPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (hF : ∀ σ, F.metric σ = 1) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) {y : Fin D → ℂ}
    {w : ((k : Unit) → dualBlocks T k) → ℂ} (h : ∃ γ, IsSheet (dualIdeal b) (dualProj b hb) y w γ) :
    sheetDensity (dualIdeal b) (dualProj b hb) (fun _ z => Real.log ((dualLine F b hb).h z))
      (fun _ => 1) y w = maDensity (fun _ : Fin D => gbPot) y := by
  unfold sheetDensity
  rw [dif_pos h, one_mul]
  apply maDensity_congr_of_eventuallyEq
  intro j
  filter_upwards [h.choose_spec.2] with y' hy'
  obtain ⟨-, hmc, hΨ⟩ := hy'
  show Real.log ((dualLine F b hb).h (h.choose y')) = gbPot y'
  rw [h_eq hOn hF b hb hmc, hΨ, gbPot, Fin.sum_univ_succ]
  simp

theorem fibre_eq (hOn : DualPtsOnPlane.Statement) (hOf : DualPtsOfPlane.Statement) {D : ℕ}
    {F : HermLattice K (D + 1)} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (y : Fin D → ℂ) :
    fibre (dualIdeal b) (dualProj b hb) y =
      Set.range fun σ : K →+* ℂ => segre (ι := dualBlocks T) (dualPlanePt b σ (Fin.cons 1 y)) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl, hΨ⟩
    obtain ⟨σ, hσ⟩ := hOn K (D + 1) F T b hb z hz
    refine ⟨σ, congrArg segre ?_⟩
    have hW : dualRecover b hb (fun t => z ⟨(), t⟩) =
        dualRecover b hb (fun t => dualPlanePt b σ (Fin.cons 1 y) ⟨(), t⟩) := by
      rw [recover_planePt]
      funext ⟨τ, j⟩
      by_cases hτ : τ = σ
      · subst hτ
        rw [if_pos rfl, ← hΨ]
        simp only [dualProj_apply, segre_const]
        exact (Finset.sum_eq_single τ (fun τ' _ h' => hσ τ' h' j) (by simp)).symm
      · rw [if_neg hτ]
        exact hσ τ hτ j
    have h1 := (dualRecover b hb).injective hW
    funext ⟨u, t⟩
    cases u
    exact (congrFun h1 t).symm
  · rintro ⟨σ, rfl⟩
    have hv : (Fin.cons 1 y : Fin (D + 1) → ℂ) ≠ 0 := fun h0 => by simpa using congrFun h0 0
    exact ⟨_, hOf K (D + 1) F T b hb σ _ hv, rfl, proj_segre_planePt b hb σ _⟩

omit [Fintype T] [DecidableEq T] in

theorem planePt_injective {D : ℕ} {F : HermLattice K (D + 1)} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (y : Fin D → ℂ) :
    Function.Injective fun σ : K →+* ℂ => segre (ι := dualBlocks T) (dualPlanePt b σ (Fin.cons 1 y)) := by
  intro σ τ h
  have h1 := congrArg (fun w : ((k : Unit) → dualBlocks T k) → ℂ =>
    dualRecover b hb (fun t => w fun _ => t)) h
  simp only [segre_const, recover_planePt] at h1
  have h2 := congrFun h1 (σ, 0)
  simpa using h2

theorem isSheet_planePt (hOf : DualPtsOfPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (y : Fin D → ℂ) :
    IsSheet (dualIdeal b) (dualProj b hb) y (segre (ι := dualBlocks T) (dualPlanePt b σ (Fin.cons 1 y)))
      (fun y' => dualPlanePt b σ (Fin.cons 1 y')) := by
  have hc : Differentiable ℂ (fun y' : Fin D → ℂ => (Fin.cons 1 y' : Fin (D + 1) → ℂ)) := by
    rw [differentiable_pi]
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp
    · simpa using differentiable_apply (𝕜 := ℂ) k
  refine ⟨rfl, Filter.Eventually.of_forall fun y' => ⟨?_, ?_, proj_segre_planePt b hb σ _⟩⟩
  · refine (differentiable_pi.mpr fun p => ?_) y'
    simp only [dualPlanePt]
    exact Differentiable.fun_sum fun j _ => (differentiable_pi.mp hc j).const_mul _
  · exact hOf K (D + 1) F T b hb σ _ fun h0 => by simpa using congrFun h0 0

end StandardDualMassAtPoint

open StandardDualMassAtPoint in

theorem DualStdMassAt.proof (hOn : DualPtsOnPlane.Statement) (hOf : DualPtsOfPlane.Statement) :
    DualStdMassAt.Statement := by
  intro K _ _ D F T _ _ b hb hF
  have hint : ∀ y : Fin D → ℂ, ∑ᶠ w ∈ fibre (dualIdeal b) (dualProj b hb) y,
      sheetDensity (dualIdeal b) (dualProj b hb) (fun _ z => Real.log ((dualLine F b hb).h z))
        (fun _ => 1) y w = (Fintype.card (K →+* ℂ) : ℝ) * maDensity (fun _ : Fin D => gbPot) y := by
    intro y
    rw [fibre_eq hOn hOf b hb y, finsum_mem_range (planePt_injective b hb y),
      finsum_eq_sum_of_fintype,
      Finset.sum_congr rfl fun σ _ => sheetDensity_eq hOn hF b hb ⟨_, isSheet_planePt hOf b hb σ y⟩,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold ptsIntegralAt
  simp only [hint]
  rw [integral_const_mul, integral_maDensity_gbPot, mul_one]

end

end GroundTheory.Heights₂.Heights
