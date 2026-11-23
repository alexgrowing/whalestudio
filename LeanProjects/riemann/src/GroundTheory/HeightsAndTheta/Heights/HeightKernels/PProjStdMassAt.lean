import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ProjProjApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix NumberField

noncomputable section

namespace ProjectiveStandardMassAtPoint

variable {K : Type} [Field K] [NumberField K]

theorem segre_const {i : ℕ} (z : (Σ _ : Unit, ProjIdx K i) → ℂ) (q : ProjIdx K i) :
    segre (ι := projBlocks K i) z (fun _ => q) = z ⟨(), q⟩ := by
  simp [segre]

open Classical in

theorem repr_sum (τ σ : K →+* ℂ) :
    ∑ m, (canonicalEmbedding.latticeBasis K).repr (Pi.single τ 1) m * σ (integralBasis K m) =
      if σ = τ then 1 else 0 := by
  have h := congrFun ((canonicalEmbedding.latticeBasis K).sum_repr (Pi.single τ 1)) σ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, canonicalEmbedding.latticeBasis_apply,
    canonicalEmbedding.apply_at, Pi.single_apply] at h
  exact h

open Classical in

theorem embComp_planePt {i : ℕ} (τ σ : K →+* ℂ) (v : Fin i → ℂ) :
    embComp τ (fun q => projPlanePt σ v ⟨(), q⟩) = if σ = τ then v else 0 := by
  funext j
  have h : ∑ m, (canonicalEmbedding.latticeBasis K).repr (Pi.single τ 1) m *
      (σ (integralBasis K m) * v j) = (if σ = τ then 1 else 0) * v j := by
    rw [← repr_sum τ σ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by ring
  simp only [embComp, projPlanePt]
  rw [h]
  split_ifs <;> simp

theorem proj_segre_planePt {i : ℕ} (σ : K →+* ℂ) (v : Fin i → ℂ) :
    projProj (segre (ι := projBlocks K i) (projPlanePt σ v)) = v := by
  classical
  rw [projProj_apply]
  simp only [segre_const, embComp_planePt]
  rw [Finset.sum_eq_single σ (fun τ _ hτ => if_neg (Ne.symm hτ)) (by simp)]
  exact if_pos rfl

theorem h_eq (hOn : ProjPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (hF : ∀ σ, F.metric σ = 1) {z : (Σ _ : Unit, ProjIdx K (D + 1)) → ℂ}
    (hz : z ∈ mcPts (projSpaceIdeal K (D + 1))) :
    (latticeLine F).h z = Real.sqrt (∑ j, ‖projProj (segre (ι := projBlocks K (D + 1)) z) j‖ ^ 2) := by
  obtain ⟨σ, hσ⟩ := hOn K (D + 1) z hz
  have hp : projProj (segre (ι := projBlocks K (D + 1)) z) = embComp σ (fun q => z ⟨(), q⟩) := by
    rw [projProj_apply]
    simp only [segre_const]
    exact Finset.sum_eq_single σ (fun τ _ hτ => hσ τ hτ) (by simp)
  show Real.sqrt (latticeNormSq F fun q => z ⟨(), q⟩) = _
  congr 1
  rw [latticeNormSq, Finset.sum_eq_single σ]
  · rw [hF, one_mulVec, dotProduct, Complex.re_sum, hp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  · intro τ _ hτ
    rw [hσ τ hτ]
    simp
  · simp

theorem sheetDensity_eq (hOn : ProjPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (hF : ∀ σ, F.metric σ = 1) {y : Fin D → ℂ}
    {w : ((k : Unit) → projBlocks K (D + 1) k) → ℂ}
    (h : ∃ γ, IsSheet (projSpaceIdeal K (D + 1)) projProj y w γ) :
    sheetDensity (projSpaceIdeal K (D + 1)) projProj (fun _ z => Real.log ((latticeLine F).h z))
      (fun _ => 1) y w = maDensity (fun _ : Fin D => gbPot) y := by
  unfold sheetDensity
  rw [dif_pos h, one_mul]
  apply maDensity_congr_of_eventuallyEq
  intro j
  filter_upwards [h.choose_spec.2] with y' hy'
  obtain ⟨-, hmc, hΨ⟩ := hy'
  show Real.log ((latticeLine F).h (h.choose y')) = gbPot y'
  rw [h_eq hOn hF hmc, hΨ, gbPot, Fin.sum_univ_succ]
  simp

theorem fibre_eq (hOn : ProjPtsOnPlane.Statement) (hOf : ProjPtsOfPlane.Statement) {D : ℕ}
    (y : Fin D → ℂ) :
    fibre (projSpaceIdeal K (D + 1)) projProj y =
      Set.range fun σ : K →+* ℂ => segre (ι := projBlocks K (D + 1)) (projPlanePt σ (Fin.cons 1 y)) := by
  classical
  ext w
  constructor
  · rintro ⟨z, hz, rfl, hΨ⟩
    obtain ⟨σ, hσ⟩ := hOn K (D + 1) z hz
    refine ⟨σ, congrArg segre ?_⟩
    have hW : ∀ τ : K →+* ℂ, embComp τ (fun q => z ⟨(), q⟩) =
        embComp τ (fun q => projPlanePt σ (Fin.cons 1 y) ⟨(), q⟩) := by
      intro τ
      rw [embComp_planePt]
      by_cases hτ : σ = τ
      · subst hτ
        rw [if_pos rfl, ← hΨ, projProj_apply]
        simp only [segre_const]
        exact (Finset.sum_eq_single σ (fun τ' _ h' => hσ τ' h') (by simp)).symm
      · rw [if_neg hτ]
        exact hσ τ (Ne.symm hτ)
    funext ⟨u, m, j⟩
    cases u
    refine ((sum_emb_embComp (fun q => projPlanePt σ (Fin.cons 1 y) ⟨(), q⟩) m j).symm.trans ?_).trans
      (sum_emb_embComp (fun q => z ⟨(), q⟩) m j)
    exact Finset.sum_congr rfl fun τ _ => by rw [hW τ]
  · rintro ⟨σ, rfl⟩
    have hv : (Fin.cons 1 y : Fin (D + 1) → ℂ) ≠ 0 := fun h0 => by simpa using congrFun h0 0
    exact ⟨_, hOf K (D + 1) σ _ hv, rfl, proj_segre_planePt σ _⟩

theorem planePt_injective {D : ℕ} (y : Fin D → ℂ) :
    Function.Injective fun σ : K →+* ℂ =>
      segre (ι := projBlocks K (D + 1)) (projPlanePt σ (Fin.cons 1 y)) := by
  classical
  intro σ τ h
  have h1 := congrArg (fun w : ((k : Unit) → projBlocks K (D + 1) k) → ℂ =>
    embComp σ (fun q => w fun _ => q)) h
  simp only [segre_const, embComp_planePt] at h1
  by_contra hne
  rw [if_pos trivial, if_neg fun e => hne e.symm] at h1
  simpa using congrFun h1 0

theorem isSheet_planePt (hOf : ProjPtsOfPlane.Statement) {D : ℕ} (σ : K →+* ℂ) (y : Fin D → ℂ) :
    IsSheet (projSpaceIdeal K (D + 1)) projProj y
      (segre (ι := projBlocks K (D + 1)) (projPlanePt σ (Fin.cons 1 y)))
      (fun y' => projPlanePt σ (Fin.cons 1 y')) := by
  have hc : Differentiable ℂ (fun y' : Fin D → ℂ => (Fin.cons 1 y' : Fin (D + 1) → ℂ)) := by
    rw [differentiable_pi]
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp
    · simpa using differentiable_apply (𝕜 := ℂ) k
  refine ⟨rfl, Filter.Eventually.of_forall fun y' => ⟨?_, ?_, proj_segre_planePt σ _⟩⟩
  · refine (differentiable_pi.mpr fun p => ?_) y'
    simp only [projPlanePt]
    exact (differentiable_pi.mp hc p.2.2).const_mul _
  · exact hOf K (D + 1) σ _ fun h0 => by simpa using congrFun h0 0

end ProjectiveStandardMassAtPoint

open ProjectiveStandardMassAtPoint in

theorem ProjStdMassAt.proof (hOn : ProjPtsOnPlane.Statement) (hOf : ProjPtsOfPlane.Statement) :
    ProjStdMassAt.Statement := by
  intro K _ _ D F hF
  have hint : ∀ y : Fin D → ℂ, ∑ᶠ w ∈ fibre (projSpaceIdeal K (D + 1)) projProj y,
      sheetDensity (projSpaceIdeal K (D + 1)) projProj (fun _ z => Real.log ((latticeLine F).h z))
        (fun _ => 1) y w = (Fintype.card (K →+* ℂ) : ℝ) * maDensity (fun _ : Fin D => gbPot) y := by
    intro y
    rw [fibre_eq hOn hOf y, finsum_mem_range (planePt_injective y),
      finsum_eq_sum_of_fintype,
      Finset.sum_congr rfl fun σ _ => sheetDensity_eq hOn hF ⟨_, isSheet_planePt hOf σ y⟩,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold ptsIntegralAt
  simp only [hint]
  rw [integral_const_mul, integral_maDensity_gbPot, mul_one]

end

end GroundTheory.Heights₂.Heights
