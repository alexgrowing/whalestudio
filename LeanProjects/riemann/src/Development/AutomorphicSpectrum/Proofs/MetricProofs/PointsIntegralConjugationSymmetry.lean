import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MeasureTheory

section Hess

variable {D : ℕ}

theorem hess_comp_star (φ : (Fin D → ℂ) → ℝ) (z u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y => φ (star y))) z u v =
      fderiv ℝ (fderiv ℝ φ) (star z) (star u) (star v) := by
  let σ : (Fin D → ℂ) ≃L[ℝ] (Fin D → ℂ) := starL' ℝ
  let T : ((Fin D → ℂ) →L[ℝ] ℝ) ≃L[ℝ] ((Fin D → ℂ) →L[ℝ] ℝ) :=
    σ.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have h1 : fderiv ℝ (fun y => φ (star y)) = T ∘ ((fderiv ℝ φ) ∘ σ) := by
    funext y
    have := σ.comp_right_fderiv (f := φ) (x := y)
    exact this
  rw [h1, T.comp_fderiv, σ.comp_right_fderiv]
  rfl

theorem cxHessian_comp_star (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    cxHessian (fun y => φ (star y)) z = (cxHessian φ (star z)).map (starRingEnd ℂ) := by
  ext i j
  have hs : ∀ i : Fin D, star (Pi.single i 1 : Fin D → ℂ) = Pi.single i 1 := fun i => by
    ext l; by_cases h : l = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hI : ∀ i : Fin D, star (Complex.I • (Pi.single i 1 : Fin D → ℂ)) =
      -(Complex.I • (Pi.single i 1 : Fin D → ℂ)) := fun i => by
    rw [star_smul, hs]; simp
  simp only [cxHessian, Matrix.map_apply, hess_comp_star, hs, hI, map_neg,
    ContinuousLinearMap.neg_apply, neg_neg]
  simp only [map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  have h4 : starRingEnd ℂ (4 : ℂ) = 4 := map_ofNat _ 4
  simp [h4]
  ring

theorem mixedDisc_map_conj (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun k => (A k).map (starRingEnd ℂ)) = starRingEnd ℂ (mixedDisc A) := by
  simp only [mixedDisc, map_mul, map_sum, map_pow, map_neg, map_one, map_div₀, map_natCast]
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.sum_apply]

theorem maDensity_comp_star (φ : Fin D → (Fin D → ℂ) → ℝ) (y : Fin D → ℂ) :
    maDensity (fun j y' => φ j (star y')) y = maDensity φ (star y) := by
  simp only [maDensity, cxHessian_comp_star, mixedDisc_map_conj, Complex.conj_re]

theorem star_measurePreserving :
    MeasurePreserving (star : (Fin D → ℂ) → (Fin D → ℂ)) volume volume := by
  have h : MeasurePreserving (starRingEnd ℂ : ℂ → ℂ) volume volume :=
    Complex.conjLIE.measurePreserving
  exact volume_preserving_pi (fun _ => h)

end Hess

section Pts

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem eval_star (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    eval (star z) (map (Int.castRingHom ℂ) f) =
      starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
  rw [eval_map, eval_map, eval₂_comp_left]
  congr 1
  exact Subsingleton.elim _ _

theorem star_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    star z ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, by simpa using hi⟩
  · rw [eval_star, hz.2 f hf, map_zero]

theorem segre_star (z : (Σ k, ι k) → ℂ) : segre (star z) = star (segre z) := by
  funext i
  simp [segre, map_prod]

theorem cons_star {e : ℕ} (y : Fin e → ℂ) :
    (Fin.cons 1 (star y) : Fin (e + 1) → ℂ) = star (Fin.cons 1 y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

variable {e : ℕ} {P : Ideal (MRing ι)}
  {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}

theorem star_mem_fibre (hΨ : ∀ w, Ψ' (star w) = star (Ψ w)) {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre P Ψ y) : star w ∈ fibre P Ψ' (star y) := by
  obtain ⟨z, hz, rfl, h⟩ := hw
  exact ⟨star z, star_mem_mcPts hz, segre_star z, by rw [hΨ, h, cons_star]⟩

theorem differentiableAt_star_star {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [StarAddMonoid E] [StarModule ℂ E] [StarModule ℝ E]
    [ContinuousStar E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F] [StarAddMonoid F] [StarModule ℂ F] [StarModule ℝ F] [ContinuousStar F]
    {γ : E → F} {x : E} (h : DifferentiableAt ℂ γ (star x)) :
    DifferentiableAt ℂ (fun y => star (γ (star y))) x := by
  have hD := h.hasFDerivAt
  set D := fderiv ℂ γ (star x)
  let sE : E →L[ℝ] E := (starL' ℝ : E ≃L[ℝ] E)
  let sF : F →L[ℝ] F := (starL' ℝ : F ≃L[ℝ] F)
  have hs : HasFDerivAt (star : E → E) sE x := sE.hasFDerivAt
  have hr : HasFDerivAt γ (D.restrictScalars ℝ) (star x) := hD.restrictScalars ℝ
  have hc : HasFDerivAt (fun y => star (γ (star y)))
      (sF.comp ((D.restrictScalars ℝ).comp sE)) x :=
    HasFDerivAt.comp x (g := (star : F → F)) sF.hasFDerivAt (hr.comp x hs)
  let cE : E →SL[starRingEnd ℂ] E := ((starL ℂ : E ≃L⋆[ℂ] E) : E →SL[starRingEnd ℂ] E)
  let cF : F →SL[starRingEnd ℂ] F := ((starL ℂ : F ≃L⋆[ℂ] F) : F →SL[starRingEnd ℂ] F)
  let D' : E →L[ℂ] F := cF.comp (D.comp cE)
  have : HasFDerivAt (fun y => star (γ (star y))) D' x :=
    hasFDerivAt_of_restrictScalars ℝ hc (by ext v; rfl)
  exact this.differentiableAt

theorem isSheet_star (hΨ : ∀ w, Ψ' (star w) = star (Ψ w)) {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (h : IsSheet P Ψ y w γ) :
    IsSheet P Ψ' (star y) (star w) (fun y' => star (γ (star y'))) := by
  refine ⟨by simp only [star_star, segre_star, h.1], ?_⟩
  have ht : Tendsto (star : (Fin e → ℂ) → (Fin e → ℂ)) (𝓝 (star y)) (𝓝 y) := by
    have := (continuous_star (R := Fin e → ℂ)).tendsto (star y)
    simpa using this
  filter_upwards [ht.eventually h.2] with y' ⟨h1, h2, h3⟩
  refine ⟨differentiableAt_star_star h1, star_mem_mcPts h2, ?_⟩
  rw [segre_star, hΨ, h3, cons_star, star_star]

theorem sheetDensity_star {L : Fin e → HermLine ι} (hLc : ∀ j, IsConjInvariantH (L j))
    {B B' : HermLine ι} (hBB : ∀ z ∈ mcPts P, B'.h (star z) = B.h z)
    (hΨ : ∀ w, Ψ' (star w) = star (Ψ w)) (hΨ' : ∀ w, Ψ (star w) = star (Ψ' w)) {y : Fin e → ℂ}
    (hy : ∀ w γ γ', IsSheet P Ψ y w γ → IsSheet P Ψ y w γ' →
      logNorm B 1 (γ y) * maDensity (fun j y' => pot L j (γ y')) y =
        logNorm B 1 (γ' y) * maDensity (fun j y' => pot L j (γ' y')) y)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ (pot L) (logNorm B 1) y w =
      sheetDensity P Ψ' (pot L) (logNorm B' 1) (star y) (star w) := by
  have back : ∀ γ, IsSheet P Ψ' (star y) (star w) γ →
      IsSheet P Ψ y w (fun y' => star (γ (star y'))) := fun γ h => by
    have := isSheet_star hΨ' h
    simpa only [star_star] using this
  unfold sheetDensity
  by_cases hex : ∃ γ, IsSheet P Ψ y w γ
  · have hex' : ∃ γ, IsSheet P Ψ' (star y) (star w) γ :=
      ⟨_, isSheet_star hΨ hex.choose_spec⟩
    rw [dif_pos hex, dif_pos hex', hy w _ _ hex.choose_spec (back _ hex'.choose_spec)]
    set γ := hex'.choose with hγ
    have hspec : IsSheet P Ψ' (star y) (star w) γ := hex'.choose_spec
    have hz : γ (star y) ∈ mcPts P := hspec.2.self_of_nhds.2.1
    have h1 : logNorm B 1 (star (γ (star (y)))) = logNorm B' 1 (γ (star y)) := by
      have h2 : B'.h (γ (star y)) = B.h (star (γ (star y))) := by
        have := hBB _ (star_mem_mcPts hz)
        rwa [star_star] at this
      simp [logNorm, h2]
    have h3 : maDensity (fun j y' => pot L j (star (γ (star y')))) y =
        maDensity (fun j y' => pot L j (γ y')) (star y) := by
      rw [← maDensity_comp_star]
      congr 1
      funext j y'
      simp only [pot]
      congr 1
      exact hLc j _
    rw [h1, h3]
  · have hex' : ¬ ∃ γ, IsSheet P Ψ' (star y) (star w) γ := fun ⟨γ, h⟩ => hex ⟨_, back γ h⟩
    rw [dif_neg hex, dif_neg hex']

end Pts

theorem ptsIntegralAt_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (B B' : HermLine ι), IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ w, Ψ' (star w) = star (Ψ w)) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsConjInvariantH (L j)) → B.a = 0 → IsSmoothHerm B → B'.a = 0 → IsSmoothHerm B' → (∀ z ∈ mcPts P, B'.h (star z) = B.h z) → IsGoodProj P Ψ' ∧ ptsIntegralAt P Ψ' (pot L) (logNorm B' 1) = ptsIntegralAt P Ψ (pot L) (logNorm B 1) := by
  intro K _ ι _ P e Ψ Ψ' L B B' hP hΨ hΨs hLs hLc hBa hBs _ _ hBB
  have hΨ2 : ∀ w, Ψ (star w) = star (Ψ' w) := fun w => by
    have := hΨs (star w)
    rw [star_star] at this
    rw [this, star_star]
  refine ⟨fun z hz h0 => ?_, ?_⟩
  · refine hΨ _ (star_mem_mcPts hz) ?_
    rw [segre_star, hΨ2, h0, star_zero]
  · have hsec : IsSectionOn P B 1 := by
      refine ⟨0, fun k => by simp [hBa], fun m hm k => ?_, ?_⟩
      · have : m = 0 := by
          have := MvPolynomial.support_one (R := ℤ) (σ := Σ k, ι k)
          rw [this] at hm
          simpa using hm
        simp [this]
      · exact fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    have hme : MeasurableEmbedding (star : (Fin e → ℂ) → (Fin e → ℂ)) :=
      (starL' ℝ : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ)).toHomeomorph.measurableEmbedding
    unfold ptsIntegralAt
    rw [← star_measurePreserving.integral_comp hme]
    refine integral_congr_ae ?_
    filter_upwards [sheetIndep K ι P e Ψ L B 1 hP hΨ hLs hBs hsec] with y hy
    symm
    refine finsum_mem_eq_of_bijOn star ⟨fun w hw => star_mem_fibre hΨs hw, ?_, ?_⟩ fun w _ =>
      sheetDensity_star hLc hBB hΨs hΨ2 hy w
    · exact star_injective.injOn
    · intro w hw
      refine ⟨star w, ?_, star_star w⟩
      have := star_mem_fibre hΨ2 hw
      rwa [star_star] at this

end GlobalTheory.CompanionTheory.Ar.Giv
