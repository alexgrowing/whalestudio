import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAddFirst
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsAddFirst.cxHessian_add {D : ℕ} {a b ψ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 a y') (hb : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 b y')
    (hψ : ψ =ᶠ[𝓝 y] fun y' => a y' + b y') :
    cxHessian ψ y = cxHessian a y + cxHessian b y := by
  have h1 : fderiv ℝ ψ =ᶠ[𝓝 y] fun y' => fderiv ℝ a y' + fderiv ℝ b y' := by
    filter_upwards [hψ.fderiv (𝕜 := ℝ), ha, hb] with y' h1 h2 h3
    rw [h1]
    exact ((h2.differentiableAt (by norm_num)).hasFDerivAt.add
      (h3.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have da2 : DifferentiableAt ℝ (fderiv ℝ a) y :=
    (ha.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have db2 : DifferentiableAt ℝ (fderiv ℝ b) y :=
    (hb.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hH : fderiv ℝ (fderiv ℝ ψ) y = fderiv ℝ (fderiv ℝ a) y + fderiv ℝ (fderiv ℝ b) y := by
    rw [h1.fderiv_eq]
    exact (da2.hasFDerivAt.add db2.hasFDerivAt).fderiv
  ext i j
  simp only [cxHessian, hH, Matrix.add_apply, add_apply]
  push_cast
  ring

theorem PtsAddFirst.mixedDisc_cons_add {D : ℕ} (A B : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)
    (C : Fin D → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ) :
    mixedDisc (Fin.cons (A + B) C : Fin (D + 1) → _) =
      mixedDisc (Fin.cons A C : Fin (D + 1) → _) + mixedDisc (Fin.cons B C : Fin (D + 1) → _) := by
  have h := ReciprocityTheory.AnForm.A.mdisc_update_add (Fin.cons A C : Fin (D + 1) → _) 0 A B
  simp only [Fin.update_cons_zero] at h
  exact h

theorem PtsAddFirst.maDensity_cons_add {D : ℕ} (f g h : (Fin (D + 1) → ℂ) → ℝ)
    (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ)
    (hH : cxHessian h y = cxHessian f y + cxHessian g y) :
    maDensity (Fin.cons h ψ) y = maDensity (Fin.cons f ψ) y + maDensity (Fin.cons g ψ) y := by
  have hc : ∀ u : (Fin (D + 1) → ℂ) → ℝ, (fun k => cxHessian ((Fin.cons u ψ : Fin (D + 1) → _) k) y) =
      Fin.cons (cxHessian u y) (fun k => cxHessian (ψ k) y) := by
    intro u
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  simp only [maDensity, hc, hH, PtsAddFirst.mixedDisc_cons_add, Complex.add_re]
  ring

theorem PtsAddFirst.pot_cons {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (M : HermLine ι) (L : Fin e → HermLine ι) :
    pot (Fin.cons M L : Fin (e + 1) → HermLine ι) = Fin.cons (fun z => Real.log (M.h z)) (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [pot]

theorem PtsAddFirst.sheetDensity_add {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {e : ℕ} (Q : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1 + 1) → ℂ))
    (L : Fin e → HermLine ι) (M N : HermLine ι) (hM : IsSmoothHerm M) (hN : IsSmoothHerm N)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin (e + 1) → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity Q Ψ (Fin.cons (fun z => Real.log ((M.tensor N).h z)) (pot L)) g y w =
      sheetDensity Q Ψ (Fin.cons (fun z => Real.log (M.h z)) (pot L)) g y w +
        sheetDensity Q Ψ (Fin.cons (fun z => Real.log (N.h z)) (pot L)) g y w := by
  by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
  · simp only [sheetDensity, dif_pos hγ]
    set γ := hγ.choose
    have hs : IsSheet Q Ψ y w γ := hγ.choose_spec
    have han : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ γ y' := (sheet_analyticAt osgood hs).eventually_analyticAt
    have hmc : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts Q := hs.2.mono fun _ h => h.2.1
    have hcd : ∀ {A : HermLine ι}, IsSmoothHerm A →
        ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (A.h (γ y''))) y' := fun hA =>
      (han.and hmc).mono fun y' h => pot_contDiffAt hA h.1 h.2.1
    have hsum : (fun y' => Real.log ((M.tensor N).h (γ y'))) =ᶠ[𝓝 y]
        fun y' => Real.log (M.h (γ y')) + Real.log (N.h (γ y')) := hmc.mono fun y' h =>
      Real.log_mul (M.pos _ h.1).ne' (N.pos _ h.1).ne'
    have hcons : ∀ u : ((Σ k, ι k) → ℂ) → ℝ,
        (fun j y' => (Fin.cons u (pot L) : Fin (e + 1) → _) j (γ y')) =
          Fin.cons (fun y' => u (γ y')) (fun j y' => pot L j (γ y')) := by
      intro u
      funext j y'
      refine Fin.cases ?_ (fun i => ?_) j <;> simp
    rw [hcons, hcons, hcons, PtsAddFirst.maDensity_cons_add _ _ _ _ _
      (PtsAddFirst.cxHessian_add (hcd hM) (hcd hN) hsum), mul_add]
  · simp only [sheetDensity, dif_neg hγ, add_zero]

theorem PtsAddFirst.proof (hInt : PtsIntegrableStatement) : PtsAddFirst.Statement := by
  intro K _ ι _ Q e L M N E t hQ hL hM hN hE ht
  have hL' : ∀ A : HermLine ι, IsSmoothHerm A → ∀ j, IsSmoothHerm ((Fin.cons A L : Fin (e + 1) → _) j) :=
    fun A hA j => Fin.cases hA (fun i => hL i) j
  have hMN : IsSmoothHerm (M.tensor N) := hM.mul hN
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1 + 1) → ℂ), IsGoodProj Q Ψ
  · simp only [ptsIntegral, dif_pos hΨ, ptsIntegralAt]
    have hI : ∀ A : HermLine ι, IsSmoothHerm A → Integrable (fun y => ∑ᶠ w ∈ fibre Q hΨ.choose y,
        sheetDensity Q hΨ.choose (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm E t) y w) := by
      intro A hA
      have h := hInt K ι Q (e + 1) hΨ.choose (Fin.cons A L) E t hQ hΨ.choose_spec (hL' A hA) hE ht
      rwa [PtsAddFirst.pot_cons] at h
    rw [← integral_add (hI M hM) (hI N hN)]
    congr 1
    funext y
    rw [← finsum_mem_add_distrib (fibreFinite K ι Q (e + 1) hΨ.choose hQ hΨ.choose_spec y)]
    exact finsum_mem_congr rfl fun w _ => PtsAddFirst.sheetDensity_add Q _ L M N hM hN _ y w
  · simp only [ptsIntegral, dif_neg hΨ, add_zero]

end GroundTheory.Heights₂.Heights.Inter
