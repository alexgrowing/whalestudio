import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesStep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSheetHessPSD
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreAssembly
import Development.WeilBound.CoreStatements.FlagImmersions.ArithmeticIntersectionDivisorSupport
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralMultilinearStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionDivisorSupportStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianCombinationSmoothConjStatement
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenFibreExists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt.Ample

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem coneTangent {P : Ideal (MRing J)} {e : ℕ}
    {τ : (Fin e → ℂ) → (Σ k, J k) → ℂ} {y : Fin e → ℂ} (hτ : DifferentiableAt ℂ τ y)
    (hm : ∀ᶠ y' in 𝓝 y, τ y' ∈ mcPts P) (w : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P (τ y) (fderiv ℂ τ y w) := by
  intro f hf
  set F := MvPolynomial.map (Int.castRingHom ℂ) f
  have h0 : (fun y' => MvPolynomial.eval (τ y') F) =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hm] with y' hy'
    exact hy'.2 f hf
  have hD := (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (τ y)).comp y hτ.hasFDerivAt
  have hD0 : HasFDerivAt (fun y' => MvPolynomial.eval (τ y') F) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq h0
  have h1 := congrArg (fun L => L w) (hD.unique hD0)
  simpa [smul_eq_mul, mul_comm] using h1

theorem maDensity_one (f : (Fin 1 → ℂ) → ℝ) (y : Fin 1 → ℂ) :
    maDensity (fun _ : Fin 1 => f) y = 2 / Real.pi * levi f y (Pi.single 0 1) := by
  have hU : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  have hne : (∅ : Finset (Fin 1)) ≠ {0} := by decide
  have key : (cxHessian f y 0 0).re = levi f y (Pi.single 0 1) := by
    simp only [cxHessian, levi]
    generalize fderiv ℝ (fderiv ℝ f) y = H
    generalize H (Pi.single 0 1) (Pi.single 0 1) + H (Complex.I • Pi.single 0 1) (Complex.I • Pi.single 0 1) = u
    simp
  have hm : mixedDisc (fun _ : Fin 1 => cxHessian f y) = cxHessian f y 0 0 := by
    unfold mixedDisc
    rw [hU, Finset.sum_pair hne]
    simp [Matrix.det_unique]
  unfold maDensity
  rw [hm, key]
  simp

theorem geomDeg_nonneg {P W : Ideal (MRing J)} {N : HermLine J} (hN : IsSemipositiveH P N) (hW : P ≤ W) :
    0 ≤ geomDeg W N 1 := by
  classical
  unfold geomDeg ptsIntegral
  split_ifs with hΨ
  · refine MeasureTheory.integral_nonneg fun y => finsum_nonneg fun w => finsum_nonneg fun _ => ?_
    unfold sheetDensity
    split_ifs with hg
    · have hev := hg.choose_spec.2
      set gm := hg.choose
      have hP : ∀ᶠ y' in 𝓝 y, gm y' ∈ mcPts P := hev.mono fun y' h => ⟨h.2.1.1, fun f hf => h.2.1.2 f (hW hf)⟩
      have hz := hP.self_of_nhds
      have han : AnalyticAt ℂ gm y :=
        GroundTheory.Heights₂.Heights.Inter.analyticAt_of_eventually_differentiableAt (hev.mono fun _ h => h.1)
      have hlog : ContDiffAt ℝ 2 (fun z => Real.log (N.h z)) (gm y) :=
        ((hN.1.contDiffAt (StokesStep.isOpen_multicone.mem_nhds hz.1)).of_le
          (WithTop.coe_le_coe.2 le_top)).log (N.pos _ hz.1).ne'
      have h1 := ReciprocityTheory.AnForm.levi_comp (Pi.single 0 1) han hlog
      have h2 := hN.2 _ hz _ (coneTangent han.differentiableAt hP (Pi.single 0 1))
      have h3 := maDensity_one ((fun z => Real.log (N.h z)) ∘ gm) y
      rw [h1] at h3
      rw [_root_.one_mul]
      exact le_of_le_of_eq (mul_nonneg (by positivity) h2) h3.symm
    · exact le_rfl
  · exact le_rfl

end LevelTowerAlt.Ample

theorem LevelTowerAlt.ample_generic_fibre_of_combination : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (N A : HermLine J) (a' : K → ℤ) (m p : ℕ), IsSemipositiveH P N → IsSmoothHerm A → (∀ k, 0 < a' k) → 1 ≤ m → 1 ≤ p → (m : ℤ) • A.a = N.a + (p : ℤ) • a' → AmpleOnGenericFibre P A := by
  intro hI II hII K _ J _ P N A a' m p hN hA ha' hm hp heq W d hd hW hPW
  classical
  have hK : Nonempty K := hW.1
  have hDG := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system ⟨II, hII⟩)
  have hF := GroundTheory.Heights₂.Heights.NumbersDVR.IntNumIsFieldIntersection.full ℚ K J
  have hPos := GroundTheory.Heights₂.Heights.Targets.Positivity.full ℚ J _ hF
  let fs : (K → ℤ) → HermLine J := fun b => HermLine.ofMetrics (fun k => fsMetric (J k)) b
  have hfs : ∀ b, IsSmoothHerm (fs b) := fun b => GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs b
  have hfsn : ∀ b : K → ℤ, (∀ k, 0 ≤ b k) → ∀ W', IsArithVar W' 2 → 0 ≤ geomDeg W' (fs b) 1 := by
    intro b hb W' hW'
    have h1 := hDG K J W' 1 (fun _ => fs b) hW' fun _ => hfs b
    have h2 := (hPos _ 1 (GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hW')).1
      (fun _ => b) fun _ k => hb k
    show 0 ≤ ptsIntegral W' (pot fun _ : Fin 1 => fs b) (fun _ => 1)
    rw [h1]
    exact_mod_cast h2
  let ℓ : Fin 3 → HermLine J := ![N, fs ((p : ℤ) • a' - 1), fs 1]
  have hℓ : ∀ j, IsSmoothHerm (ℓ j) := fun j => by
    fin_cases j
    · exact hN.1
    · exact hfs _
    · exact hfs _
  have hnef : ∀ j W', IsArithVar W' 2 → W ≤ W' → 0 ≤ geomDeg W' (ℓ j) 1 := fun j W' h1 h2 => by
    fin_cases j
    · exact LevelTowerAlt.Ample.geomDeg_nonneg hN (hPW.trans h2)
    · refine hfsn _ (fun k => ?_) W' h1
      have h3 := ha' k
      have h4 : (1 : ℤ) ≤ p := by exact_mod_cast hp
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]
      nlinarith
    · exact hfsn _ (fun _ => zero_le_one) W' h1
  have e1 := (GlobalTheory.T.log_integral_multilinear II hII K J W d (Fin 3) ℓ (fun _ _ => 1) hW hℓ).1
  have e2 := (GlobalTheory.T.log_integral_multilinear II hII K J W d Unit (fun _ => A) (fun _ _ => (m : ℤ)) hW fun _ => hA).1
  have e3 := (GlobalTheory.T.log_integral_multilinear II hII K J W d Unit (fun _ => A) (fun _ _ => (m : ℤ)) hW fun _ => hA).2
    (fun _ => Top.combLine ℓ fun _ => 1) (fun _ => Top.combLine (fun _ : Unit => A) fun _ => (m : ℤ)) (Equiv.refl _)
    (fun _ => (GlobalTheory.T.hermitian_combination_smooth_conj K J _ ℓ _).1 hℓ) (fun _ => (GlobalTheory.T.hermitian_combination_smooth_conj K J _ _ _).1 fun _ => hA) fun _ => by
      show ∑ _ : Unit, (m : ℤ) • A.a = ∑ j, (1 : ℤ) • (ℓ j).a
      rw [Fin.sum_univ_three]
      simp only [Finset.univ_unique, Finset.sum_singleton, one_smul, heq]
      show _ = N.a + ((p : ℤ) • a' - 1) + 1
      abel
  rw [e1, e2] at e3
  have hpos : 0 < ∑ w : Fin d → Fin 3, (∏ k : Fin d, ((1 : ℤ) : ℝ)) *
      ptsIntegral W (fun k z => Real.log ((ℓ (w k)).h z)) (fun _ => 1) := by
    simp only [Int.cast_one, Finset.prod_const_one, _root_.one_mul]
    refine Finset.sum_pos' (fun w _ => ?_) ⟨fun _ => 2, Finset.mem_univ _, ?_⟩
    · exact GlobalTheory.T.ptsIntegral_log_nonneg hI.kleimanNefF (fun K _ J _ => (PB.Known.fieldNumbers ℚ K J).1) PB.Known.divSuppArith II hII K J W d (fun k => ℓ (w k)) hW
        (fun k => hℓ _) fun k => hnef _
    · have h1 := hDG K J W d (fun _ => fs 1) hW fun _ => hfs _
      have h2 := (hPos _ d (GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hW)).2
      show 0 < ptsIntegral W (pot fun _ : Fin d => fs 1) (fun _ => 1)
      rw [h1]
      exact_mod_cast h2
  rw [← e3, Fintype.sum_unique] at hpos
  have hc : (0 : ℝ) ≤ ∏ k : Fin d, ((m : ℤ) : ℝ) := Finset.prod_nonneg fun _ _ => by positivity
  exact (pos_iff_pos_of_mul_pos hpos).1 (lt_of_le_of_ne hc fun h => by
    rw [← h, zero_mul] at hpos
    exact lt_irrefl _ hpos)
