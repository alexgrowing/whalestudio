import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAddFirst
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDeLeSemiPos
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegrePartition
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LogRegLineTensor
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LelongSectionLimit
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LelongChartLimit
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem sheetDensity_finset_sum {e : ℕ} (Q : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {T : Type*} (S : Finset T) (u : T → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity Q Ψ φ (fun z => ∑ t ∈ S, u t z) y w = ∑ t ∈ S, sheetDensity Q Ψ φ (u t) y w := by
  unfold sheetDensity
  split_ifs <;> simp [Finset.sum_mul]

theorem integrable_fibreSum_degZero (hInt : PtsIntegrableStatement) {Q : Ideal (MRing ι)} {e : ℕ}
    (hQ : IsArithVar Q (e + 1)) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ : IsGoodProj Q Ψ)
    {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {u : ((Σ k, ι k) → ℂ) → ℝ}
    (hu : IsDegZeroSmooth u) :
    Integrable (fun y => ∑ᶠ w ∈ fibre Q Ψ y, sheetDensity Q Ψ (pot L) u y w) := by
  have hsm : IsSmoothHerm (HermLine.ofWeight u hu.2) :=
    Real.contDiff_exp.comp_contDiffOn hu.1.neg
  have h := hInt K ι Q e Ψ L (HermLine.ofWeight u hu.2) 1 hQ hΨ hL hsm
    (Inter.isSectionOn_one hQ rfl)
  have hlog : logNorm (HermLine.ofWeight u hu.2) 1 = u := by
    funext z
    simp [logNorm, HermLine.ofWeight, Real.log_inv, Real.log_exp]
  rwa [hlog] at h

theorem ptsIntegral_finset_sum (hInt : PtsIntegrableStatement) {Q : Ideal (MRing ι)} {e : ℕ}
    (hQ : IsArithVar Q (e + 1)) {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {T : Type*}
    (S : Finset T) {u : T → ((Σ k, ι k) → ℂ) → ℝ} (hu : ∀ t, IsDegZeroSmooth (u t)) :
    ptsIntegral Q (pot L) (fun z => ∑ t ∈ S, u t z) = ∑ t ∈ S, ptsIntegral Q (pot L) (u t) := by
  classical
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ
  · simp only [ptsIntegral, dif_pos hΨ, ptsIntegralAt]
    rw [← integral_finsetSum S fun t _ =>
      integrable_fibreSum_degZero hInt hQ hΨ.choose_spec hL (hu t)]
    congr 1
    funext y
    have hfin := fibreFinite K ι Q e hΨ.choose hQ hΨ.choose_spec y
    simp only [sheetDensity_finset_sum]
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ => (finsum_mem_eq_finite_toFinset_sum _ hfin).symm
  · simp [ptsIntegral, dif_neg hΨ]

theorem LelongSectionLimit.proof (hInt : PtsIntegrableStatement) (hChart : LelongChartLimit.Statement) :
    LelongSectionLimit.Statement := by
  classical
  intro K _ ι _ P n L A B s hP hL hA hB hBa hs
  obtain ⟨a, ha, hsa, -⟩ := id hs
  have hne : ∀ k, Nonempty (ι k) := fun k => ⟨(hP.2.1.2.2 k).choose⟩
  obtain ⟨δ, hδ, ρ, hρ, hsum, hsupp⟩ := SegrePartition.proof K ι hne
  have hv := isDegZeroSmooth_log hB hBa
  have hg : ∀ i, IsDegZeroSmooth (fun z => ρ i z * Real.log (B.h z)) := fun i => (hρ i).mul hv
  have hvsum : (fun z => Real.log (B.h z)) = fun z => ∑ i, ρ i z * Real.log (B.h z) :=
    funext fun z => by rw [← Finset.sum_mul, hsum, one_mul]

  have hlim := tendsto_finsetSum (Finset.univ : Finset ((k : K) → ι k)) fun i _ =>
    hChart K ι P n L A s _ i δ hP hL hA hs (hg i) hδ fun z hz => by simp [hsupp i z hz]

  have hfin : {W | W ∈ divSupp P s ∧ IsHorizontal W}.Finite := (divSupp_finite P s).subset fun _ h => h.1
  have hsplit : ∀ f : Ideal (MRing ι) → ℝ,
      ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), f W = ∑ W ∈ hfin.toFinset, f W :=
    fun f => finsum_mem_eq_finite_toFinset_sum f hfin
  have hW : ∀ W ∈ hfin.toFinset, ptsIntegral W (pot L) (fun z => Real.log (B.h z)) =
      ∑ i, ptsIntegral W (pot L) (fun z => ρ i z * Real.log (B.h z)) := by
    intro W hW
    rw [Set.Finite.mem_toFinset] at hW
    have hWar : IsArithVar W (n + 1) := (divSuppArith K ι P (n + 1) A s W hP hs hW.1).1 hW.2
    rw [hvsum]
    exact ptsIntegral_finset_sum hInt hWar hL Finset.univ hg
  have hrhs : (∑ i, ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => ρ i z * Real.log (B.h z))) =
      ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z)) := by
    simp only [hsplit]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun W hW' => ?_
    rw [hW W hW', Finset.mul_sum]
  rw [hrhs] at hlim

  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
  set M := (regLine A s ε ha hsa).tensor A
  have hM : IsSmoothHerm M := (isSmoothHerm_regLine hA hε ha hsa).mul hA
  have hcongr : ∀ g : ((Σ k, ι k) → ℂ) → ℝ,
      ptsIntegral P
          (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
            (pot L)) g = ptsIntegral P (pot (Fin.cons M L)) g := by
    intro g
    rw [Inter.PtsAddFirst.pot_cons]
    refine Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun j => ?_) (fun _ _ => rfl)
    refine Fin.cases ?_ (fun i => ?_) j
    · intro z hz
      simp only [Fin.cons_zero]
      exact (log_regLine_tensor A s hε ha hsa z hz.1).symm
    · intro z _
      simp only [Fin.cons_succ]
  have hML : ∀ j, IsSmoothHerm ((Fin.cons M L : Fin (n + 1) → HermLine ι) j) :=
    fun j => Fin.cases hM (fun i => hL i) j
  simp only [hcongr]
  rw [hvsum]
  exact (ptsIntegral_finset_sum hInt hP hML Finset.univ hg).symm

end GroundTheory.Heights₂.Heights.Targets
