import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisor
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartIntegral
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisorComponents
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisorLength
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartIntegralPoints
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsSectionOn ptsIntegral pot segre divSupp IsHorizontal
  multAt divSupp_finite divSuppArith)
open GroundTheory.Heights₂.Heights (varInt localMult IsDegZeroSmooth segreChartSet segreChartComponents chartLift
  SegreChartIntegral.Statement)

theorem segreChartSet_mono {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)}
    (h : P ≤ W) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    segreChartSet W σ i ⊆ segreChartSet P σ i := by
  rintro _ ⟨z, ⟨hz1, hz2⟩, hzi, rfl⟩
  exact ⟨z, ⟨hz1, fun f hf => hz2 f (h hf)⟩, hzi, rfl⟩

theorem ptsIntegral_eq_sum_chart (hInt : SegreChartIntegral.Statement) (hPts : SegreChartIntegralPoints.Statement)
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)} {n m : ℕ}
    {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k} {L : Fin n → HermLine ι} {g : ((Σ k, ι k) → ℂ) → ℝ} {δ : ℝ}
    {G : (Fin m → ℂ) → ℝ} {Φ : Fin n → (Fin m → ℂ) → ℝ} (hW : IsArithVar W (n + 1)) (hPW : P ≤ W)
    (hL : ∀ j, IsSmoothHerm (L j)) (hg : IsDegZeroSmooth g) (hδ : 0 < δ)
    (hsupp : ∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0)
    (hgerm : ∀ x ∈ segreChartSet P σ i,
      G =ᶠ[𝓝 x] g ∘ chartLift σ i ∧ ∀ j, Φ j =ᶠ[𝓝 x] pot L j ∘ chartLift σ i) :
    ptsIntegral W (pot L) g = ∑ W' ∈ segreChartComponents W σ i, varInt W' n G Φ := by
  have hsub := segreChartSet_mono hPW σ i
  cases n with
  | zero => exact hPts K ι W m σ i L g δ G Φ hW hg hδ hsupp fun x hx => (hgerm x (hsub hx)).1
  | succ e => exact hInt K ι W e m σ i L g δ G Φ hW hL hg hδ (Or.inl hsupp) fun x hx => hgerm x (hsub hx)

theorem ChartDivisorCompare.proof (hInt : SegreChartIntegral.Statement) (hPts : SegreChartIntegralPoints.Statement)
    (hComp : ChartDivisorComponents.Statement) (hLen : ChartDivisorLength.Statement) :
    ChartDivisorCompare.Statement := by
  classical
  intro K _ _ ι _ P n m σ i L A s g δ G Φ hP hL hs hg hδ hsupp hgerm
  obtain ⟨hmin, hdisj⟩ := hComp K ι P n m σ i A s hP hs
  have hfin : {W | W ∈ divSupp P s ∧ IsHorizontal W}.Finite := (divSupp_finite P s).subset fun _ h => h.1
  set S := hfin.toFinset with hS
  set T := S.biUnion fun W => segreChartComponents W σ i with hT
  have hA : ∀ J ∈ segreChartComponents P σ i,
      ∑ᶠ (W' : Ideal (MvPolynomial (Fin m) ℂ)) (_ : W' ∈ (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {chartSection σ i s}) W' : ℝ) * varInt W' n G Φ =
        ∑ W' ∈ T, if J ≤ W' then
          (localMult (J ⊔ Ideal.span {chartSection σ i s}) W' : ℝ) * varInt W' n G Φ else 0 := by
    intro J hJ
    have hset : (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes = ↑(T.filter fun W' => J ≤ W') := by
      ext W'
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, hmin J hJ W', hT, hS, Finset.mem_biUnion,
        Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      tauto
    rw [hset, finsum_mem_coe_finset, Finset.sum_filter]
  have hB : ∀ W ∈ S, ∀ W' ∈ segreChartComponents W σ i,
      ∑ J ∈ segreChartComponents P σ i, (if J ≤ W' then
          (localMult (J ⊔ Ideal.span {chartSection σ i s}) W' : ℝ) * varInt W' n G Φ else 0) =
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * varInt W' n G Φ := by
    intro W hW W' hW'
    rw [Set.Finite.mem_toFinset] at hW
    rw [← Finset.sum_filter, ← Finset.sum_mul, ← Nat.cast_sum, hLen K ι P n m σ i A s hP hs W hW.1 hW.2 W' hW']
  have hdisjT : (↑S : Set (Ideal (MRing ι))).PairwiseDisjoint fun W => segreChartComponents W σ i := by
    intro W₁ h₁ W₂ h₂ hne
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at h₁ h₂
    exact Finset.disjoint_left.2 fun W' hW₁ hW₂ => hne (hdisj W₁ W₂ h₁ h₂ W' hW₁ hW₂)
  rw [Finset.sum_congr rfl hA, Finset.sum_comm, Finset.sum_biUnion hdisjT,
    Finset.sum_congr rfl fun W hW => Finset.sum_congr rfl (hB W hW), eq_comm]
  refine (finsum_mem_eq_finite_toFinset_sum
    (fun W => (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) g) hfin).trans ?_
  refine Finset.sum_congr rfl fun W hW => ?_
  rw [← Finset.mul_sum]
  rw [Set.Finite.mem_toFinset] at hW
  have hWv : IsArithVar W (n + 1) := (divSuppArith K ι P (n + 1) A s W hP hs hW.1).1 hW.2
  rw [ptsIntegral_eq_sum_chart hInt hPts hWv (le_sup_left.trans hW.1.1.1.2) hL hg hδ hsupp hgerm]

end GroundTheory.Heights₂.Heights.Targets
