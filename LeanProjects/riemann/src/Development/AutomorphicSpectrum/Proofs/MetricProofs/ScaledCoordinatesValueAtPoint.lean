import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartNormPtsA
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Values
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec

theorem isValueAt_aeval {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]
    {y' : (Σ k, ι' k) → Ω} {z : (Σ k, ι' k) → ℂ} {σ : Type} {s : σ → Ω} {w : σ → ℂ}
    (hv : ∀ q, IsValueAt y' (s q) z (w q)) (f : MvPolynomial σ ℤ) :
    IsValueAt y' (aeval s f) z (eval w (map (Int.castRingHom ℂ) f)) := by
  induction f using MvPolynomial.induction_on with
  | C n => simpa using GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_intCast y' z n
  | add p q hp hq => simpa using GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_add hp hq
  | mul_X p i hp => simpa using GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_mul hp (hv i)

theorem mem_mcPts_of_specialise : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] (a : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (z : (Σ k, ι' k) → ℂ) (zt : (Σ k, ι k) → ℂ) (e : K → Ω) (s : (Σ k, ι k) → Ω) (t : K → ℂ), z ∈ mcPts (mCoordIdeal y') → (∀ k, ∃ i, zt ⟨k, i⟩ ≠ 0) → (∀ k, e k ≠ 0) → (∀ k, t k ≠ 0) → (∀ q, a q = e q.1 * s q) → (∀ q, IsValueAt y' (s q) z (t q.1 * zt q)) → zt ∈ mcPts (mCoordIdeal a) := by
  intro K _ ι _ K' _ ι' _ Ω _ a y' z zt e s t hz hzt he ht has hv
  refine ⟨hzt, fun f hf => ?_⟩
  obtain ⟨T, hT, hE⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal a
  rw [hE] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨d, hd⟩ := hT g hg
    have h0 : aeval a g = 0 :=
      (GlobalTheory.CompanionTheory.Ar.PB.form_mem_mCoordIdeal_iff a hd).1 (by rw [hE]; exact Ideal.subset_span hg)
    have ha : a = fun p => e p.1 * s p := funext has
    have h1 : aeval s g = 0 := by
      have h := GroundTheory.Heights₂.Heights.Inter.ChartNormPts.aeval_smul_homog g d hd e s
      rw [← ha, h0] at h
      have hne : (∏ k, e k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (he k)
      exact (mul_eq_zero.1 h.symm).resolve_left hne
    have hval := isValueAt_aeval (w := fun q => t q.1 * zt q) hv g
    rw [h1] at hval
    have h2 := GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_zero hz hval
    rw [ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_homog g d hd t zt] at h2
    have hne : (∏ k, t k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k)
    exact (mul_eq_zero.1 h2).resolve_left hne
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul r x _ hx => simp [smul_eq_mul, map_mul, hx]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec
