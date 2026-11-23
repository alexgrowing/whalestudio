import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem eval_eq_zero_of_mem_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {w : (Σ k, ι k) → ℂ} {f : MRing ι} (hf : f ∈ mCoordIdeal w) : eval w (map (Int.castRingHom ℂ) f) = 0 := by
  have h : (mConeMap w : MRing ι →+* MvPolynomial K ℂ) f = 0 := RingHom.mem_ker.mp hf
  have key : ((MvPolynomial.eval (fun _ : K => (1 : ℂ))).comp (mConeMap w : MRing ι →+* MvPolynomial K ℂ) : MRing ι →+* ℂ)
      = (MvPolynomial.eval w).comp (MvPolynomial.map (Int.castRingHom ℂ)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [mConeMap]
    · intro p
      simp [mConeMap]
  have := RingHom.congr_fun key f
  simp only [RingHom.comp_apply] at this
  rw [← this, h, map_zero]

theorem bvec_good : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, FC.bvec BM l b ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt (BM.F l) (mCoordIdeal (FC.bvec BM l b)) ∧ (∀ k, FC.bvec BM l b ⟨k, (BM.F l).c k⟩ = 1) ∧ SameOrbit (FC.bvec BM l b) (BM.Rb.lift b b) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (BM.Rb.lift b b)) := BM.good l b hb
  have hne : ∀ k, BM.Rb.lift b b ⟨k, (BM.F l).c k⟩ ≠ 0 := fun k =>
    GlobalTheory.CompanionTheory.Ar.PB.FibreCount.chart_ne (hgood.1 k)
  have hbv : ∀ q, GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b q
      = (BM.Rb.lift b b ⟨q.1, (BM.F l).c q.1⟩)⁻¹ * BM.Rb.lift b b q := fun q => by
    simp only [GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec, div_eq_inv_mul]
  have horb : SameOrbit (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b) (BM.Rb.lift b b) := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit
    exact ⟨fun k => (BM.Rb.lift b b ⟨k, (BM.F l).c k⟩)⁻¹, fun k => inv_ne_zero (hne k), funext hbv⟩
  have hideal : mCoordIdeal (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b) = mCoordIdeal (BM.Rb.lift b b) :=
    GlobalTheory.CompanionTheory.Ar.PB.FibreCount.mCoordIdeal_eq_of_orbit horb
  have hone : ∀ k, GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b ⟨k, (BM.F l).c k⟩ = 1 := fun k => by
    rw [hbv]; exact inv_mul_cancel₀ (hne k)
  have hmem : BM.Rb.lift b b ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem b b (BM.Rb.mem_U b)
  have hpt : GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b ∈ mcPts (mCoordIdeal M.x) := by
    simp only [mcPts, Set.mem_ofPred_eq]
    refine ⟨fun k => ⟨(BM.F l).c k, by rw [hone k]; exact one_ne_zero⟩, fun f hf => ?_⟩
    apply eval_eq_zero_of_mem_mCoordIdeal
    rw [hideal]
    exact GlobalTheory.CompanionTheory.Ar.PB.CPts.mCoordIdeal_le hmem hf
  refine ⟨hpt, ?_, hone, horb⟩
  rw [hideal]
  exact hgood

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
