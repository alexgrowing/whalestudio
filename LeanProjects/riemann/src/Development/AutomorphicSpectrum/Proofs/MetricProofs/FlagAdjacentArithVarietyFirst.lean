import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatementStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentPluckerOrbitStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.WMem

section Mat

variable {N j : ℕ}

theorem transv_isBlockDiag {a b ca cb : Fin N} (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  have same : ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) := by
    have := a.2
    have := b.2
    have := cb.2
    unfold lastCol at hca
    split_ifs at hca <;> omega
  intro r s hrs
  have e1 : r ≠ s := fun e => hrs (by rw [e])
  rw [Matrix.add_apply, Matrix.one_apply_ne e1, zero_add, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hrs same.symm

theorem transv_det_one {ca cb : Fin N} (hc : (cb : ℕ) = ca + 1) (t : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 := by
  have hne : ca ≠ cb := fun e => by rw [e] at hc; omega
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  rw [Matrix.det_of_lowerTriangular _ fun r c h => ?_]
  · refine Finset.prod_eq_one fun c _ => ?_
    rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, e⟩
    exact hne e
  · have h' : r < c := h
    rw [Matrix.add_apply, Matrix.one_apply_ne h'.ne, Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm h' hlt

end Mat

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem isFlagOf_flagPt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {b : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : ∀ k, b ⟨k, F.c k⟩ = 1) {h : Ψ → Matrix (Fin N) (Fin N) ℂ}
    (hh : ∀ τ, IsBlockDiag j (h τ) ∧ (h τ).det ≠ 0) : M.IsFlagOf F (flagPt M F b h) h := by
  refine ⟨fun k => by rw [basePart_flagPt]; exact hb k, hh, fun p k hp => ⟨1, one_ne_zero, fun m => ?_⟩⟩
  rw [basePart_flagPt, flagPt_step M F b h hp m, one_mul]

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ (l : Fin BM.q), ∀ b' ∈ BM.O l, ∀ (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) → FC.wVec M (BM.F l) (FC.bvec BM l b') h τ a k₀ ca cb t ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM d τ a b k₀ ca cb hb hab hk hca hcb hvar l b' hb' h t hh
  obtain ⟨h1, h2⟩ := GlobalTheory.T.flag_adjacent_plucker_orbit K ι Φ y Ψ N j M τ a b k₀ ca cb hb hab hk hca hcb (BM.F l) (bvec BM l b') h t
  obtain ⟨g1, g2, g3, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good K ι Φ y Ψ N j M n BM l b' hb'
  have hh' : ∀ τ', IsBlockDiag j (Function.update h τ (h τ * (1 + Matrix.single cb ca t)) τ') ∧
      (Function.update h τ (h τ * (1 + Matrix.single cb ca t)) τ').det ≠ 0 := by
    intro τ'
    by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      refine ⟨(hh τ').1.mul (transv_isBlockDiag hb hab hca hcb t), ?_⟩
      rw [Matrix.det_mul, transv_det_one hcb, mul_one]
      exact (hh τ').2
    · rw [Function.update_of_ne e]
      exact hh τ'
  have hbase : basePart M.blk (fstPt k₀ (wVec M (BM.F l) (bvec BM l b') h τ a k₀ ca cb t)) = bvec BM l b' := by
    rw [h1, basePart_flagPt]
  refine (GlobalTheory.T.log_period_statement K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hvar (BM.F l) _ (BM.isFrame l)
    (by rw [hbase]; exact g1) (by rw [hbase]; exact g2) (by rw [hbase]; exact g3)).2 ⟨h, t, ?_, ?_⟩
  · rw [h1]
    exact isFlagOf_flagPt M (BM.F l) g3 hh
  · rw [h2]
    exact isFlagOf_flagPt M (BM.F l) g3 hh'

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.WMem
