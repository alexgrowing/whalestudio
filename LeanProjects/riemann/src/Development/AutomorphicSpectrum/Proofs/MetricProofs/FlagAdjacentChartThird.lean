import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSecondStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatementStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Mem

theorem blockDiag_transvection {N j : ℕ} {ca cb : Fin N} (hc : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := fun x y hxy => by
  have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) x y = 0 := Matrix.one_apply_ne fun e => hxy (by rw [e])
  have h2 : Matrix.single cb ca t x y = 0 := by
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hxy hc.symm
  rw [Matrix.add_apply, h1, h2, add_zero]

theorem det_transvection' {N : ℕ} {ca cb : Fin N} (hc : ca ≠ cb) (t : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 :=
  Matrix.det_transvection_of_ne cb ca hc.symm t

theorem cols_same_block {N j : ℕ} {a b ca cb : Fin N} (hb : (b : ℕ) = a + 1) (hbj : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
  have := b.2
  have := cb.2
  unfold lastCol at hca
  split_ifs at hca <;> omega

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ w ∈ wD ε V, wPhi M F bl h ε k₀ τ ca cb w ∈ mcPts (wP M τ a k₀ ca cb) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hW w hw
  obtain ⟨-, hE⟩ := GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hW
  obtain ⟨hHB, hbase, hX⟩ := hE w hw
  obtain ⟨hb, hbj, hblk, hca, hcb, hvar, hF, hBC, -, -, -⟩ := hW
  obtain ⟨hmc, hnorm, hgood, -⟩ := hBC.2.2.2.2 (wB ε w) hw
  have hbase' : basePart M.blk (fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb w)) = bl (wB ε w) := hbase
  have hc : ca ≠ cb := fun e => by rw [e] at hcb; omega
  refine (GlobalTheory.T.log_period_statement K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hbj hblk hca hcb hvar F
    (wPhi M F bl h ε k₀ τ ca cb w) hF (by rw [hbase']; exact hmc) (by rw [hbase']; exact hgood)
    (by rw [hbase']; exact hnorm)).2 ⟨fun τ' => wH h ε τ' w, wT ε w, ?_, ?_⟩
  · refine ⟨(hX τ a).1.1, hHB, fun p k hk => ⟨1, one_ne_zero, fun m => ?_⟩⟩
    rw [one_mul]
    exact (hX p.1 p.2).1.2 k hk m
  · refine ⟨(hX τ a).2.1, fun τ' => ?_, fun p k hk => ⟨1, one_ne_zero, fun m => ?_⟩⟩
    · by_cases e : τ' = τ
      · subst e
        rw [Function.update_self]
        refine ⟨(hHB τ').1.mul (blockDiag_transvection (cols_same_block hb hbj hca hcb) _), ?_⟩
        rw [Matrix.det_mul, det_transvection' hc, mul_one]
        exact (hHB τ').2
      · rw [Function.update_of_ne e]
        exact hHB τ'
    · rw [one_mul]
      have hm := (hX p.1 p.2).2.2 k hk m
      by_cases e : p.1 = τ
      · rw [if_pos e] at hm
        rw [e, Function.update_self]
        rw [e] at hm
        exact hm
      · rw [if_neg e] at hm
        rw [Function.update_of_ne e]
        exact hm

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Mem
