import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapTorusInvariant
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapSameBaseOrbitStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt

theorem eq_on_block {K : Type} {ι : K → Type} {Kk : Type} {ιk : Kk → Type} {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v) {a b : (Σ k, ι k) → ℂ} (h : a ∘ v = b ∘ v)
    {k : K} (hk : k ∈ Set.range κ) (m : ι k) : a ⟨k, m⟩ = b ⟨k, m⟩ := by
  obtain ⟨q, hq⟩ := hb.2.2.2 ⟨k, m⟩ hk
  rw [← hq]
  exact congrFun h q

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X), IsStepHyp M BM p κ v R pr → ∀ (x y' : R.X) (z : (Σ k, ι k) → ℂ), y' ∈ R.U x → pr y' ∉ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → z ∘ v = R.lift x y' → stepPh M BM p v R pr y' = stepGap M BM p z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr H x y' z hy' hpr hz hzv
  obtain ⟨hb, hr, -, H1⟩ := H
  obtain ⟨z₀, hz₀, hz₀v, hz₀o⟩ := H1 y'
  have hex : pr y' ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift y' y' :=
    ⟨hpr, z₀, hz₀, hz₀v⟩
  have hph : stepPh M BM p v R pr y' = stepGap M BM p hex.2.choose := by
    unfold stepPh
    rw [dif_pos hex]
  obtain ⟨hz₁, hz₁v⟩ := hex.2.choose_spec
  rw [hph]
  generalize hex.2.choose = z₁ at hz₁ hz₁v

  have hbase : ∀ {a b : (Σ k, ι k) → ℂ}, a ∘ v = b ∘ v → basePart M.blk a = basePart M.blk b := by
    intro a b hab
    funext q
    exact eq_on_block hb hab (hr q.1.1 (Or.inl q.1.2)) q.2
  have hz₁o : SameOrbit (basePart M.blk z₁) (BM.Rb.lift (pr y') (pr y')) := by
    rw [hbase (hz₁v.trans hz₀v.symm)]
    exact hz₀o

  obtain ⟨c, hc, hcl⟩ := R.compat x y' y' ⟨hy', R.mem_U y'⟩
  set c' : K → ℂ := Function.extend κ c 1 with hc'
  have hc'0 : ∀ k, c' k ≠ 0 := by
    intro k
    by_cases hk : ∃ a, κ a = k
    · obtain ⟨a, rfl⟩ := hk
      rw [hc', hb.1.extend_apply]
      exact hc a
    · rw [hc', Function.extend_apply' _ _ _ hk]
      exact one_ne_zero
  set z₂ : (Σ k, ι k) → ℂ := fun q => c' q.1 * z₁ q with hz₂
  have hz₂m : z₂ ∈ mcPts (mCoordIdeal y) :=
    ((GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main K ι Φ y z₁ c' hc'0).2 hz₁).1
  have hz₂v : z₂ ∘ v = z ∘ v := by
    rw [hzv, hcl]
    funext q
    have h1 : z₁ (v q) = R.lift y' y' q := congrFun hz₁v q
    have h2 : c' (v q).1 = c q.1 := by
      rw [hb.2.2.1 q, hc', hb.1.extend_apply]
    simp only [Function.comp, hz₂, h1, h2]
  have ht : stepGap M BM p z₂ = stepGap M BM p z₁ :=
    GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_torus K ι Φ y Ψ N j M n BM p z₁ c' hc'0 hz₁.1
  have hz₂o : SameOrbit (basePart M.blk z₂) (BM.Rb.lift (pr y') (pr y')) := by
    obtain ⟨d, hd, hdl⟩ := hz₁o
    refine ⟨fun k => c' k.1 * d k, fun k => mul_ne_zero (hc'0 _) (hd k), ?_⟩
    funext q
    have h1 : basePart M.blk z₁ q = d q.1 * BM.Rb.lift (pr y') (pr y') q := congrFun hdl q
    have h2 : basePart M.blk z₂ q = c' q.1.1 * basePart M.blk z₁ q := rfl
    rw [h2, h1, mul_assoc]
  have hg : stepGap M BM p z₂ = stepGap M BM p z :=
    GlobalTheory.T.flag_gap_same_base_orbit K ι Φ y Ψ N j M n BM p (pr y') z₂ z hpr hz₂m hz hz₂o (hbase hz₂v)
      (fun k hk m => eq_on_block hb hz₂v (hr k (Or.inr hk)) m)
  rw [← ht, hg]

end GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt
