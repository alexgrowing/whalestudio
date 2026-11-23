import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapTorusInvariantStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapSameBaseOrbitStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j n : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem sameOrbit_basePart {M : FlagModel y Ψ N j} {BM : BaseMetric M n} {p : Ψ × Fin N} {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} {e : ℕ} {R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e} {pr : R.X → BM.Rb.X}
    (hS : IsStepHyp M BM p κ v R pr) (x : R.X) {z : (Σ k, ι k) → ℂ} (hz : z ∘ v = R.lift x x) :
    SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x)) := by
  obtain ⟨hbm, hcov, -, hall⟩ := hS
  obtain ⟨z₁, -, h1, h2⟩ := hall x
  have e : basePart M.blk z = basePart M.blk z₁ := by
    funext q
    obtain ⟨r, hr⟩ := hbm.2.2.2 ⟨q.1.1, q.2⟩ (hcov _ (Or.inl q.1.2))
    have h3 : z (v r) = z₁ (v r) := congrFun (hz.trans h1.symm) r
    rw [hr] at h3
    exact h3
  rw [e]
  exact h2

theorem exists_base_const {L : Type} {μ : L → Type} {b₁ b₂ b : (Σ k, μ k) → ℂ} (h₁ : SameOrbit b₁ b)
    (h₂ : SameOrbit b₂ b) : ∃ c : L → ℂ, (∀ k, c k ≠ 0) ∧ ∀ q, b₁ q = c q.1 * b₂ q := by
  obtain ⟨c₁, hc₁, rfl⟩ := h₁
  obtain ⟨c₂, hc₂, rfl⟩ := h₂
  refine ⟨fun k => c₁ k / c₂ k, fun k => div_ne_zero (hc₁ k) (hc₂ k), fun q => ?_⟩
  have := hc₂ q.1
  field_simp

theorem exists_coord {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hbm : IsBlockMap κ v) (k : Kk) (i : ι (κ k)) :
    ∃ m : ιk k, v ⟨k, m⟩ = ⟨κ k, i⟩ := by
  obtain ⟨r, hr⟩ := hbm.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
  have h1 : κ r.1 = κ k := by rw [← hbm.2.2.1 r, hr]
  have h2 : r.1 = k := hbm.1 h1
  obtain ⟨r1, m⟩ := r
  obtain rfl : r1 = k := h2
  exact ⟨m, hr⟩

theorem stepGap_eq {M : FlagModel y Ψ N j} [Fintype Ψ] [DecidableEq Ψ] {BM : BaseMetric M n} {p : Ψ × Fin N} {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} {e : ℕ} {R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e} {pr : R.X → BM.Rb.X}
    (hS : IsStepHyp M BM p κ v R pr) {x x' : R.X} (hpr : pr x = pr x') (hb : pr x ∉ bdry BM.s)
    (hblk : ∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k,
      R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩)
    {z z' : (Σ k, ι k) → ℂ} (hzm : z ∈ mcPts (mCoordIdeal y)) (hz'm : z' ∈ mcPts (mCoordIdeal y))
    (hz : z ∘ v = R.lift x x) (hz' : z' ∘ v = R.lift x' x') :
    stepGap M BM p z = stepGap M BM p z' := by
  have so := sameOrbit_basePart hS x hz
  have so' := sameOrbit_basePart hS x' hz'
  rw [← hpr] at so'
  obtain ⟨cb, hcb, hcbq⟩ := exists_base_const so so'
  obtain ⟨hbm, hcov, -, -⟩ := hS
  have e1 : ∀ r, z (v r) = R.lift x x r := congrFun hz
  have e2 : ∀ r, z' (v r) = R.lift x' x' r := congrFun hz'
  have ha : ∃ a : ℂ, a ≠ 0 ∧ ∀ k, M.blk p = some k → ∀ m : ι k, z ⟨k, m⟩ = a * z' ⟨k, m⟩ := by
    rcases hp : M.blk p with _ | k₀
    · exact ⟨1, one_ne_zero, fun k hk => by simp at hk⟩
    · obtain ⟨k', rfl⟩ := hcov k₀ (Or.inr hp)
      obtain ⟨i, hi⟩ := hzm.1 (κ k')
      obtain ⟨m, hm⟩ := exists_coord hbm k' i
      obtain ⟨a, ha⟩ := hblk k' m hp
      refine ⟨a, fun h0 => hi ?_, fun k hk m' => ?_⟩
      · rw [← hm, e1, ha, h0, zero_mul]
      · obtain rfl : κ k' = k := Option.some.inj hk
        obtain ⟨m'', hm''⟩ := exists_coord hbm k' m'
        rw [← hm'', e1, e2, ha]
  obtain ⟨a, ha0, ha⟩ := ha
  let c : K → ℂ := fun k =>
    if h : ∀ p', M.blk p' ≠ some k then cb ⟨k, h⟩ else if M.blk p = some k then a else 1
  have hc : ∀ k, c k ≠ 0 := fun k => by
    simp only [c]
    split_ifs
    · exact hcb _
    · exact ha0
    · exact one_ne_zero
  have hT := GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main K ι Φ y z' c hc
  have h1 : stepGap M BM p (fun q => c q.1 * z' q) = stepGap M BM p z' :=
    GlobalTheory.T.flag_gap_torus_invariant K ι Φ y Ψ N j M n BM p z' c hc hz'm.1
  rw [← h1]
  refine GlobalTheory.T.flag_gap_same_base_orbit K ι Φ y Ψ N j M n BM p (pr x) z _ hb hzm (hT.2 hz'm).1 so ?_ ?_
  · funext q
    have : c q.1.1 = cb q.1 := dif_pos q.1.2
    show basePart M.blk z q = c q.1.1 * z' ⟨q.1.1, q.2⟩
    rw [this, hcbq]
    rfl
  · intro k hk m
    have : c k = a := (dif_neg fun h => h p hk).trans (if_pos hk)
    show z ⟨k, m⟩ = c k * z' ⟨k, m⟩
    rw [this, ha k hk]

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X), IsStepHyp M BM p κ v R pr → ∀ x x', pr x = pr x' → (∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k, R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩) → stepPh M BM p v R pr x = stepPh M BM p v R pr x' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hS x x' hpr hblk
  by_cases hb : pr x ∈ bdry BM.s
  · have hb' : pr x' ∈ bdry BM.s := hpr ▸ hb
    rw [stepPh, stepPh, dif_neg fun h => h.1 hb, dif_neg fun h => h.1 hb']
  · have hb' : pr x' ∉ bdry BM.s := hpr ▸ hb
    obtain ⟨z₁, hz₁, hv₁, -⟩ := hS.2.2.2 x
    obtain ⟨z₂, hz₂, hv₂, -⟩ := hS.2.2.2 x'
    have h1 : pr x ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x := ⟨hb, z₁, hz₁, hv₁⟩
    have h2 : pr x' ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x' x' := ⟨hb', z₂, hz₂, hv₂⟩
    rw [stepPh, stepPh, dif_pos h1, dif_pos h2]
    exact stepGap_eq hS hpr hb hblk h1.2.choose_spec.1 h2.2.choose_spec.1 h1.2.choose_spec.2 h2.2.choose_spec.2

end GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp
