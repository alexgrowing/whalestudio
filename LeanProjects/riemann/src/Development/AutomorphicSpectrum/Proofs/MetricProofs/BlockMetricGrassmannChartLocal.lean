import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPointsStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.FlagPoint

theorem stepCols_ne_empty {N j : ℕ} (hj : j ≤ N) (i : Fin N) : stepCols N j i ≠ ∅ := by
  intro h
  have hi' := i.2
  by_cases hi : (i : ℕ) + 1 ≤ j
  · have hm : (⟨N - j, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hi]
      constructor <;> simp
    simp [h] at hm
  · have hm : (⟨0, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hi]
      show 0 < (i : ℕ) + 1 - j
      omega
    simp [h] at hm

theorem val_sum {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {α : Type} (s : Finset α)
    (f : α → Ω) (hf : ∀ a ∈ s, RegAt x (mCoordIdeal z) (f a)) :
    RegAt x (mCoordIdeal z) (∑ a ∈ s, f a) ∧ valAt x (∑ a ∈ s, f a) z = ∑ a ∈ s, valAt x (f a) z := by
  have R := GlobalTheory.CompanionTheory.Ar.PB.ValRing.regAt_valAt_ring K ι Ω x z hz
  induction s using Finset.induction_on with
  | empty => simpa using ⟨R.1, R.2.2.1⟩
  | insert a s ha ih =>
    have ih' := ih fun b hb => hf b (Finset.mem_insert_of_mem hb)
    have h := R.2.2.2.2 (f a) _ (hf a (Finset.mem_insert_self _ _)) ih'.1
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨h.2.1, h.2.2.2.trans (by rw [ih'.2])⟩

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ)
    (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ),
    M.blk p = some k₀ → x₀ ∈ BM.O l → z ∈ mcPts (mCoordIdeal y) →
    SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) →
    ∃ (h : Matrix (Fin N) (Fin N) ℂ) (a : ℂ), IsBlockDiag j h ∧ h.det ≠ 0 ∧ a ≠ 0 ∧
      (∀ I, IsStepRows N j p.2 I → plk M (BM.F l) k₀ z I = a * minorIJ h I (stepCols N j p.2)) ∧
      ∀ m : ι k₀, z ⟨k₀, m⟩ =
        a * ∑ I, valAt M.x ((BM.F l).u ⟨k₀, m⟩ I) (basePart M.blk z) * minorIJ h I (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p k₀ l x₀ z hblk hx hz horb
  obtain ⟨F, hFe⟩ : ∃ F, F = BM.F l := ⟨_, rfl⟩
  rw [← hFe]
  have hF : M.IsFrame F := hFe ▸ BM.isFrame l
  have hG₀ : M.GoodAt F (mCoordIdeal (BM.Rb.lift x₀ x₀)) := hFe ▸ BM.good l x₀ hx
  obtain ⟨hp1, -, hp3⟩ := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  obtain ⟨zb, hzbe⟩ : ∃ zb, zb = basePart M.blk z := ⟨_, rfl⟩
  rw [← hzbe] at horb ⊢
  have hzbm : zb ∈ mcPts (mCoordIdeal M.x) := hzbe ▸ hp1 z hz
  obtain ⟨c₀, hc₀, hc₀e⟩ := horb
  have hG : M.GoodAt F (mCoordIdeal zb) := by
    have e : mCoordIdeal zb = mCoordIdeal (BM.Rb.lift x₀ x₀) := by
      rw [hc₀e]
      exact (GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main _ _ _ M.x (BM.Rb.lift x₀ x₀) c₀ hc₀).1
    rw [e]
    exact hG₀
  have hne : ∀ k : NonPluckerBlocks M.blk, zb ⟨k, F.c k⟩ ≠ 0 := fun k h0 => hG.1 k (by
    show mConeMap zb (X ⟨k, F.c k⟩) = 0
    rw [mConeMap, aeval_X, h0, map_zero, zero_mul])
  let c : K → ℂ := fun k =>
    if h : ∀ p', M.blk p' ≠ some k then (zb ⟨⟨k, h⟩, F.c ⟨k, h⟩⟩)⁻¹ else 1
  have hck : ∀ k : NonPluckerBlocks M.blk, c k.1 = (zb ⟨k, F.c k⟩)⁻¹ := fun k => dif_pos k.2
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases h : ∀ p', M.blk p' ≠ some k
    · rw [hck ⟨k, h⟩]
      exact inv_ne_zero (hne ⟨k, h⟩)
    · have : c k = 1 := dif_neg h
      rw [this]
      exact one_ne_zero
  have hck₀ : c k₀ = 1 := dif_neg fun h => h p hblk
  let z₁ : (Σ k, ι k) → ℂ := fun q => c q.1 * z q
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y) := ((GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main K ι Φ y z c hc).2 hz).1
  let cb : NonPluckerBlocks M.blk → ℂ := fun k => c k.1
  have hb₁ : basePart M.blk z₁ = fun q => cb q.1 * zb q := by
    rw [hzbe]
    rfl
  obtain ⟨hT1, hT2⟩ :=
    GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x zb cb fun k => hc k.1
  obtain ⟨-, hval⟩ := hT2 hzbm
  have hG₁ : M.GoodAt F (mCoordIdeal (basePart M.blk z₁)) := by
    rw [hb₁, hT1]
    exact hG
  have hnorm : ∀ k, basePart M.blk z₁ ⟨k, F.c k⟩ = 1 := fun k => by
    rw [hb₁]
    show c k.1 * zb ⟨k, F.c k⟩ = 1
    rw [hck, inv_mul_cancel₀ (hne k)]
  obtain ⟨hh, -, hτ, hstep⟩ := (hp3 F hF z₁ (hp1 z₁ hz₁) hG₁ hnorm).1 hz₁
  obtain ⟨a, ha, hza⟩ := hstep p k₀ hblk
  have hvals : ∀ s, valAt M.x s (basePart M.blk z₁) = valAt M.x s zb := fun s => by
    rw [hb₁]
    exact hval s
  have hzk : ∀ m : ι k₀, z ⟨k₀, m⟩ =
      a * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) zb * minorIJ (hh p.1) I (stepCols N j p.2) := fun m => by
    have e : z₁ ⟨k₀, m⟩ = z ⟨k₀, m⟩ := by
      show c k₀ * _ = _
      rw [hck₀, one_mul]
    have := hza m
    rw [e] at this
    simpa only [hvals] using this
  refine ⟨hh p.1, a, (hτ p.1).1, (hτ p.1).2, ha, fun I hI => ?_, hzk⟩
  have R := GlobalTheory.CompanionTheory.Ar.PB.ValRing.regAt_valAt_ring _ _ _ M.x zb hzbm
  have hδ : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩) zb * valAt M.x (F.u ⟨k₀, m⟩ I') zb = if I = I' then 1 else 0 := by
    intro I' hI'
    have h1 := (val_sum hzbm Finset.univ (fun m : ι k₀ => F.u' I ⟨k₀, m⟩ * F.u ⟨k₀, m⟩ I') fun m _ =>
      (R.2.2.2.2 _ _ (hG.2.1 ⟨k₀, m⟩ I).2 (hG.2.1 ⟨k₀, m⟩ I').1).1).2
    rw [hF.2.2.1 p k₀ hblk I I' hI hI'] at h1
    have h2 : ∀ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩ * F.u ⟨k₀, m⟩ I') zb =
        valAt M.x (F.u' I ⟨k₀, m⟩) zb * valAt M.x (F.u ⟨k₀, m⟩ I') zb := fun m =>
      (R.2.2.2.2 _ _ (hG.2.1 ⟨k₀, m⟩ I).2 (hG.2.1 ⟨k₀, m⟩ I').1).2.2.1
    simp only [h2] at h1
    rw [← h1]
    split_ifs
    · exact R.2.2.2.1
    · exact R.2.2.1
  have hmin : ∀ I', ¬ IsStepRows N j p.2 I' → minorIJ (hh p.1) I' (stepCols N j p.2) = 0 := fun I' hI' =>
    ((GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le).2.1 (hh p.1) I' (hτ p.1).1 hI').resolve_right
      (stepCols_ne_empty M.j_le p.2)
  have hsum : ∑ I', (∑ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩) zb * valAt M.x (F.u ⟨k₀, m⟩ I') zb) *
      minorIJ (hh p.1) I' (stepCols N j p.2) = minorIJ (hh p.1) I (stepCols N j p.2) := by
    rw [Finset.sum_eq_single I]
    · rw [hδ I hI, if_pos rfl, one_mul]
    · intro I' _ hne'
      by_cases hs : IsStepRows N j p.2 I'
      · rw [hδ I' hs, if_neg (Ne.symm hne'), zero_mul]
      · rw [hmin I' hs, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ I) h
  have hplk : plk M F k₀ z I = ∑ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩) zb * z ⟨k₀, m⟩ := by
    rw [hzbe]
    rfl
  rw [hplk, ← hsum, Finset.mul_sum]
  simp only [hzk, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m _ => ?_
  ring

end GlobalTheory.CompanionTheory.Ar.PB.StepW.FlagPoint
