import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverTwoFramesComparison
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryTwistMinorOtherStepsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryTwistMinorScalarStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockTriangularOfProportionalMinorsStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Same

section Cols

variable {N j : ℕ} {a b ca cb : Fin N}

theorem cols_next (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hcase : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) :
    stepCols N j b = insert cb (stepCols N j a) ∧ cb ∉ stepCols N j a ∧ ca ∈ stepCols N j a := by
  have hbN := b.2
  rcases hcase with h | h
  · have h1 : (a : ℕ) + 1 ≤ j := by omega
    have h2 : (b : ℕ) + 1 ≤ j := by omega
    simp only [lastCol, if_pos h1] at hca
    refine ⟨?_, ?_, ?_⟩
    · ext c
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1, if_pos h2,
        Finset.mem_insert, Fin.ext_iff]
      omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1]
      omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1]
      omega
  · have h1 : ¬ (a : ℕ) + 1 ≤ j := by omega
    have h2 : ¬ (b : ℕ) + 1 ≤ j := by omega
    simp only [lastCol, if_neg h1] at hca
    refine ⟨?_, ?_, ?_⟩
    · ext c
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h1, if_neg h2,
        Finset.mem_insert, Fin.ext_iff]
      omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h1]
      omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h1]
      omega

theorem cols_prev (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hcase : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) {a' : Fin N} (ha' : (a' : ℕ) + 1 = a) (hp : IsProperStep N j a') :
    stepCols N j a' = (stepCols N j a).erase ca := by
  have hbN := b.2
  have hp1 := hp.1
  rcases hcase with h | h
  · have h1 : (a : ℕ) + 1 ≤ j := by omega
    have h2 : (a' : ℕ) + 1 ≤ j := by omega
    simp only [lastCol, if_pos h1] at hca
    ext c
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1, if_pos h2,
      Finset.mem_erase, ne_eq, Fin.ext_iff]
    omega
  · have h1 : ¬ (a : ℕ) + 1 ≤ j := by omega
    have h2 : ¬ (a' : ℕ) + 1 ≤ j := by omega
    simp only [lastCol, if_neg h1] at hca
    ext c
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h1, if_neg h2,
      Finset.mem_erase, ne_eq, Fin.ext_iff]
    omega

theorem cols_first (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hcase : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (h0 : (a : ℕ) = 0 ∨ (a : ℕ) = j) :
    (stepCols N j a).erase ca = ∅ := by
  have hbN := b.2
  rw [Finset.eq_empty_iff_forall_notMem]
  intro c
  by_cases h1 : (a : ℕ) + 1 ≤ j
  · simp only [lastCol, if_pos h1] at hca
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1,
      Finset.mem_erase, ne_eq, Fin.ext_iff]
    omega
  · simp only [lastCol, if_neg h1] at hca
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h1,
      Finset.mem_erase, ne_eq, Fin.ext_iff]
    omega

theorem transv_blockDiag (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hcase : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  have hbN := b.2
  have hs : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
    by_cases h1 : (a : ℕ) + 1 ≤ j
    · simp only [lastCol, if_pos h1] at hca
      omega
    · simp only [lastCol, if_neg h1] at hca
      omega
  intro r s h
  have hrs : r ≠ s := fun e => h (by rw [e])
  rw [Matrix.add_apply, Matrix.one_apply_ne hrs, zero_add, Matrix.single_apply_of_ne]
  rintro ⟨rfl, rfl⟩
  exact h hs.symm

theorem fac_next (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hcase : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hp : ¬ IsProperStep N j b) (h : Matrix (Fin N) (Fin N) ℂ) :
    Fib.facOf N j a h b = minorIJ h (stepCols N j b) (stepCols N j b) := by
  have hbN := b.2
  by_cases h1 : (b : ℕ) + 1 = j
  · have h2 : (a : ℕ) < j := by omega
    have e : stepCols N j b = wIdx N j := by
      ext c
      have := c.2
      simp only [stepCols, wIdx, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1.le]
      omega
    rw [e]
    simp only [Fib.facOf, if_pos h1, if_pos h2]
  · have h3 : (b : ℕ) + 1 = N := by
      by_contra h3
      exact hp ⟨h1, h3⟩
    have h4 : ¬ (b : ℕ) + 1 ≤ j := by omega
    have e : stepCols N j b = omIdx N j := by
      ext c
      simp only [stepCols, omIdx, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h4]
      omega
    rw [e]
    simp only [Fib.facOf, if_neg h1]

theorem fac_prev (hb : (b : ℕ) = a + 1) {a' : Fin N} (ha' : (a' : ℕ) + 1 = a) (hp : ¬ IsProperStep N j a')
    (h : Matrix (Fin N) (Fin N) ℂ) : Fib.facOf N j a h a' = 1 ∧ (a : ℕ) = j := by
  have hbN := b.2
  have h1 : (a' : ℕ) + 1 = j := by
    by_contra h1
    exact hp ⟨h1, by omega⟩
  have h2 : ¬ (a : ℕ) < j := by omega
  exact ⟨by simp only [Fib.facOf, if_pos h1, if_neg h2], by omega⟩

theorem fac_ne_zero (hj : j ≤ N) (i : Fin N) {h : Matrix (Fin N) (Fin N) ℂ} (hh : IsBlockDiag j h) (hd : h.det ≠ 0)
    (a : Fin N) : Fib.facOf N j a h i ≠ 0 := by
  have hN : 0 < N := by have := i.2; omega
  have hd' := GlobalTheory.CompanionTheory.Ar.PB.CPts.detFac_ne_zero hj (⟨N - 1, by omega⟩ : Fin N) hh hd
  have e1 : j ≤ N - 1 + 1 := by omega
  simp only [detFac, if_pos e1, show N - 1 + 1 = N by omega, if_true, if_pos hj] at hd'
  simp only [Fib.facOf]
  have := left_ne_zero_of_mul hd'
  have := right_ne_zero_of_mul hd'
  split_ifs <;> first | assumption | simp

end Cols

section Xi

variable {Ψ : Type} [DecidableEq Ψ] {N : ℕ}

theorem xi_sum (τ : Ψ) {a b : Fin N} (hb : (b : ℕ) = a + 1) (D : Fin N → ℝ) (D₀ : ℝ)
    (hD : ∀ a' : Fin N, (a' : ℕ) + 1 = a → D a' = D₀) (h0 : (a : ℕ) = 0 → D₀ = 0) :
    ∑ i, (xiCoef τ a (τ, i) : ℝ) * D i = D₀ + D b - 2 * D a := by
  have e : ∀ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * D i =
      (if (i : ℕ) + 1 = a then D i else 0) + (if i = b then D i else 0) - (if i = a then 2 * D i else 0) := by
    intro i
    have e1 : ((i : ℕ) = (a : ℕ) + 1) ↔ i = b := by rw [Fin.ext_iff, hb]
    simp only [xiCoef, if_true, e1]
    push_cast
    split_ifs <;> first | ring | simp
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 2
  by_cases ha : (a : ℕ) = 0
  · rw [h0 ha]
    exact Finset.sum_eq_zero fun i _ => if_neg (by omega)
  · have hlt := a.2
    rw [Finset.sum_eq_single (⟨a - 1, by omega⟩ : Fin N)]
    · rw [if_pos (show ((a : ℕ) - 1) + 1 = a by omega)]
      exact hD _ (show ((a : ℕ) - 1) + 1 = a by omega)
    · intro i _ hne
      refine if_neg fun e => hne (Fin.ext ?_)
      show (i : ℕ) = (a : ℕ) - 1
      omega
    · simp

end Xi

section Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

theorem log_fs_smul (d : K → ℤ) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((fsHerm ι d).h fun p => c p.1 * z p) =
      Real.log ((fsHerm ι d).h z) + ∑ k, (d k : ℝ) * Real.log ‖c k‖ := by
  have hn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hc k)
  rw [(fsHerm ι d).smul c z hc,
    Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hn k)) ((fsHerm ι d).pos z hz).ne',
    Real.log_prod (fun k _ => zpow_ne_zero _ (hn k)), add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => Real.log_zpow _ _

theorem dy_sum_some (M : FlagModel y Ψ N j) {p : Ψ × Fin N} {k₀ : K} (hk : M.blk p = some k₀) {c : K → ℂ}
    (hc : ∀ k, (∀ p', M.blk p' ≠ some k) → c k = 1) :
    ∑ k, (M.dy p k : ℝ) * Real.log ‖c k‖ = Real.log ‖c k₀‖ := by
  rw [Finset.sum_eq_single k₀]
  · have e : M.dy p k₀ = 1 := by
      unfold FlagModel.dy
      rw [dif_neg (fun h => h p hk), if_pos hk]
    rw [e]
    simp
  · intro k _ hne
    by_cases h : ∀ p', M.blk p' ≠ some k
    · rw [hc k h]
      simp
    · have e : M.dy p k = 0 := by
        unfold FlagModel.dy
        rw [dif_neg h, if_neg fun e => hne (by rw [hk] at e; exact (Option.some_injective _ e).symm)]
      rw [e]
      simp
  · simp

theorem dy_sum_none (M : FlagModel y Ψ N j) {p : Ψ × Fin N} (hp : M.blk p = none) {c : K → ℂ}
    (hc : ∀ k, (∀ p', M.blk p' ≠ some k) → c k = 1) :
    ∑ k, (M.dy p k : ℝ) * Real.log ‖c k‖ = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : ∀ p', M.blk p' ≠ some k
  · rw [hc k h]
    simp
  · have e : M.dy p k = 0 := by
      unfold FlagModel.dy
      rw [dif_neg h, if_neg fun e => by rw [hp] at e; exact absurd e (by simp)]
    rw [e]
    simp

theorem base_one (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {z z' : (Σ k, ι k) → ℂ} {c : K → ℂ}
    (hz' : z' = fun p => c p.1 * z p) (h₁ : ∀ k, basePart M.blk z ⟨k, F.c k⟩ = 1)
    (h₂ : ∀ k, basePart M.blk z' ⟨k, F.c k⟩ = 1) : ∀ k, (∀ p', M.blk p' ≠ some k) → c k = 1 := by
  intro k hk
  have a₁ : z ⟨k, F.c ⟨k, hk⟩⟩ = 1 := h₁ ⟨k, hk⟩
  have a₂ : z' ⟨k, F.c ⟨k, hk⟩⟩ = 1 := h₂ ⟨k, hk⟩
  rw [hz'] at a₂
  have a₃ : c k * z ⟨k, F.c ⟨k, hk⟩⟩ = 1 := a₂
  rwa [a₁, mul_one] at a₃

theorem base_eq {blk : Ψ × Fin N → Option K} {z z' : (Σ k, ι k) → ℂ} {c : K → ℂ}
    (hz' : z' = fun p => c p.1 * z p) (hc : ∀ k, (∀ p', blk p' ≠ some k) → c k = 1) :
    basePart blk z' = basePart blk z := by
  funext q
  show z' ⟨q.1.1, q.2⟩ = z ⟨q.1.1, q.2⟩
  rw [hz']
  show c q.1.1 * _ = _
  rw [hc _ q.1.2, one_mul]

theorem minors_prop (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {bp : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : bp ∈ mcPts (mCoordIdeal M.x)) (hF : M.IsFrame F) (hG : M.GoodAt F (mCoordIdeal bp)) {p : Ψ × Fin N} {k : K}
    (hk : M.blk p = some k) {z z' : (Σ k, ι k) → ℂ} {c : K → ℂ} (hz' : z' = fun q => c q.1 * z q)
    (hz : basePart M.blk z = bp) (hzb : basePart M.blk z' = bp) {g g' : Matrix (Fin N) (Fin N) ℂ}
    (hg : IsBlockDiag j g) (hg' : IsBlockDiag j g') (e : M.ExactAt F p z g) (e' : M.ExactAt F p z' g')
    (I : Finset (Fin N)) : minorIJ g' I (stepCols N j p.2) = c k * minorIJ g I (stepCols N j p.2) := by
  refine Ind.minor_eq_of_plk M hb hF hG hk hg' hg (fun m => ?_) I
  have a := e.2 k hk m
  have a' := e'.2 k hk m
  rw [hz] at a
  rw [hzb] at a'
  simp only [plk]
  rw [← a, ← a', hz']

theorem val_ups_ne (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {bp : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : bp ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal bp)) {p : Ψ × Fin N} (hp : M.blk p = none) :
    valAt M.x (F.υ p) bp ≠ 0 := by
  obtain ⟨h0, r1, r2⟩ := hG.2.2 p hp
  have e := (reg_mul hb r1 r2).2
  rw [mul_inv_cancel₀ h0] at e
  have e1 : valAt M.x (1 : M.Ω) bp = 1 := map_one (regVal M.x hb)
  rw [e1] at e
  exact left_ne_zero_of_mul (e ▸ one_ne_zero)

end Lines

section Scal

variable {N j : ℕ}

theorem minor_one (S : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (S.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem exists_minor_ne (hj : j ≤ N) (i : Fin N) {h : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) :
    ∃ I, minorIJ h I (stepCols N j i) ≠ 0 := by
  by_contra hc
  push_neg at hc
  have e := (GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj).1 h⁻¹ h (stepCols N j i) (stepCols N j i)
  rw [Matrix.nonsing_inv_mul _ hd.isUnit, minor_one, Finset.sum_eq_zero fun I _ => by rw [hc I, mul_zero]] at e
  exact one_ne_zero e

theorem scal_eq (hj : j ≤ N) (i : Fin N) {h B : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) (hB : IsBlockDiag j B)
    (hBt : B.BlockTriangular id) {c : ℂ}
    (e : ∀ I, minorIJ (h * B) I (stepCols N j i) = c * minorIJ h I (stepCols N j i)) :
    c = ∏ x ∈ stepCols N j i, B x x := by
  obtain ⟨I, hI⟩ := exists_minor_ne hj i hd
  have a := e I
  rw [(GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj).2.2.1 h B I hB hBt] at a
  apply mul_right_cancel₀ hI
  rw [← a, mul_comm]

end Scal

section Main

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def wt (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (F : FrameData ι Ψ N M.Ω M.blk)
    (bp : (Σ k, baseIdx ι M.blk k) → ℂ) (g : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : ℝ :=
  if IsProperStep N j i then 0 else Real.log ‖valAt M.x (F.υ (τ, i)) bp * Fib.facOf N j a g i‖

theorem normRhs_eq (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (F : FrameData ι Ψ N M.Ω M.blk)
    (z₀ z₁ : (Σ k, ι k) → ℂ) (h : Matrix (Fin N) (Fin N) ℂ) {t : ℂ} (ht : t ≠ 0)
    (hv : ∀ i, ¬ IsProperStep N j i → valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) ≠ 0)
    (hf : ∀ i, Fib.facOf N j a h i ≠ 0) :
    normRhs M τ a F z₀ z₁ h t = Real.log ‖t‖ + ∑ i, (xiCoef τ a (τ, i) : ℝ) *
      (wt M τ a F (basePart M.blk z₀) h i + (1 / 2) * (Real.log ((fsHerm ι (M.dy (τ, i))).h z₀) +
        Real.log ((fsHerm ι (M.dy (τ, i))).h z₁))) := by
  have hu : ∀ i, (if IsProperStep N j i then (1 : ℂ) else
      valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) * Fib.facOf N j a h i) ≠ 0 := fun i => by
    split_ifs with hp
    · exact one_ne_zero
    · exact mul_ne_zero (hv i hp) (hf i)
  have hn : ∀ i, ‖(if IsProperStep N j i then (1 : ℂ) else
      valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) * Fib.facOf N j a h i) ^ xiCoef τ a (τ, i)‖ ≠ 0 :=
    fun i => norm_ne_zero_iff.2 (zpow_ne_zero _ (hu i))
  have e1 : Real.log ‖t * ∏ i : Fin N, (if IsProperStep N j i then (1 : ℂ) else
      valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) * Fib.facOf N j a h i) ^ xiCoef τ a (τ, i)‖ =
      Real.log ‖t‖ + ∑ i, (xiCoef τ a (τ, i) : ℝ) * wt M τ a F (basePart M.blk z₀) h i := by
    rw [norm_mul, norm_prod, Real.log_mul (norm_ne_zero_iff.2 ht)
      (Finset.prod_ne_zero_iff.2 fun i _ => hn i), Real.log_prod fun i _ => hn i]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_zpow, Real.log_zpow]
    simp only [wt]
    split_ifs <;> simp
  have e2 : ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) =
      ∑ i, (xiCoef τ a (τ, i) : ℝ) * (Real.log ((fsHerm ι (M.dy (τ, i))).h z₀) +
        Real.log ((fsHerm ι (M.dy (τ, i))).h z₁)) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
    · intro τ' _ hne
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [xiCoef, hne]
    · simp
  unfold normRhs
  rw [e2]
  refine (congrArg₂ (· + ·) e1 rfl).trans ?_
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, add_assoc]
  congr 2
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

end Main

section Thm

theorem normRhs_same : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (z₀ z₁ z₀' z₁' : (Σ k, ι k) → ℂ) (h h' : Matrix (Fin N) (Fin N) ℂ) (t t' : ℂ), basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) → (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) → basePart M.blk z₁ = basePart M.blk z₀ → M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → SameOrbit z₀ z₀' → SameOrbit z₁ z₁' → IsBlockDiag j h → h.det ≠ 0 → IsBlockDiag j h' → h'.det ≠ 0 → t ≠ 0 → t' ≠ 0 → (∀ i, M.ExactAt F (τ, i) z₀ h) → (∀ i, M.ExactAt F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → (∀ i, M.ExactAt F (τ, i) z₀' h') → (∀ i, M.ExactAt F (τ, i) z₁' (h' * (1 + Matrix.single cb ca t'))) → normRhs M τ a F z₀ z₁ h t = normRhs M τ a F z₀' z₁' h' t' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b k₀ ca cb hb hcase hk₀ hca hcb F z₀ z₁ z₀' z₁' h h' t t' hbp hn0 hn1 hb1 hF hG
    ho0 ho1 hh hd hh' hd' ht ht' e0 e1 e0' e1'
  have hj := M.j_le
  obtain ⟨c0, hc0, q0⟩ := orbit_symm ho0
  obtain ⟨c1, hc1, q1⟩ := orbit_symm ho1
  have ob0 := base_one M F q0 (e0 a).1 (e0' a).1
  have ob1 := base_one M F q1 (e1 a).1 (e1' a).1
  have bz0 : basePart M.blk z₀' = basePart M.blk z₀ := base_eq q0 ob0
  have bz1 : basePart M.blk z₁' = basePart M.blk z₀ := (base_eq q1 ob1).trans hb1
  have hT := transv_blockDiag (a := a) (b := b) (ca := ca) (cb := cb) hj hb hcase hca hcb
  have m0 : ∀ i k, M.blk (τ, i) = some k → ∀ I, minorIJ h' I (stepCols N j i) = c0 k * minorIJ h I (stepCols N j i) :=
    fun i k hk I => minors_prop M hbp hF hG hk q0 rfl bz0 hh hh' (e0 i) (e0' i) I
  have m1 : ∀ i k, M.blk (τ, i) = some k → ∀ I, minorIJ (h' * (1 + Matrix.single cb ca t')) I (stepCols N j i) =
      c1 k * minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j i) :=
    fun i k hk I => minors_prop M hbp hF hG hk q1 hb1 bz1 (hh.mul (hT t)) (hh'.mul (hT t')) (e1 i) (e1' i) I
  have hsome : ∀ i, IsProperStep N j i → ∃ k, M.blk (τ, i) = some k := fun i hi =>
    Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
  have tri : (h⁻¹ * h').BlockTriangular id := GlobalTheory.T.block_triangular_of_proportional_minors N j h h' hj hh hh' hd hd' fun i hi => by
    obtain ⟨k, hk⟩ := hsome i hi
    exact ⟨c0 k, m0 i k hk⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = h⁻¹ * h' := ⟨_, rfl⟩
  have hBt : B.BlockTriangular id := hBd ▸ tri
  have hBb : IsBlockDiag j B := hBd ▸ (hh.inv hd.isUnit).mul hh'
  have hhB : h' = h * B := by rw [hBd, Matrix.mul_nonsing_inv_cancel_left _ _ hd.isUnit]
  have hBdet : B.det ≠ 0 := fun e => hd' (by rw [hhB, Matrix.det_mul, e, mul_zero])
  have hdiag : ∀ c, B c c ≠ 0 := fun c => by
    rw [Matrix.det_of_upperTriangular hBt] at hBdet
    exact Finset.prod_ne_zero_iff.1 hBdet c (Finset.mem_univ c)
  have hΛ : ∀ S : Finset (Fin N), ∏ x ∈ S, B x x ≠ 0 := fun S => Finset.prod_ne_zero_iff.2 fun c _ => hdiag c
  have s0 : ∀ i k, M.blk (τ, i) = some k → c0 k = ∏ x ∈ stepCols N j i, B x x := fun i k hk =>
    scal_eq hj i hd hBb hBt fun I => by rw [← hhB]; exact m0 i k hk I
  have s1 : ∀ i k, M.blk (τ, i) = some k → i ≠ a → c1 k = ∏ x ∈ stepCols N j i, B x x := fun i k hk hi =>
    scal_eq hj i hd hBb hBt fun I => by
      have e := m1 i k hk I
      rw [GlobalTheory.T.elementary_twist_minor_other_steps N j a b ca cb hj hb hcase hca hcb h' t' i hi I,
        GlobalTheory.T.elementary_twist_minor_other_steps N j a b ca cb hj hb hcase hca hcb h t i hi I, hhB] at e
      exact e
  obtain ⟨-, p2⟩ := GlobalTheory.T.elementary_twist_minor_scalar N j a b ca cb hj hb hcase hca hcb h B t t' (c1 k₀) hd hBb hBt fun I => by
    rw [← hhB]; exact m1 a k₀ hk₀ I
  have hv : ∀ i, ¬ IsProperStep N j i → valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) ≠ 0 := fun i hi =>
    val_ups_ne M hbp hG ((M.blk_none _).2 hi)
  have hv' : ∀ i, ¬ IsProperStep N j i → valAt M.x (F.υ (τ, i)) (basePart M.blk z₀') ≠ 0 := by
    rw [bz0]; exact hv
  rw [normRhs_eq M τ a F z₀ z₁ h ht hv (fun i => fac_ne_zero hj i hh hd a),
    normRhs_eq M τ a F z₀' z₁' h' ht' hv' (fun i => fac_ne_zero hj i hh' hd' a), bz0]
  have f0 : ∀ i, Real.log ((fsHerm ι (M.dy (τ, i))).h z₀') = Real.log ((fsHerm ι (M.dy (τ, i))).h z₀) +
      ∑ k, (M.dy (τ, i) k : ℝ) * Real.log ‖c0 k‖ := fun i => by
    rw [q0]; exact log_fs_smul _ hc0 hn0
  have f1 : ∀ i, Real.log ((fsHerm ι (M.dy (τ, i))).h z₁') = Real.log ((fsHerm ι (M.dy (τ, i))).h z₁) +
      ∑ k, (M.dy (τ, i) k : ℝ) * Real.log ‖c1 k‖ := fun i => by
    rw [q1]; exact log_fs_smul _ hc1 hn1
  obtain ⟨D, hD⟩ : ∃ D : Fin N → ℝ, D = fun i => wt M τ a F (basePart M.blk z₀) h' i -
      wt M τ a F (basePart M.blk z₀) h i + (1 / 2) * (∑ k, (M.dy (τ, i) k : ℝ) * Real.log ‖c0 k‖ +
        ∑ k, (M.dy (τ, i) k : ℝ) * Real.log ‖c1 k‖) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = ∏ x ∈ (stepCols N j a).erase ca, B x x := ⟨_, rfl⟩
  have hβ0 : β ≠ 0 := hβ ▸ hΛ _
  have hproper : ∀ i, IsProperStep N j i → i ≠ a → D i = Real.log ‖∏ x ∈ stepCols N j i, B x x‖ := fun i hi hia => by
    obtain ⟨k, hk⟩ := hsome i hi
    rw [hD]
    simp only [wt, if_pos hi]
    rw [dy_sum_some M hk ob0, dy_sum_some M hk ob1, s0 i k hk, s1 i k hk hia]
    ring
  have hprev : ∀ a' : Fin N, (a' : ℕ) + 1 = a → D a' = Real.log ‖β‖ := fun a' ha' => by
    have hne : a' ≠ a := fun e => by rw [e] at ha'; omega
    by_cases hp : IsProperStep N j a'
    · rw [hproper a' hp hne, cols_prev hj hb hcase hca ha' hp, hβ]
    · obtain ⟨g1, g2⟩ := fac_prev (j := j) hb ha' hp h
      obtain ⟨g3, -⟩ := fac_prev (j := j) hb ha' hp h'
      have hbl := (M.blk_none (τ, a')).2 hp
      rw [hD]
      simp only [wt, if_neg hp]
      rw [dy_sum_none M hbl ob0, dy_sum_none M hbl ob1, g1, g3, hβ, cols_first hj hb hcase hca (Or.inr g2)]
      simp
  have hzero : (a : ℕ) = 0 → Real.log ‖β‖ = 0 := fun h0 => by
    rw [hβ, cols_first hj hb hcase hca (Or.inl h0)]
    simp
  obtain ⟨cn, hcbn, hcam⟩ := cols_next hj hb hcase hca hcb
  have hDb : D b = Real.log ‖∏ x ∈ stepCols N j b, B x x‖ := by
    have hne : b ≠ a := fun e => by rw [e] at hb; omega
    by_cases hp : IsProperStep N j b
    · exact hproper b hp hne
    · have hbl := (M.blk_none (τ, b)).2 hp
      have e : Fib.facOf N j a h' b = Fib.facOf N j a h b * ∏ x ∈ stepCols N j b, B x x := by
        rw [fac_next hj hb hcase hp, fac_next hj hb hcase hp, hhB]
        exact (GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j b hj).2.2.1 h B _ hBb hBt
      rw [hD]
      simp only [wt, if_neg hp]
      rw [dy_sum_none M hbl ob0, dy_sum_none M hbl ob1, e, ← mul_assoc, norm_mul _ (∏ x ∈ stepCols N j b, B x x),
        Real.log_mul (norm_ne_zero_iff.2 (mul_ne_zero (hv b hp) (fac_ne_zero hj b hh hd a)))
          (norm_ne_zero_iff.2 (hΛ _))]
      ring
  have hap : IsProperStep N j a := by
    by_contra hp
    have := (M.blk_none (τ, a)).2 hp
    rw [hk₀] at this
    exact absurd this (by simp)
  have hDa : 2 * D a = Real.log ‖∏ x ∈ stepCols N j a, B x x‖ + Real.log ‖c1 k₀‖ := by
    rw [hD]
    simp only [wt, if_pos hap]
    rw [dy_sum_some M hk₀ ob0, dy_sum_some M hk₀ ob1, s0 a k₀ hk₀]
    ring
  have key := xi_sum τ hb D (Real.log ‖β‖) hprev hzero
  have hlogs : Real.log ‖c1 k₀‖ + Real.log ‖t‖ = Real.log ‖β‖ + (Real.log ‖t'‖ + Real.log ‖B cb cb‖) := by
    rw [← Real.log_mul (norm_ne_zero_iff.2 (hc1 k₀)) (norm_ne_zero_iff.2 ht),
      ← Real.log_mul (norm_ne_zero_iff.2 ht') (norm_ne_zero_iff.2 (hdiag cb)),
      ← Real.log_mul (norm_ne_zero_iff.2 hβ0) (mul_ne_zero (norm_ne_zero_iff.2 ht') (norm_ne_zero_iff.2 (hdiag cb))),
      ← norm_mul, ← norm_mul, ← norm_mul, p2, hβ]
  have hDb' : D b = Real.log ‖∏ x ∈ stepCols N j a, B x x‖ + Real.log ‖B cb cb‖ := by
    rw [hDb, cn, Finset.prod_insert hcbn, norm_mul, mul_comm,
      Real.log_mul (norm_ne_zero_iff.2 (hΛ _)) (norm_ne_zero_iff.2 (hdiag cb))]
  have hsum : ∑ i, (xiCoef τ a (τ, i) : ℝ) * D i = Real.log ‖t‖ - Real.log ‖t'‖ := by
    rw [key, hDb', hDa]
    linarith
  have hsplit : ∑ i, (xiCoef τ a (τ, i) : ℝ) * (wt M τ a F (basePart M.blk z₀) h' i +
      (1 / 2) * (Real.log ((fsHerm ι (M.dy (τ, i))).h z₀') + Real.log ((fsHerm ι (M.dy (τ, i))).h z₁'))) =
      ∑ i, (xiCoef τ a (τ, i) : ℝ) * (wt M τ a F (basePart M.blk z₀) h i +
        (1 / 2) * (Real.log ((fsHerm ι (M.dy (τ, i))).h z₀) + Real.log ((fsHerm ι (M.dy (τ, i))).h z₁))) +
      ∑ i, (xiCoef τ a (τ, i) : ℝ) * D i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [f0 i, f1 i, hD]
    ring
  rw [hsplit, hsum]
  ring

end Thm

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Same
