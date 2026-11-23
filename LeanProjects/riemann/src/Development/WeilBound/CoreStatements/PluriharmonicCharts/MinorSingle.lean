import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeScalarFactor
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesAtPoint
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeUnderFieldMap
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace PositivityTheory.Xgp.c_cov_self

open GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

section Mat

variable {N : ℕ}

theorem minor_single {R : Type} [CommRing R] (A : Matrix (Fin N) (Fin N) R) (a b : Fin N) :
    minorIJ A {a} {b} = A a b := by
  rw [MinorCalc.minorIJ_eq_det A {a} {b} 1 (Finset.card_singleton a) (Finset.card_singleton b), Matrix.det_unique,
    Matrix.submatrix_apply]
  congr 1
  · exact Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ _ _)
  · exact Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ _ _)

theorem minor_mem {L : Type} [Field L] (P : Subring L) {A : Matrix (Fin N) (Fin N) L} {I J : Finset (Fin N)}
    (hA : ∀ a ∈ I, ∀ b ∈ J, A a b ∈ P) : minorIJ A I J ∈ P := by
  unfold minorIJ
  split_ifs with e
  · rw [Matrix.det_apply]
    refine P.sum_mem fun σ _ => ?_
    rw [Units.smul_def]
    exact P.zsmul_mem (P.prod_mem fun i _ =>
      hA _ (Finset.orderEmbOfFin_mem _ _ _) _ (Finset.orderEmbOfFin_mem _ _ _)) _
  · exact P.zero_mem

end Mat

section Val

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem regAt_of_val {s : Ω} {v : ℂ} (h : IsValueAt x s z v) : RegAt x (mCoordIdeal z) s := by
  obtain ⟨d, g, h0, hg, hh, -, heq, hz0, -⟩ := h
  exact ⟨d, g, h0, hg, hh, An.notMem_of_eval_ne_zero hz0, heq⟩

theorem val_one : IsValueAt x (1 : Ω) z 1 := by simpa using isValueAt_intCast x z 1

theorem val_zpow {s : Ω} {v : ℂ} (h : IsValueAt x s z v) (hs : s ≠ 0) (hv : v ≠ 0) (n : ℤ) :
    IsValueAt x (s ^ n) z (v ^ n) := by
  cases n with
  | ofNat n => simpa using isValueAt_pow h n
  | negSucc n =>
    rw [zpow_negSucc, zpow_negSucc]
    exact isValueAt_inv (isValueAt_pow h _) (pow_ne_zero _ hs) (pow_ne_zero _ hv)

theorem val_prod {α : Type} (t : Finset α) (f : α → Ω) (v : α → ℂ) (h : ∀ a, IsValueAt x (f a) z (v a)) :
    IsValueAt x (∏ a ∈ t, f a) z (∏ a ∈ t, v a) := by
  induction t using Finset.induction_on with
  | empty => simpa using val_one
  | insert a t ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha]; exact isValueAt_mul (h a) ih

theorem reg_detFac (hz : z ∈ mcPts (mCoordIdeal x)) {N : ℕ} (j : ℕ) (i : Fin N) {A : Matrix (Fin N) (Fin N) Ω}
    (hA : ∀ a b, RegAt x (mCoordIdeal z) (A a b)) :
    RegAt x (mCoordIdeal z) (detFac j i A) ∧ valAt x (detFac j i A) z = detFac j i (valMat x z A) := by
  have h1 := reg_minor hz hA (wIdx N j) (wIdx N j)
  have h2 := reg_minor hz hA (omIdx N j) (omIdx N j)
  have h0 := FV.valAt_one' hz
  have r0 := ValRing.regAt_one x z
  unfold detFac
  split_ifs
  · exact ⟨(reg_mul hz h1.1 h2.1).1, by rw [(reg_mul hz h1.1 h2.1).2, h1.2, h2.2]⟩
  · simp only [mul_one]; exact h1
  · simp only [one_mul]; exact h2
  · simp only [mul_one]; exact ⟨r0, h0⟩

end Val

section Frames

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j)

def rho (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk) (p : Ψ × Fin N) : M.Ω :=
  ∏ k', (M.x ⟨k', F₂.c k'⟩ / M.x ⟨k', F₁.c k'⟩) ^ M.b p k'

def rhoC (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk) (p : Ψ × Fin N) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) : ℂ :=
  ∏ k', (zb ⟨k', F₂.c k'⟩ / zb ⟨k', F₁.c k'⟩) ^ M.b p k'

variable {M} {F₁ F₂ : FrameData ι Ψ N M.Ω M.blk}

theorem rho_mul (c₁ : ∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) (p : Ψ × Fin N) :
    rho M F₁ F₂ p * ∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k' = ∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k' := by
  rw [rho, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← mul_zpow, div_mul_cancel₀ _ (c₁ k)]

theorem detFac_chg (h₁ : M.IsFrame F₁) (h₂ : M.IsFrame F₂) (τ : Ψ) (i : Fin N) :
    detFac j i (F₂.T τ) = detFac j i (F₁.T τ) * detFac j i ((F₁.T τ)⁻¹ * F₂.T τ) := by
  have hu₁ : IsUnit (F₁.T τ).det := (h₁.1 τ).2.isUnit
  rw [← MinorCalc.detFac_mul i (((h₁.1 τ).1.inv hu₁).mul (h₂.1 τ).1), Matrix.mul_nonsing_inv_cancel_left _ _ hu₁]

theorem rel (h₁ : M.IsFrame F₁) (h₂ : M.IsFrame F₂) (c₁ : ∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) (m : ι k) (I' : Finset (Fin N)) (hI' : IsStepRows N j p.2 I') :
    ∑ I, detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) * F₁.u ⟨k, m⟩ I * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' =
      rho M F₁ F₂ p * F₂.u ⟨k, m⟩ I' := by
  have hT₁ := h₁.1 p.1
  have hT₂ := h₂.1 p.1
  have hu₁ : IsUnit (F₁.T p.1).det := hT₁.2.isUnit
  have hA₁ : (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (c₁ k')
  have hS : IsBlockDiag j ((F₁.T p.1)⁻¹ * F₂.T p.1) := (hT₁.1.inv hu₁).mul hT₂.1
  have hE : IsBlockDiag j (FrameChange.unitCols I' (stepCols N j p.2) hI'.1 : Matrix (Fin N) (Fin N) M.Ω) :=
    FrameChange.unitCols_blockDiag _ _ _ (FrameChange.stepRows_same_side hI')
  have e1 := h₁.2.1 p k hp m _ (hS.mul hE)
  have e2 := h₂.2.1 p k hp m _ hE
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu₁] at e1
  have hm : ∀ I, minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1 * FrameChange.unitCols I' (stepCols N j p.2) hI'.1) I
      (stepCols N j p.2) = minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' := fun I => by
    rw [MinorCalc.minorIJ_mul]
    simp only [FrameChange.minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hr : ∑ I, F₂.u ⟨k, m⟩ I * minorIJ (FrameChange.unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2) =
      F₂.u ⟨k, m⟩ I' := by
    simp only [FrameChange.minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [hm] at e1
  rw [hr, detFac_chg h₁ h₂, ← rho_mul (F₂ := F₂) c₁] at e2
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  apply mul_left_cancel₀ hA₁
  linear_combination (-detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1)) * e1 + e2

theorem rel0 (h₁ : M.IsFrame F₁) (h₂ : M.IsFrame F₂) (c₁ : ∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) {p : Ψ × Fin N}
    (hp : M.blk p = none) : detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) * F₁.υ p = rho M F₁ F₂ p * F₂.υ p := by
  have hA₁ : (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (c₁ k')
  have e1 := h₁.2.2.2 p hp
  have e2 := h₂.2.2.2 p hp
  rw [detFac_chg h₁ h₂, ← rho_mul (F₂ := F₂) c₁] at e2
  apply mul_left_cancel₀ hA₁
  linear_combination (-detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1)) * e1 + e2

variable {zb : (Σ k, baseIdx ι M.blk k) → ℂ}

theorem x_chart_ne_zero_of_goodAt (hz : zb ∈ mcPts (mCoordIdeal M.x)) (g₁ : M.GoodAt F₁ (mCoordIdeal zb)) (k) :
    M.x ⟨k, F₁.c k⟩ ≠ 0 := CPts.coord_ne hz (An.coord_ne_zero_of_notMem (g₁.1 k))

theorem rho_val (hz : zb ∈ mcPts (mCoordIdeal M.x)) (g₁ : M.GoodAt F₁ (mCoordIdeal zb))
    (g₂ : M.GoodAt F₂ (mCoordIdeal zb)) (p : Ψ × Fin N) : IsValueAt M.x (rho M F₁ F₂ p) zb (rhoC M F₁ F₂ p zb) :=
  val_prod _ _ _ fun k => val_zpow
    (CPts.isValueAt_ratio (x_chart_ne_zero_of_goodAt hz g₁ k) (An.coord_ne_zero_of_notMem (g₁.1 k)))
    (div_ne_zero (x_chart_ne_zero_of_goodAt hz g₂ k) (x_chart_ne_zero_of_goodAt hz g₁ k))
    (div_ne_zero (An.coord_ne_zero_of_notMem (g₂.1 k)) (An.coord_ne_zero_of_notMem (g₁.1 k))) _

theorem step_mem (hz : zb ∈ mcPts (mCoordIdeal M.x)) (h₁ : M.IsFrame F₁) (h₂ : M.IsFrame F₂)
    (g₁ : M.GoodAt F₁ (mCoordIdeal zb)) (g₂ : M.GoodAt F₂ (mCoordIdeal zb)) (τ : Ψ) (i : Fin N)
    (hi : IsProperStep N j i) {I₀ I' : Finset (Fin N)} (h₀ : IsStepRows N j i I₀) (h' : IsStepRows N j i I') :
    detFac j i ((F₁.T τ)⁻¹ * F₂.T τ) * minorIJ ((F₁.T τ)⁻¹ * F₂.T τ) I₀ I' ∈ regRing M.x zb := by
  obtain ⟨k, hk⟩ : ∃ k, M.blk (τ, i) = some k :=
    Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
  have hu₁ : IsUnit (F₁.T τ).det := (h₁.1 τ).2.isUnit
  have hS : IsBlockDiag j ((F₁.T τ)⁻¹ * F₂.T τ) := ((h₁.1 τ).1.inv hu₁).mul (h₂.1 τ).1
  set S := (F₁.T τ)⁻¹ * F₂.T τ with hSdef
  have hoff : ∀ I, ¬ IsStepRows N j i I → minorIJ S I I' = 0 := by
    intro I hI
    have hE : IsBlockDiag j (FrameChange.unitCols I' (stepCols N j i) h'.1 : Matrix (Fin N) (Fin N) M.Ω) :=
      FrameChange.unitCols_blockDiag _ _ _ (FrameChange.stepRows_same_side h')
    have := ((GlobalTheory.T.block_diagonal_minor_vanishing M.Ω N j i M.j_le).2.1 _ I (hS.mul hE) hI).resolve_right (FV.stepCols_ne_empty i)
    rw [MinorCalc.minorIJ_mul] at this
    simpa only [FrameChange.minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] using this
  have e : detFac j i S * minorIJ S I₀ I' = ∑ m : ι k, F₁.u' I₀ ⟨k, m⟩ * (rho M F₁ F₂ (τ, i) * F₂.u ⟨k, m⟩ I') := by
    have r := fun m => rel h₁ h₂ (x_chart_ne_zero_of_goodAt hz g₁) hk m I' h'
    simp only [← r, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc detFac j i S * minorIJ S I₀ I'
        = ∑ I, (if I₀ = I then 1 else 0) * (detFac j i S * minorIJ S I I') := by simp
      _ = _ := Finset.sum_congr rfl fun I _ => by
          by_cases hI : IsStepRows N j i I
          · rw [← h₁.2.2.1 (τ, i) k hk I₀ I h₀ hI, Finset.sum_mul]
            exact Finset.sum_congr rfl fun m _ => by ring
          · simp only [← hSdef, hoff I hI, mul_zero, Finset.sum_const_zero]
  rw [e]
  exact Subring.sum_mem _ fun m _ => Subring.mul_mem _ (g₁.2.1 _ _).2
    (Subring.mul_mem _ (regAt_of_val (rho_val hz g₁ g₂ _)) (g₂.2.1 _ _).1)

theorem nonstep_mem (hz : zb ∈ mcPts (mCoordIdeal M.x)) (h₁ : M.IsFrame F₁) (h₂ : M.IsFrame F₂)
    (g₁ : M.GoodAt F₁ (mCoordIdeal zb)) (g₂ : M.GoodAt F₂ (mCoordIdeal zb)) (τ : Ψ) (i : Fin N)
    (hi : ¬ IsProperStep N j i) : detFac j i ((F₁.T τ)⁻¹ * F₂.T τ) ∈ regRing M.x zb := by
  have hp : M.blk (τ, i) = none := (M.blk_none _).2 hi
  have r := rel0 h₁ h₂ (x_chart_ne_zero_of_goodAt hz g₁) hp
  have e : detFac j i ((F₁.T τ)⁻¹ * F₂.T τ) = rho M F₁ F₂ (τ, i) * F₂.υ (τ, i) * (F₁.υ (τ, i))⁻¹ := by
    rw [← r, mul_inv_cancel_right₀ (g₁.2.2 _ hp).1]
  rw [e]
  exact Subring.mul_mem _ (Subring.mul_mem _ (regAt_of_val (rho_val hz g₁ g₂ _)) (g₂.2.2 _ hp).2.1)
    (g₁.2.2 _ hp).2.2

theorem w_mem (hz : zb ∈ mcPts (mCoordIdeal M.x)) (h₁ : M.IsFrame F₁) (h₂ : M.IsFrame F₂)
    (g₁ : M.GoodAt F₁ (mCoordIdeal zb)) (g₂ : M.GoodAt F₂ (mCoordIdeal zb)) (τ : Ψ) :
    ∀ a ∈ wIdx N j, ∀ b ∈ wIdx N j, ((F₁.T τ)⁻¹ * F₂.T τ) a b ∈ regRing M.x zb := by
  intro a ha b hb
  have hj := M.j_le
  have ha' : N - j ≤ (a : ℕ) := (Finset.mem_filter.1 ha).2
  have hb' : N - j ≤ (b : ℕ) := (Finset.mem_filter.1 hb).2
  have ha2 := a.2
  have hb2 := b.2
  let i : Fin N := ⟨0, a.pos⟩
  by_cases h1 : j = 1
  · have hab : b = a := Fin.ext (by omega)
    subst hab
    have hW : wIdx N j = {b} := by
      ext c
      simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
      have := c.2
      omega
    have := nonstep_mem hz h₁ h₂ g₁ g₂ τ i fun h => h.1 (by simp [i, h1])
    unfold detFac at this
    rw [if_pos (by simp [i, h1]), hW, minor_single] at this
    split_ifs at this with h2
    · have hO : omIdx N j = ∅ := by
        ext c
        simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        simp only [i] at h2
        omega
      rw [hO, MinorCalc.minorIJ_eq_det _ _ _ 0 rfl rfl, Matrix.det_isEmpty, mul_one] at this
      exact this
    · rwa [mul_one] at this
  · have hrow : ∀ c ∈ wIdx N j, IsStepRows N j i {c} := by
      intro c hc
      have hs : stepCols N j i = {⟨N - j, by omega⟩} := by
        ext c
        simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff, i]
        rw [if_pos (by omega)]
        omega
      refine ⟨by rw [hs]; rfl, ?_⟩
      rw [if_pos (by simp only [i]; omega)]
      exact Finset.singleton_subset_iff.2 hc
    have := step_mem hz h₁ h₂ g₁ g₂ τ i ⟨by simp only [i]; omega, by simp only [i]; omega⟩ (hrow a ha) (hrow b hb)
    unfold detFac at this
    rwa [if_neg (by simp only [i]; omega), if_neg (by simp only [i]; omega), one_mul, one_mul, minor_single] at this

theorem all_mem (hz : zb ∈ mcPts (mCoordIdeal M.x)) (h₁ : M.IsFrame F₁) (h₂ : M.IsFrame F₂)
    (g₁ : M.GoodAt F₁ (mCoordIdeal zb)) (g₂ : M.GoodAt F₂ (mCoordIdeal zb)) (τ : Ψ) (a b : Fin N) :
    RegAt M.x (mCoordIdeal zb) (((F₁.T τ)⁻¹ * F₂.T τ) a b) := by
  have hj := M.j_le
  have hu₁ : IsUnit (F₁.T τ).det := (h₁.1 τ).2.isUnit
  have hu₂ : IsUnit (F₂.T τ).det := (h₂.1 τ).2.isUnit
  have hS : IsBlockDiag j ((F₁.T τ)⁻¹ * F₂.T τ) := ((h₁.1 τ).1.inv hu₁).mul (h₂.1 τ).1
  show _ ∈ regRing M.x zb
  by_cases hab : ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
  swap
  · rw [hS a b hab]; exact Subring.zero_mem _
  by_cases ha : (a : ℕ) < N - j
  swap
  · exact w_mem hz h₁ h₂ g₁ g₂ τ a (by simp [wIdx]; omega) b (by simp [wIdx]; omega)
  have hb := hab.1 ha
  have hd : minorIJ ((F₂.T τ)⁻¹ * F₁.T τ) (wIdx N j) (wIdx N j) ∈ regRing M.x zb :=
    minor_mem _ (w_mem hz h₂ h₁ g₂ g₁ τ)
  have hone : minorIJ ((F₂.T τ)⁻¹ * F₁.T τ) (wIdx N j) (wIdx N j) *
      minorIJ ((F₁.T τ)⁻¹ * F₂.T τ) (wIdx N j) (wIdx N j) = 1 := by
    rw [← MinorCalc.minorIJ_mul_of_support _ _ _ _ (MinorCalc.support_wIdx hS), Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hu₁, Matrix.nonsing_inv_mul _ hu₂, CPts.minorIJ_one]
  suffices h : minorIJ ((F₁.T τ)⁻¹ * F₂.T τ) (wIdx N j) (wIdx N j) * ((F₁.T τ)⁻¹ * F₂.T τ) a b ∈ regRing M.x zb by
    have := Subring.mul_mem _ hd h
    rwa [← mul_assoc, hone, one_mul] at this
  let i : Fin N := ⟨j, by omega⟩
  by_cases h1 : j + 1 = N
  · have hab : b = a := Fin.ext (by omega)
    subst hab
    have hO : omIdx N j = {b} := by
      ext c
      simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
      omega
    have := nonstep_mem hz h₁ h₂ g₁ g₂ τ i fun h => h.2 h1
    unfold detFac at this
    rwa [if_pos (by simp only [i]; omega), if_pos h1, hO, minor_single] at this
  · have hrow : ∀ c : Fin N, (c : ℕ) < N - j → IsStepRows N j i {c} := by
      intro c hc
      have hs : stepCols N j i = {⟨0, by omega⟩} := by
        ext c
        simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff, i]
        rw [if_neg (by omega)]
        omega
      refine ⟨by rw [hs]; rfl, ?_⟩
      rw [if_neg (by simp only [i]; omega)]
      exact Finset.singleton_subset_iff.2 (by simpa [omIdx] using hc)
    have := step_mem hz h₁ h₂ g₁ g₂ τ i ⟨by simp only [i]; omega, h1⟩ (hrow a ha) (hrow b hb)
    unfold detFac at this
    rwa [if_pos (by simp only [i]; omega), if_neg h1, mul_one, minor_single] at this

theorem relC (hz : zb ∈ mcPts (mCoordIdeal M.x)) (h₁ : M.IsFrame F₁) (h₂ : M.IsFrame F₂)
    (g₁ : M.GoodAt F₁ (mCoordIdeal zb)) (g₂ : M.GoodAt F₂ (mCoordIdeal zb)) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) (h : Matrix (Fin N) (Fin N) ℂ) (hh : IsBlockDiag j h) (m : ι k) :
    detFac j p.2 (valMat M.x zb ((F₁.T p.1)⁻¹ * F₂.T p.1)) * ∑ I, valAt M.x (F₁.u ⟨k, m⟩ I) zb *
        minorIJ (valMat M.x zb ((F₁.T p.1)⁻¹ * F₂.T p.1) * h) I (stepCols N j p.2) =
      rhoC M F₁ F₂ p zb * ∑ I, valAt M.x (F₂.u ⟨k, m⟩ I) zb * minorIJ h I (stepCols N j p.2) := by
  have hA := all_mem hz h₁ h₂ g₁ g₂ p.1
  have hd := reg_detFac hz j p.2 hA
  have hstep : IsStepRows N j p.2 (stepCols N j p.2) := FV.isStepRows_stepCols p.2
  have hinv := h₂.2.2.1 p k hp _ _ hstep hstep
  rw [if_pos rfl] at hinv
  obtain ⟨-, hval⟩ := FV.reg_values hz p.2
    (fun (m : ι k) I => detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) * F₁.u ⟨k, m⟩ I)
    (fun (m : ι k) I => F₂.u ⟨k, m⟩ I) (fun m : ι k => F₂.u' (stepCols N j p.2) ⟨k, m⟩) _ (rho M F₁ F₂ p) _ hstep
    (fun m I => ValRing.regAt_mul hd.1 (g₁.2.1 _ _).1) (fun m I => (g₂.2.1 _ _).1) (fun m => (g₂.2.1 _ _).2) hA
    (rel h₁ h₂ (x_chart_ne_zero_of_goodAt hz g₁) hp) hinv
  have := FV.sum_minor_mul M.j_le p.2 _ _ _ _ hval h hh m
  rw [valAt_eq hz (rho_val hz g₁ g₂ p)] at this
  rw [← this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [(reg_mul hz hd.1 (g₁.2.1 _ _).1).2, hd.2, mul_assoc]

theorem rel0C (hz : zb ∈ mcPts (mCoordIdeal M.x)) (h₁ : M.IsFrame F₁) (h₂ : M.IsFrame F₂)
    (g₁ : M.GoodAt F₁ (mCoordIdeal zb)) (g₂ : M.GoodAt F₂ (mCoordIdeal zb)) {p : Ψ × Fin N}
    (hp : M.blk p = none) :
    detFac j p.2 (valMat M.x zb ((F₁.T p.1)⁻¹ * F₂.T p.1)) * valAt M.x (F₁.υ p) zb =
      rhoC M F₁ F₂ p zb * valAt M.x (F₂.υ p) zb := by
  have hd := reg_detFac hz j p.2 (all_mem hz h₁ h₂ g₁ g₂ p.1)
  rw [← hd.2, ← (reg_mul hz hd.1 (g₁.2.2 p hp).2.1).2, rel0 h₁ h₂ (x_chart_ne_zero_of_goodAt hz g₁) hp,
    (reg_mul hz (regAt_of_val (rho_val hz g₁ g₂ p)) (g₂.2.2 p hp).2.1).2, valAt_eq hz (rho_val hz g₁ g₂ p)]

theorem ups_ne (hz : zb ∈ mcPts (mCoordIdeal M.x)) (g₁ : M.GoodAt F₁ (mCoordIdeal zb)) {p : Ψ × Fin N}
    (hp : M.blk p = none) : valAt M.x (F₁.υ p) zb ≠ 0 := by
  have h := (reg_mul hz (g₁.2.2 p hp).2.1 (g₁.2.2 p hp).2.2).2
  rw [mul_inv_cancel₀ (g₁.2.2 p hp).1, FV.valAt_one' hz] at h
  exact left_ne_zero_of_mul_eq_one h.symm

theorem rhoC_ne (g₁ : M.GoodAt F₁ (mCoordIdeal zb)) (g₂ : M.GoodAt F₂ (mCoordIdeal zb)) (p : Ψ × Fin N) :
    rhoC M F₁ F₂ p zb ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _
    (div_ne_zero (An.coord_ne_zero_of_notMem (g₂.1 k)) (An.coord_ne_zero_of_notMem (g₁.1 k)))

end Frames

end PositivityTheory.Xgp.c_cov_self
