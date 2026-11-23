import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeScalarFactor
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.FrameReg

open GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FrameChange

theorem stepCols_ne_empty {N j : ℕ} (i : Fin N) : stepCols N j i ≠ ∅ := by
  intro e
  have hi := i.2
  by_cases h : (i : ℕ) + 1 ≤ j
  · have : (⟨N - j, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h]
      omega
    simp [e] at this
  · have : (⟨0, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h]
      omega
    simp [e] at this

theorem minor_singleton {R : Type} [CommRing R] {N : ℕ} (h : Matrix (Fin N) (Fin N) R) (a b : Fin N) :
    minorIJ h {a} {b} = h a b := by
  unfold minorIJ
  rw [dif_pos (by simp)]
  haveI : Unique (Fin ({b} : Finset (Fin N)).card) := inferInstanceAs (Unique (Fin 1))
  rw [det_unique]
  show h _ _ = _
  congr 1
  · exact Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ _ _)
  · exact Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ _ _)

theorem minor_empty {R : Type} [CommRing R] {N : ℕ} (h : Matrix (Fin N) (Fin N) R) :
    minorIJ h ∅ ∅ = 1 := by
  unfold minorIJ
  rw [dif_pos rfl]
  haveI : IsEmpty (Fin (∅ : Finset (Fin N)).card) := inferInstanceAs (IsEmpty (Fin 0))
  exact det_isEmpty

theorem stepCols_eq_singleton_of_zero {N j : ℕ} (i : Fin N) (hi : (i : ℕ) = 0) (hj : 1 ≤ j) (hN : j ≤ N) :
    stepCols N j i = {⟨N - j, by omega⟩} := by
  ext a
  have := a.2
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
  rw [if_pos (by omega)]
  omega

theorem stepCols_om {N j : ℕ} (i : Fin N) (hi : (i : ℕ) = j) :
    stepCols N j i = {⟨0, by have := i.2; omega⟩} := by
  ext a
  have := a.2
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
  rw [if_neg (by omega)]
  omega

theorem isStepRows_singleton_low {N j : ℕ} (i : Fin N) (hi : (i : ℕ) = 0) (hj : 2 ≤ j) (hN : j ≤ N) (r : Fin N)
    (hr : N - j ≤ (r : ℕ)) : IsStepRows N j i {r} := by
  refine ⟨by rw [stepCols_eq_singleton_of_zero i hi (by omega) hN]; simp, ?_⟩
  rw [if_pos (by omega), Finset.singleton_subset_iff]
  simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hr

theorem isStepRows_om {N j : ℕ} (i : Fin N) (hi : (i : ℕ) = j) (r : Fin N)
    (hr : (r : ℕ) < N - j) : IsStepRows N j i {r} := by
  refine ⟨by rw [stepCols_om i hi]; simp, ?_⟩
  rw [if_neg (by omega), Finset.singleton_subset_iff]
  simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hr

section Reg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem regAt_zpow {s : Ω} (h : RegAt x (mCoordIdeal z) s) (h' : RegAt x (mCoordIdeal z) s⁻¹) (n : ℤ) :
    RegAt x (mCoordIdeal z) (s ^ n) := by
  have a : s ∈ regRing x z := h
  have b : s⁻¹ ∈ regRing x z := h'
  show s ^ n ∈ regRing x z
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast]; exact Subring.pow_mem _ a n
  · rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]; exact Subring.pow_mem _ b n

theorem coord_ne (hz : z ∈ mcPts (mCoordIdeal x)) {q : Σ k, ι k} (hq : (X q : MRing ι) ∉ mCoordIdeal z) :
    x q ≠ 0 := by
  have := ValRing.aeval_ne_zero_of_notMem hz (isMultiHomog_X_single q) hq
  simpa using this

theorem regAt_ratio (hz : z ∈ mcPts (mCoordIdeal x)) {k : K} (a b : ι k)
    (hb : (X ⟨k, b⟩ : MRing ι) ∉ mCoordIdeal z) : RegAt x (mCoordIdeal z) (x ⟨k, a⟩ / x ⟨k, b⟩) := by
  have hx := coord_ne hz hb
  refine ⟨_, X ⟨k, a⟩, X ⟨k, b⟩, isMultiHomog_X_single _, isMultiHomog_X_single _, hb, ?_⟩
  simp [div_mul_cancel₀ _ hx]

end Reg

section Model

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j)
  {zb : (Σ k, baseIdx ι M.blk k) → ℂ} {F₁ F₂ : FrameData ι Ψ N M.Ω M.blk}

include M in

theorem twist_ratio (hz : zb ∈ mcPts (mCoordIdeal M.x)) (hG₁ : M.GoodAt F₁ (mCoordIdeal zb))
    (hG₂ : M.GoodAt F₂ (mCoordIdeal zb)) (p : Ψ × Fin N) :
    RegAt M.x (mCoordIdeal zb)
      ((∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') / ∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') := by
  rw [← Finset.prod_div_distrib]
  refine Subring.prod_mem (regRing M.x zb) fun k _ => ?_
  rw [← div_zpow]
  refine regAt_zpow (regAt_ratio hz _ _ (hG₁.1 k)) ?_ _
  rw [inv_div]
  exact regAt_ratio hz _ _ (hG₂.1 k)

theorem detFac_improper (hz : zb ∈ mcPts (mCoordIdeal M.x)) (hF₁ : M.IsFrame F₁) (hF₂ : M.IsFrame F₂)
    (hG₁ : M.GoodAt F₁ (mCoordIdeal zb)) (hG₂ : M.GoodAt F₂ (mCoordIdeal zb)) (p : Ψ × Fin N)
    (hp : M.blk p = none) :
    RegAt M.x (mCoordIdeal zb) (detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1)) ∧
      RegAt M.x (mCoordIdeal zb) (detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1))⁻¹ := by
  have hT₁ := hF₁.1 p.1
  have hT₂ := hF₂.1 p.1
  have hu₁ : IsUnit (F₁.T p.1).det := hT₁.2.isUnit
  have hC : IsBlockDiag j ((F₁.T p.1)⁻¹ * F₂.T p.1) := (hT₁.1.inv hu₁).mul hT₂.1
  have hm := ((GlobalTheory.T.block_diagonal_minor_vanishing M.Ω N j p.2 M.j_le).2.2.2 _ _ hT₁.1 hC).2
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu₁] at hm
  have e₁ := hF₁.2.2.2 p hp
  have e₂ := hF₂.2.2.2 p hp
  have hr := twist_ratio M hz hG₁ hG₂ p
  have hr' := twist_ratio M hz hG₂ hG₁ p
  have hl := M.lam_ne_zero p hp
  have hd₁ := detFac_ne_zero M.j_le p.2 hT₁.1 hT₁.2
  have hA₁ : (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (coord_ne hz (hG₁.1 k'))
  have hA₂ : (∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (coord_ne hz (hG₂.1 k'))
  obtain ⟨v₁, rv₁, ri₁⟩ := hG₁.2.2 p hp
  obtain ⟨v₂, rv₂, ri₂⟩ := hG₂.2.2 p hp
  generalize detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) = D at *
  generalize detFac j p.2 (F₂.T p.1) = d₂ at *
  generalize detFac j p.2 (F₁.T p.1) = d₁ at *
  generalize (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') = A₁ at *
  generalize (∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') = A₂ at *
  have key : A₁ * F₁.υ p * D = A₂ * F₂.υ p := by rw [← e₁, ← e₂, hm]; ring
  have hD : D = A₂ / A₁ * (F₂.υ p * (F₁.υ p)⁻¹) := by
    field_simp
    linear_combination key
  have hD' : D⁻¹ = A₁ / A₂ * (F₁.υ p * (F₂.υ p)⁻¹) := by
    rw [hD]
    field_simp
  rw [hD', hD]
  exact ⟨ValRing.regAt_mul hr (ValRing.regAt_mul rv₂ ri₁), ValRing.regAt_mul hr' (ValRing.regAt_mul rv₁ ri₂)⟩

end Model

section Model2

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j)
  {zb : (Σ k, baseIdx ι M.blk k) → ℂ} {F₁ F₂ : FrameData ι Ψ N M.Ω M.blk}

theorem minor_change (hz : zb ∈ mcPts (mCoordIdeal M.x)) (hF₁ : M.IsFrame F₁) (hF₂ : M.IsFrame F₂)
    (hG₁ : M.GoodAt F₁ (mCoordIdeal zb)) (hG₂ : M.GoodAt F₂ (mCoordIdeal zb)) (p : Ψ × Fin N) (k : K)
    (hp : M.blk p = some k) {I₀ I' : Finset (Fin N)} (hI₀ : IsStepRows N j p.2 I₀)
    (hI' : IsStepRows N j p.2 I') :
    minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I₀ I' =
      (detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1))⁻¹ *
        ((∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') / ∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') *
        ∑ m : ι k, F₁.u' I₀ ⟨k, m⟩ * F₂.u ⟨k, m⟩ I' := by
  have hj := M.j_le
  have hT₁ := hF₁.1 p.1
  have hT₂ := hF₂.1 p.1
  have hu₁ : IsUnit (F₁.T p.1).det := hT₁.2.isUnit
  have hi := GlobalTheory.T.block_diagonal_minor_vanishing M.Ω N j p.2 hj
  have hC : IsBlockDiag j ((F₁.T p.1)⁻¹ * F₂.T p.1) := (hT₁.1.inv hu₁).mul hT₂.1
  have hdet : ((F₁.T p.1)⁻¹ * F₂.T p.1).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv]
    exact mul_ne_zero (by simpa using hT₁.2) hT₂.2
  have hD := detFac_ne_zero hj p.2 hC hdet
  have hd₁ := detFac_ne_zero hj p.2 hT₁.1 hT₁.2
  have hm := (hi.2.2.2 _ _ hT₁.1 hC).2
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu₁] at hm
  have hA₁ : (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (coord_ne hz (hG₁.1 k'))
  have hE : IsBlockDiag j (unitCols I' (stepCols N j p.2) hI'.1 : Matrix (Fin N) (Fin N) M.Ω) :=
    unitCols_blockDiag _ _ _ (stepRows_same_side hI')
  have hmin : ∀ I, minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1 * unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2) =
      minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' := fun I => by
    rw [hi.1]
    simp only [minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hr : ∀ m : ι k, ∑ I, F₂.u ⟨k, m⟩ I * minorIJ (unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2) =
      F₂.u ⟨k, m⟩ I' := fun m => by
    simp only [minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

  have rel : ∀ m : ι k, detFac j p.2 (F₂.T p.1) * (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') *
      ∑ I, F₁.u ⟨k, m⟩ I * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' =
      detFac j p.2 (F₁.T p.1) * (∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') * F₂.u ⟨k, m⟩ I' := fun m => by
    have e1 := hF₁.2.1 p k hp m _ (hC.mul hE)
    have e2 := hF₂.2.1 p k hp m _ hE
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu₁] at e1
    simp only [hmin] at e1
    rw [hr m] at e2
    linear_combination (-detFac j p.2 (F₂.T p.1)) * e1 + detFac j p.2 (F₁.T p.1) * e2

  have hread : ∑ m : ι k, F₁.u' I₀ ⟨k, m⟩ * ∑ I, F₁.u ⟨k, m⟩ I * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' =
      minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I₀ I' := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ I, ∑ m : ι k, F₁.u' I₀ ⟨k, m⟩ * (F₁.u ⟨k, m⟩ I * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I') =
        if I₀ = I then minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' else 0 := fun I => by
      by_cases hI : IsStepRows N j p.2 I
      · have e := hF₁.2.2.1 p k hp I₀ I hI₀ hI
        calc _ = (∑ m : ι k, F₁.u' I₀ ⟨k, m⟩ * F₁.u ⟨k, m⟩ I) * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun m _ => (mul_assoc _ _ _).symm
          _ = _ := by rw [e]; split_ifs <;> simp
      · have h0 : minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' = 0 := by
          rw [← hmin I]
          exact (hi.2.1 _ I (hC.mul hE) hI).resolve_right (stepCols_ne_empty p.2)
        simp [h0]
    simp only [this]
    simp
  have hsum : detFac j p.2 (F₂.T p.1) * (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') *
      minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I₀ I' =
      detFac j p.2 (F₁.T p.1) * (∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') *
        ∑ m : ι k, F₁.u' I₀ ⟨k, m⟩ * F₂.u ⟨k, m⟩ I' := by
    rw [← hread, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    linear_combination F₁.u' I₀ ⟨k, m⟩ * rel m
  rw [hm] at hsum
  generalize detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) = D at *
  generalize detFac j p.2 (F₁.T p.1) = d₁ at *
  generalize (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') = A₁ at *
  field_simp
  have h2 : d₁ * (D * A₁ * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I₀ I') =
      d₁ * ((∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') * ∑ m : ι k, F₁.u' I₀ ⟨k, m⟩ * F₂.u ⟨k, m⟩ I') := by
    linear_combination hsum
  have h3 := mul_left_cancel₀ hd₁ h2
  linear_combination h3

theorem minor_reg (hz : zb ∈ mcPts (mCoordIdeal M.x)) (hF₁ : M.IsFrame F₁) (hF₂ : M.IsFrame F₂)
    (hG₁ : M.GoodAt F₁ (mCoordIdeal zb)) (hG₂ : M.GoodAt F₂ (mCoordIdeal zb)) (p : Ψ × Fin N) (k : K)
    (hp : M.blk p = some k) {I₀ I' : Finset (Fin N)} (hI₀ : IsStepRows N j p.2 I₀)
    (hI' : IsStepRows N j p.2 I')
    (hD : RegAt M.x (mCoordIdeal zb) (detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1))⁻¹) :
    RegAt M.x (mCoordIdeal zb) (minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I₀ I') := by
  rw [minor_change M hz hF₁ hF₂ hG₁ hG₂ p k hp hI₀ hI']
  exact ValRing.regAt_mul (ValRing.regAt_mul hD (twist_ratio M hz hG₁ hG₂ p))
    (reg_sum hz _ _ fun m _ => ValRing.regAt_mul (hG₁.2.1 _ _).2 (hG₂.2.1 _ _).1).1

theorem detW_reg (hz : zb ∈ mcPts (mCoordIdeal M.x)) (hF₁ : M.IsFrame F₁) (hF₂ : M.IsFrame F₂)
    (hG₁ : M.GoodAt F₁ (mCoordIdeal zb)) (hG₂ : M.GoodAt F₂ (mCoordIdeal zb)) (τ : Ψ) (hjN : j < N) :
    RegAt M.x (mCoordIdeal zb) (minorIJ ((F₁.T τ)⁻¹ * F₂.T τ) (wIdx N j) (wIdx N j)) ∧
      RegAt M.x (mCoordIdeal zb) (minorIJ ((F₁.T τ)⁻¹ * F₂.T τ) (wIdx N j) (wIdx N j))⁻¹ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have e : wIdx N 0 = ∅ := by
      ext a
      have := a.2
      simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      omega
    rw [e, minor_empty, inv_one]
    exact ⟨ValRing.regAt_one _ _, ValRing.regAt_one _ _⟩
  · let i : Fin N := ⟨j - 1, by omega⟩
    have hi : (i : ℕ) + 1 = j := by show j - 1 + 1 = j; omega
    have hp : M.blk (τ, i) = none := (M.blk_none _).2 fun h => h.1 hi
    have h := detFac_improper M hz hF₁ hF₂ hG₁ hG₂ (τ, i) hp
    have e : detFac j i ((F₁.T τ)⁻¹ * F₂.T τ) = minorIJ ((F₁.T τ)⁻¹ * F₂.T τ) (wIdx N j) (wIdx N j) := by
      unfold detFac
      rw [if_pos (by omega), if_neg (by omega), mul_one]
    rw [← e]
    exact h

end Model2

theorem change_regular : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal M.x) → M.IsFrame F₁ → M.IsFrame F₂ → M.GoodAt F₁ (mCoordIdeal zb) → M.GoodAt F₂ (mCoordIdeal zb) → ∀ (τ : Ψ) (r s : Fin N), RegAt M.x (mCoordIdeal zb) (((F₁.T τ)⁻¹ * F₂.T τ) r s) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M zb F₁ F₂ hz hF₁ hF₂ hG₁ hG₂ τ r s
  have hjN := M.j_le
  have hT₁ := hF₁.1 τ
  have hT₂ := hF₂.1 τ
  have hu₁ : IsUnit (F₁.T τ).det := hT₁.2.isUnit
  have hC : IsBlockDiag j ((F₁.T τ)⁻¹ * F₂.T τ) := (hT₁.1.inv hu₁).mul hT₂.1
  have hr₀ := r.2
  have hs₀ := s.2
  by_cases hrs : ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)
  swap
  · rw [hC r s hrs]
    exact ValRing.regAt_zero _ _
  have proper : ∀ i : Fin N, IsProperStep N j i → ∃ k, M.blk (τ, i) = some k := fun i hi => by
    rcases h : M.blk (τ, i) with _ | k
    · exact absurd hi ((M.blk_none _).1 h)
    · exact ⟨k, rfl⟩
  by_cases hr : (r : ℕ) < N - j
  ·
    have hs := hrs.1 hr
    obtain ⟨hW, hW'⟩ := detW_reg M hz hF₁ hF₂ hG₁ hG₂ τ (by omega : j < N)
    by_cases h2 : 2 ≤ N - j
    · let i : Fin N := ⟨j, by omega⟩
      obtain ⟨k, hk⟩ := proper i ⟨by show j + 1 ≠ j; omega, by show j + 1 ≠ N; omega⟩
      have e : detFac j i ((F₁.T τ)⁻¹ * F₂.T τ) = minorIJ ((F₁.T τ)⁻¹ * F₂.T τ) (wIdx N j) (wIdx N j) := by
        unfold detFac
        rw [if_pos (by show j ≤ j + 1; omega), if_neg (by show ¬ j + 1 = N; omega), mul_one]
      have := minor_reg M hz hF₁ hF₂ hG₁ hG₂ (τ, i) k hk (isStepRows_om i rfl r hr)
        (isStepRows_om i rfl s hs) (by show RegAt _ _ (detFac j i _)⁻¹; rw [e]; exact hW')
      rwa [minor_singleton] at this
    ·
      have hNj : j + 1 = N := by omega
      let i : Fin N := ⟨N - 1, by omega⟩
      have hp : M.blk (τ, i) = none := (M.blk_none _).2 fun h => h.2 (by show N - 1 + 1 = N; omega)
      have h := (detFac_improper M hz hF₁ hF₂ hG₁ hG₂ (τ, i) hp).1
      have hd : minorIJ ((F₁.T τ)⁻¹ * F₂.T τ) (wIdx N j) (wIdx N j) * ((F₁.T τ)⁻¹ * F₂.T τ) r s =
          detFac j i ((F₁.T τ)⁻¹ * F₂.T τ) := by
        have e : omIdx N j = {r} := by
          ext a
          have := a.2
          simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
          omega
        have ers : r = s := Fin.ext (by omega)
        unfold detFac
        rw [if_pos (by show j ≤ N - 1 + 1; omega), if_pos (by show N - 1 + 1 = N; omega), e, minor_singleton, ers]
      have hdet : ((F₁.T τ)⁻¹ * F₂.T τ).det ≠ 0 := by
        rw [Matrix.det_mul, Matrix.det_nonsing_inv]
        exact mul_ne_zero (by simpa using hT₁.2) hT₂.2
      have hne := detFac_ne_zero hjN i hC hdet
      have hW0 : minorIJ ((F₁.T τ)⁻¹ * F₂.T τ) (wIdx N j) (wIdx N j) ≠ 0 := fun h0 => hne (by
        rw [← hd, h0, zero_mul])
      have e2 : ((F₁.T τ)⁻¹ * F₂.T τ) r s =
          (minorIJ ((F₁.T τ)⁻¹ * F₂.T τ) (wIdx N j) (wIdx N j))⁻¹ * detFac j i ((F₁.T τ)⁻¹ * F₂.T τ) := by
        rw [← hd, inv_mul_cancel_left₀ hW0]
      rw [e2]
      exact ValRing.regAt_mul hW' h
  ·
    have hs : ¬ (s : ℕ) < N - j := fun h => hr (hrs.2 h)
    by_cases h2 : 2 ≤ j
    · let i : Fin N := ⟨0, by omega⟩
      obtain ⟨k, hk⟩ := proper i ⟨by show 0 + 1 ≠ j; omega, by show 0 + 1 ≠ N; omega⟩
      have e : detFac j i ((F₁.T τ)⁻¹ * F₂.T τ) = 1 := by
        unfold detFac
        rw [if_neg (by show ¬ j ≤ 0 + 1; omega), if_neg (by show ¬ 0 + 1 = N; omega), mul_one]
      have := minor_reg M hz hF₁ hF₂ hG₁ hG₂ (τ, i) k hk (isStepRows_singleton_low i rfl h2 hjN r (by omega))
        (isStepRows_singleton_low i rfl h2 hjN s (by omega))
        (by show RegAt _ _ (detFac j i _)⁻¹; rw [e, inv_one]; exact ValRing.regAt_one _ _)
      rwa [minor_singleton] at this
    · have hj1 : j = 1 := by omega
      subst hj1
      let i : Fin N := ⟨0, by omega⟩
      have hp : M.blk (τ, i) = none := (M.blk_none _).2 fun h => h.1 rfl
      have h := (detFac_improper M hz hF₁ hF₂ hG₁ hG₂ (τ, i) hp).1
      have e : detFac 1 i ((F₁.T τ)⁻¹ * F₂.T τ) = ((F₁.T τ)⁻¹ * F₂.T τ) r s := by
        have ew : wIdx N 1 = {r} := by
          ext a
          have := a.2
          simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
          omega
        have ers : r = s := Fin.ext (by omega)
        unfold detFac
        rw [if_pos (by show 1 ≤ 0 + 1; omega), ew, minor_singleton, ← ers]
        split_ifs with hN1
        · have eo : omIdx N 1 = ∅ := by
            ext a
            have := a.2
            have hN1' : 0 + 1 = N := hN1
            simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            omega
          rw [eo, minor_empty, mul_one]
        · rw [mul_one]
      rw [← e]
      exact h

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.FrameReg
