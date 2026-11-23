import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PlueckerCoordinates.IsHodgeFibrePt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PlueckerCoordinates.FlagLine
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open scoped Matrix

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ωf : Type} [Field Ωf]

theorem isMultiHomog_neg {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) : IsMultiHomog (-g) d :=
  fun m hm => hg m (by simpa using hm)

theorem isValueAt_unique {y : (Σ k, ι k) → Ωf} {s : Ωf} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {v v' : ℂ} (h : IsValueAt y s z v) (h' : IsValueAt y s z v') :
    v = v' := by
  obtain ⟨d, g, h0, hg, hh, -, heq, hz0, rfl⟩ := h
  obtain ⟨d', g', h0', hg', hh', -, heq', hz0', rfl⟩ := h'
  have hhom : IsMultiHomog (g * h0' + -(g' * h0)) (d + d') := by
    refine isMultiHomog_add (isMultiHomog_mul hg hh') (isMultiHomog_neg ?_)
    rw [add_comm]
    exact isMultiHomog_mul hg' hh
  have haev : aeval y (g * h0' + -(g' * h0)) = 0 := by
    rw [map_add, map_neg, map_mul, map_mul, heq, heq']
    ring
  have := eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero y hhom haev)
  simp only [map_add, map_neg, map_mul] at this
  rw [div_eq_div_iff hz0 hz0']
  linear_combination this

theorem isValueAt_mul {y : (Σ k, ι k) → Ωf} {s₁ s₂ : Ωf} {z : (Σ k, ι k) → ℂ} {v₁ v₂ : ℂ}
    (h₁ : IsValueAt y s₁ z v₁) (h₂ : IsValueAt y s₂ z v₂) : IsValueAt y (s₁ * s₂) z (v₁ * v₂) := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := h₁
  obtain ⟨d', g', h', hg', hh', hy', heq', hz0', rfl⟩ := h₂
  refine ⟨d + d', g * g', h * h', isMultiHomog_mul hg hg', isMultiHomog_mul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · rw [map_mul, map_mul, heq, heq']; ring
  · rw [map_mul, map_mul]; exact mul_ne_zero hz0 hz0'
  · rw [map_mul, map_mul, map_mul, map_mul]; field_simp

theorem isValueAt_add {y : (Σ k, ι k) → Ωf} {s₁ s₂ : Ωf} {z : (Σ k, ι k) → ℂ} {v₁ v₂ : ℂ}
    (h₁ : IsValueAt y s₁ z v₁) (h₂ : IsValueAt y s₂ z v₂) : IsValueAt y (s₁ + s₂) z (v₁ + v₂) := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := h₁
  obtain ⟨d', g', h', hg', hh', hy', heq', hz0', rfl⟩ := h₂
  refine ⟨d + d', g * h' + g' * h, h * h', isMultiHomog_add (isMultiHomog_mul hg hh') ?_,
    isMultiHomog_mul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [add_comm]; exact isMultiHomog_mul hg' hh
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · rw [map_add, map_mul, map_mul, map_mul, heq, heq']; ring
  · rw [map_mul, map_mul]; exact mul_ne_zero hz0 hz0'
  · simp only [map_add, map_mul]; field_simp

theorem isValueAt_zero' (y : (Σ k, ι k) → Ωf) (z : (Σ k, ι k) → ℂ) : IsValueAt y 0 z 0 :=
  ⟨0, 0, 1, isMultiHomog_zero 0, isMultiHomog_one, by simp, by simp, by simp, by simp⟩

theorem isValueAt_inv {y : (Σ k, ι k) → Ωf} {s : Ωf} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {v : ℂ} (h : IsValueAt y s z v) (hv : v ≠ 0) :
    IsValueAt y s⁻¹ z v⁻¹ := by
  obtain ⟨d, g, h0, hg, hh, hy, heq, hz0, rfl⟩ := h
  have hgz : eval z (map (Int.castRingHom ℂ) g) ≠ 0 := fun h' => hv (by rw [h', zero_div])
  have hgy : aeval y g ≠ 0 := fun h' =>
    hgz (eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero y hg h'))
  have hs : s ≠ 0 := fun h' => hgy (by rw [heq, h', zero_mul])
  refine ⟨d, h0, g, hh, hg, hgy, ?_, hgz, ?_⟩
  · rw [heq]; field_simp
  · rw [inv_div]

theorem isValueAt_pow {y : (Σ k, ι k) → Ωf} {s : Ωf} {z : (Σ k, ι k) → ℂ} {v : ℂ}
    (h : IsValueAt y s z v) (n : ℕ) : IsValueAt y (s ^ n) z (v ^ n) := by
  induction n with
  | zero => simpa using isValueAt_one_self y z
  | succ k ih => rw [pow_succ, pow_succ]; exact isValueAt_mul ih h

theorem isValueAt_sum {y : (Σ k, ι k) → Ωf} {z : (Σ k, ι k) → ℂ} {n : ℕ} (s : Fin n → Ωf) (v : Fin n → ℂ)
    (h : ∀ i, IsValueAt y (s i) z (v i)) : IsValueAt y (∑ i, s i) z (∑ i, v i) := by
  induction n with
  | zero => simpa using isValueAt_zero' y z
  | succ n ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    exact isValueAt_add (h 0) (ih _ _ fun i => h i.succ)

end Values

section LineValues

theorem isValueAt_ratio (z : (Σ _ : Unit, Fin 2) → ℂ) (i c : Fin 2) (hc : z ⟨(), c⟩ ≠ 0) :
    IsValueAt yLine (yLine ⟨(), i⟩ / yLine ⟨(), c⟩) z (z ⟨(), i⟩ / z ⟨(), c⟩) := by
  refine ⟨fun _ => 1, X ⟨(), i⟩, X ⟨(), c⟩, isMultiHomog_X_line i, isMultiHomog_X_line c, ?_, ?_, ?_, ?_⟩
  · simpa using yLine_ne_zero _
  · have := yLine_ne_zero ⟨(), c⟩
    simp only [aeval_X]
    field_simp
  · simpa using hc
  · simp

theorem exists_value_of_mem_chartRing (c : (k : Unit) → PBlk 2 k) (z : (Σ _ : Unit, Fin 2) → ℂ)
    (hc : z ⟨(), c ()⟩ ≠ 0) {r : Ω} (hr : r ∈ chartRing ℤ (segreCoord yLine) c) :
    ∃ v, IsValueAt yLine r z v := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨c', rfl⟩ := hx
    refine ⟨z ⟨(), c' ()⟩ / z ⟨(), c ()⟩, ?_⟩
    have e1 : segreCoord yLine c' = yLine ⟨(), c' ()⟩ := by simp [segreCoord]
    have e2 : segreCoord yLine c = yLine ⟨(), c ()⟩ := by simp [segreCoord]
    show IsValueAt yLine (segreCoord yLine c' / segreCoord yLine c) z _
    rw [e1, e2]
    exact isValueAt_ratio z (c' ()) (c ()) hc
  | algebraMap a => exact ⟨a, by simpa using isValueAt_intCast z a⟩
  | add x y _ _ hx hy =>
    obtain ⟨v, hv⟩ := hx
    obtain ⟨w, hw⟩ := hy
    exact ⟨v + w, isValueAt_add hv hw⟩
  | mul x y _ _ hx hy =>
    obtain ⟨v, hv⟩ := hx
    obtain ⟨w, hw⟩ := hy
    exact ⟨v * w, isValueAt_mul hv hw⟩

end LineValues

section MuModel

def muVec (z : (Σ _ : Unit, Fin 2) → ℂ) : (Σ k : MuBlocks DL, ιMu PL k) → ℂ
  | ⟨Sum.inl _, i⟩ => z ⟨(), i⟩
  | ⟨Sum.inr (Sum.inl τ), m⟩ => if (show Fin (PL.M τ (jIdx DL)) from m).val = 0 then 1 else 0
  | ⟨Sum.inr (Sum.inr _), _⟩ => 1

end MuModel

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
