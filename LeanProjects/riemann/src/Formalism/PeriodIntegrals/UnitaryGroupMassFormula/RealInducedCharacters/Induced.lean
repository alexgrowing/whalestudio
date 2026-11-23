import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RealInducedCharacters.InducedCharRealised

set_option autoImplicit false

namespace BrauerSchur

open scoped BigOperators

section Induced

variable {G : Type*} [Group G] {K : Type*} [Field K] (H : Subgroup G) (ψ : H →* Kˣ)

open scoped Classical in

noncomputable def dot (x : G) : K := if hx : x ∈ H then ((ψ ⟨x, hx⟩ : Kˣ) : K) else 0

theorem dot_mul_of_mem {a b : G} (hb : b ∈ H) : dot H ψ a * dot H ψ b = dot H ψ (a * b) := by
  classical
  unfold dot
  by_cases ha : a ∈ H
  · rw [dif_pos ha, dif_pos hb, dif_pos (H.mul_mem ha hb), ← Units.val_mul, ← map_mul]
    rfl
  · have hab : a * b ∉ H := fun h => ha (by
      have := H.mul_mem h (H.inv_mem hb)
      rwa [mul_inv_cancel_right] at this)
    rw [dif_neg ha, dif_neg hab, zero_mul]

theorem dot_conj {h : G} (hh : h ∈ H) (y : G) : dot H ψ (h⁻¹ * y * h) = dot H ψ y := by
  classical
  unfold dot
  by_cases hy : y ∈ H
  · have hm : h⁻¹ * y * h ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hh) hy) hh
    rw [dif_pos hy, dif_pos hm]
    have e : (⟨h⁻¹ * y * h, hm⟩ : H) = (⟨h, hh⟩ : H)⁻¹ * ⟨y, hy⟩ * ⟨h, hh⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  · have hm : h⁻¹ * y * h ∉ H := fun hm => hy (by
      have e : y = h * (h⁻¹ * y * h) * h⁻¹ := by group
      rw [e]
      exact H.mul_mem (H.mul_mem hh hm) (H.inv_mem hh))
    rw [dif_neg hy, dif_neg hm]

variable {m : ℕ} (t : Fin m → G)

noncomputable def indMat (g : G) : Matrix (Fin m) (Fin m) K :=
  fun i j => dot H ψ ((t i)⁻¹ * g * t j)

theorem indMat_one (ht : ∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j) : indMat H ψ t 1 = 1 := by
  classical
  ext i j
  simp only [indMat, mul_one]
  rw [Matrix.one_apply]
  unfold dot
  split_ifs with h1 h2 h2
  · subst h2
    have e : (⟨(t i)⁻¹ * t i, h1⟩ : H) = 1 := Subtype.ext (inv_mul_cancel _)
    rw [e, map_one, Units.val_one]
  · exact absurd ((ht i j).mp h1) h2
  · exact absurd ((ht i j).mpr h2) h1
  · rfl

theorem indMat_mul (ht : ∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j) (hc : ∀ x : G, ∃ i, (t i)⁻¹ * x ∈ H)
    (g g' : G) : indMat H ψ t (g * g') = indMat H ψ t g * indMat H ψ t g' := by
  ext i k
  rw [Matrix.mul_apply]
  obtain ⟨j0, hj0⟩ := hc (g' * t k)
  have hb : (t j0)⁻¹ * g' * t k ∈ H := by rwa [mul_assoc]
  rw [Finset.sum_eq_single j0]
  · simp only [indMat]
    rw [dot_mul_of_mem H ψ hb]
    congr 1
    group
  · intro j _ hj
    simp only [indMat]
    have hz : dot H ψ ((t j)⁻¹ * g' * t k) = 0 := by
      classical
      unfold dot
      rw [dif_neg]
      intro hm
      apply hj
      rw [← ht j j0]
      have e : (t j)⁻¹ * t j0 = ((t j)⁻¹ * g' * t k) * ((t j0)⁻¹ * g' * t k)⁻¹ := by group
      rw [e]
      exact H.mul_mem hm (H.inv_mem hb)
    rw [hz, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

noncomputable def indRep (ht : ∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j) (hc : ∀ x : G, ∃ i, (t i)⁻¹ * x ∈ H) :
    Representation K G (Fin m → K) where
  toFun g := Matrix.toLin' (indMat H ψ t g)
  map_one' := by rw [indMat_one H ψ t ht, Matrix.toLin'_one]; rfl
  map_mul' g g' := by rw [indMat_mul H ψ t ht hc, Matrix.toLin'_mul]; rfl

theorem indRep_trace (ht : ∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j) (hc : ∀ x : G, ∃ i, (t i)⁻¹ * x ∈ H)
    (g : G) : LinearMap.trace K (Fin m → K) (indRep H ψ t ht hc g) = ∑ i, dot H ψ ((t i)⁻¹ * g * t i) := by
  show LinearMap.trace K (Fin m → K) (Matrix.toLin' (indMat H ψ t g)) = _
  rw [Matrix.trace_toLin'_eq]
  rfl

theorem indFun_eq_sum [Fintype G] [CharZero K] (ht : ∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j)
    (hc : ∀ x : G, ∃ i, (t i)⁻¹ * x ∈ H) (g : G) :
    indFun H (fun h => ((ψ h : Kˣ) : K)) g = ∑ i, dot H ψ ((t i)⁻¹ * g * t i) := by
  classical
  show (Nat.card H : K)⁻¹ * ∑ x : G, dot H ψ (x⁻¹ * g * x) = _
  let f : Fin m × H → G := fun p => t p.1 * p.2
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, h⟩ ⟨j, h'⟩ hij
      simp only [f] at hij
      have hij' : i = j := by
        rw [← ht i j]
        have e : (t i)⁻¹ * t j = (h : G) * (h' : G)⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← hij, inv_mul_cancel_left]
        rw [e]
        exact H.mul_mem h.2 (H.inv_mem h'.2)
      subst hij'
      have : (h : G) = h' := mul_left_cancel hij
      rw [Subtype.ext this]
    · intro x
      obtain ⟨i, hi⟩ := hc x
      exact ⟨⟨i, ⟨_, hi⟩⟩, by simp [f]⟩
  rw [← Fintype.sum_bijective f hf (fun p => dot H ψ ((f p)⁻¹ * g * f p)) _ (fun _ => rfl),
    Fintype.sum_prod_type]
  have hin : ∀ i, ∑ h : H, dot H ψ ((f (i, h))⁻¹ * g * f (i, h)) =
      (Fintype.card H : K) * dot H ψ ((t i)⁻¹ * g * t i) := by
    intro i
    have : ∀ h : H, dot H ψ ((f (i, h))⁻¹ * g * f (i, h)) = dot H ψ ((t i)⁻¹ * g * t i) := by
      intro h
      have e : (f (i, h))⁻¹ * g * f (i, h) = (h : G)⁻¹ * ((t i)⁻¹ * g * t i) * h := by
        simp only [f]
        group
      rw [e, dot_conj H ψ h.2]
    rw [Finset.sum_congr rfl fun h _ => this h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun i _ => hin i, ← Finset.mul_sum, ← mul_assoc, Nat.card_eq_fintype_card,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

end Induced

end BrauerSchur
