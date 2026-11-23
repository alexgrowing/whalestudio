import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MinorDeterminants
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PlVanish

theorem cols_ne_empty {N j : ℕ} (hj : j ≤ N) (i : Fin N) : stepCols N j i ≠ ∅ := by
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

theorem minor_one_ne {N : ℕ} {I J : Finset (Fin N)} (h : I ≠ J) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I J = 0 := by
  unfold minorIJ
  split_ifs with e
  · obtain ⟨a, ha, hb⟩ : ∃ a ∈ I, a ∉ J := by
      by_contra hc
      push_neg at hc
      exact h (Finset.eq_of_subset_of_card_le hc e.ge)
    obtain ⟨r, hr⟩ : ∃ r, I.orderEmbOfFin e r = a := by
      have h2 : a ∈ Set.range (I.orderEmbOfFin e) := by
        rw [Finset.range_orderEmbOfFin]
        exact ha
      exact h2
    refine Matrix.det_eq_zero_of_row_eq_zero r fun c => ?_
    rw [Matrix.submatrix_apply, hr]
    exact Matrix.one_apply_ne fun q => hb (q ▸ Finset.orderEmbOfFin_mem _ _ _)
  · rfl

theorem minor_one_same {N : ℕ} (I : Finset (Fin N)) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I I = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem det_submatrix_eq_zero {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N))
    (f : Fin S.card → Fin N) (hf : Function.Injective f)
    (h0 : minorIJ C (Finset.univ.image f) S = 0) :
    (C.submatrix f (S.orderEmbOfFin rfl)).det = 0 :=
  _root_.UpperTheory.Reformulated.B.MinorDeterminants.main C S f hf h0

theorem minor_quot {N j : ℕ} (hj : j ≤ N) (i : Fin N) {h₁ h₂ : Matrix (Fin N) (Fin N) ℂ} {α β : ℂ}
    (hb₁ : IsBlockDiag j h₁) (hb₂ : IsBlockDiag j h₂) (hd : h₁.det ≠ 0)
    (hp : ∀ I, IsStepRows N j i I → α * minorIJ h₁ I (stepCols N j i) = β * minorIJ h₂ I (stepCols N j i))
    (I : Finset (Fin N)) :
    β * minorIJ (h₁⁻¹ * h₂) I (stepCols N j i) =
      α * minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I (stepCols N j i) := by
  obtain ⟨cb, off, -, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main ℂ N j i hj
  have hne := cols_ne_empty hj i
  have hall : ∀ J, α * minorIJ h₁ J (stepCols N j i) = β * minorIJ h₂ J (stepCols N j i) := fun J => by
    by_cases hJ : IsStepRows N j i J
    · exact hp J hJ
    · rw [(off h₁ J hb₁ hJ).resolve_right hne, (off h₂ J hb₂ hJ).resolve_right hne, mul_zero, mul_zero]
  have e1 : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I (stepCols N j i) =
      minorIJ (h₁⁻¹ * h₁) I (stepCols N j i) := by
    rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hd)]
  rw [e1, cb, cb, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  linear_combination (-minorIJ h₁⁻¹ I J) * hall J

theorem quot_vanish : ∀ (N j : ℕ) (i : Fin N) (h₁ h₂ : Matrix (Fin N) (Fin N) ℂ) (α β : ℂ), j ≤ N →
    IsBlockDiag j h₁ → IsBlockDiag j h₂ → h₁.det ≠ 0 → α ≠ 0 → β ≠ 0 →
    (∀ I, IsStepRows N j i I → α * minorIJ h₁ I (stepCols N j i) = β * minorIJ h₂ I (stepCols N j i)) →
    ∀ r c, c ∈ stepCols N j i → r ∉ stepCols N j i → (h₁⁻¹ * h₂) r c = 0 := by
  intro N j i h₁ h₂ α β hj hb₁ hb₂ hd hα hβ hp r c hc hr
  have hq := minor_quot hj i hb₁ hb₂ hd hp
  set S := stepCols N j i with hS
  set C := h₁⁻¹ * h₂ with hC
  let e := S.orderEmbOfFin rfl
  obtain ⟨t, ht⟩ : ∃ t, e t = c := by
    have h2 : c ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]
      exact hc
    exact h2
  let D : Matrix (Fin S.card) (Fin S.card) ℂ := C.submatrix e e
  have hD : D.det ≠ 0 := by
    have h1 := hq S
    rw [minor_one_same, mul_one] at h1
    have h2 : minorIJ C S S = D.det := dif_pos rfl
    rw [← h2]
    intro h0
    rw [h0, mul_zero] at h1
    exact hα h1.symm
  let v : Fin S.card → ℂ := fun s => C r (e s)
  have hrow : ∀ u, (D.updateRow u v).det = 0 := fun u => by
    let f : Fin S.card → Fin N := Function.update e u r
    have hmem : ∀ s, e s ∈ S := fun s => Finset.orderEmbOfFin_mem _ _ _
    have hf : Function.Injective f := fun a b hab => by
      by_cases ha : a = u
      · by_cases hb : b = u
        · rw [ha, hb]
        · subst ha
          simp only [f, Function.update_self, Function.update_of_ne hb] at hab
          exact absurd (hab ▸ hmem b) hr
      · by_cases hb : b = u
        · subst hb
          simp only [f, Function.update_self, Function.update_of_ne ha] at hab
          exact absurd (hab ▸ hmem a) hr
        · simp only [f, Function.update_of_ne ha, Function.update_of_ne hb] at hab
          exact e.injective hab
    have hI : Finset.univ.image f ≠ S := fun h => hr (by
      rw [← h]
      exact Finset.mem_image.2 ⟨u, Finset.mem_univ _, Function.update_self _ _ _⟩)
    have h0 : minorIJ C (Finset.univ.image f) S = 0 := by
      have h1 := hq (Finset.univ.image f)
      rw [minor_one_ne hI, mul_zero] at h1
      exact (mul_eq_zero.1 h1).resolve_left hβ
    have h2 := det_submatrix_eq_zero C S f hf h0
    have e2 : D.updateRow u v = C.submatrix f e := by
      ext a b
      by_cases ha : a = u
      · subst ha
        simp [f, D, v, Matrix.updateRow_self]
      · simp [f, D, Matrix.updateRow_ne ha, Function.update_of_ne ha]
    rw [e2]
    exact h2
  have hcr : Dᵀ.cramer v = 0 := by
    funext u
    rw [Matrix.cramer_transpose_apply]
    exact hrow u
  have h3 := Matrix.mulVec_cramer Dᵀ v
  rw [hcr, Matrix.mulVec_zero, Matrix.det_transpose] at h3
  have h4 : D.det * v t = 0 := by
    have := congrFun h3 t
    simpa using this.symm
  have h5 : v t = 0 := (mul_eq_zero.1 h4).resolve_left hD
  rw [← ht]
  exact h5

end GlobalTheory.CompanionTheory.Ar.PB.PlVanish
