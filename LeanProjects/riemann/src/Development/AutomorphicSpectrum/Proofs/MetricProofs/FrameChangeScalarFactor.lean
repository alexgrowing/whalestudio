import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBlkCover
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPointsStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FrameChange

section Unit

variable {R : Type} [CommRing R] {N : ℕ}

def unitCols (I' C : Finset (Fin N)) (e : I'.card = C.card) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun a b => ∑ s : Fin C.card,
    if a = I'.orderEmbOfFin e s ∧ b = C.orderEmbOfFin rfl s then 1 else 0

theorem unitCols_col (I' C : Finset (Fin N)) (e : I'.card = C.card) (a : Fin N) (t : Fin C.card) :
    (unitCols I' C e : Matrix (Fin N) (Fin N) R) a (C.orderEmbOfFin rfl t) =
      if a = I'.orderEmbOfFin e t then 1 else 0 := by
  simp only [unitCols, Matrix.of_apply]
  rw [Finset.sum_eq_single t]
  · simp
  · intro s _ hs
    rw [if_neg]
    rintro ⟨_, h⟩
    exact hs ((C.orderEmbOfFin rfl).injective h).symm
  · simp

theorem minor_unitCols (I' C J : Finset (Fin N)) (e : I'.card = C.card) :
    minorIJ (unitCols I' C e : Matrix (Fin N) (Fin N) R) J C = if J = I' then 1 else 0 := by
  by_cases hJ : J = I'
  · subst hJ
    rw [if_pos rfl, minorIJ, dif_pos e]
    have : (unitCols J C e : Matrix (Fin N) (Fin N) R).submatrix (J.orderEmbOfFin e) (C.orderEmbOfFin rfl) = 1 := by
      ext s t
      rw [Matrix.submatrix_apply, unitCols_col, Matrix.one_apply]
      simp
    rw [this, Matrix.det_one]
  · rw [if_neg hJ, minorIJ]
    split_ifs with e'
    · have hns : ¬ J ⊆ I' := fun hs => hJ (Finset.eq_of_subset_of_card_le hs (by rw [e, e']))
      obtain ⟨a, haJ, haI⟩ := Finset.not_subset.1 hns
      have hr : a ∈ Set.range (J.orderEmbOfFin e') := by
        rw [Finset.range_orderEmbOfFin]; exact haJ
      obtain ⟨s, rfl⟩ := hr
      refine Matrix.det_eq_zero_of_row_eq_zero s fun t => ?_
      rw [Matrix.submatrix_apply, unitCols_col, if_neg]
      intro h
      exact haI (h ▸ Finset.orderEmbOfFin_mem _ _ _)
    · rfl

theorem unitCols_blockDiag {j : ℕ} (I' C : Finset (Fin N)) (e : I'.card = C.card)
    (hs : ∀ a ∈ I', ∀ b ∈ C, ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)) :
    IsBlockDiag j (unitCols I' C e : Matrix (Fin N) (Fin N) R) := fun a b h => by
  simp only [unitCols, Matrix.of_apply]
  refine Finset.sum_eq_zero fun s _ => if_neg ?_
  rintro ⟨rfl, rfl⟩
  exact h (hs _ (Finset.orderEmbOfFin_mem _ _ _) _ (Finset.orderEmbOfFin_mem _ _ _))

theorem stepRows_same_side {j : ℕ} {i : Fin N} {I' : Finset (Fin N)} (h : IsStepRows N j i I') :
    ∀ a ∈ I', ∀ b ∈ stepCols N j i, ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) := by
  intro a ha b hb
  have h2 := h.2 ha
  have hi := i.2
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  split_ifs at h2 hb with c
  · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at h2
    omega
  · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at h2
    omega

theorem minorIJ_one_self (I : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) R) I I = 1 := by
  rw [minorIJ, dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem detFac_one (j : ℕ) (i : Fin N) : detFac j i (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  simp only [detFac, minorIJ_one_self, ite_self, mul_one]

end Unit

theorem detFac_ne_zero {Ω : Type} [Field Ω] {N j : ℕ} (hj : j ≤ N) (i : Fin N) {T : Matrix (Fin N) (Fin N) Ω}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : detFac j i T ≠ 0 := by
  intro h0
  have hu : IsUnit T.det := hd.isUnit
  have h := ((GlobalTheory.T.block_diagonal_minor_vanishing Ω N j i hj).2.2.2 T T⁻¹ hT (hT.inv hu)).2
  rw [Matrix.mul_nonsing_inv _ hu, detFac_one, h0, zero_mul] at h
  exact one_ne_zero h

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FrameChange

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

open FrameChange in

theorem plucker_change_of_frame : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), M.IsFrame F₁ → M.IsFrame F₂ → (∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) → (∀ k, M.x ⟨k, F₂.c k⟩ ≠ 0) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ ρ : M.Ω, ρ ≠ 0 ∧ ∀ (m : ι k) (I' : Finset (Fin N)), IsStepRows N j p.2 I' → ∑ I, F₁.u ⟨k, m⟩ I * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' = ρ * F₂.u ⟨k, m⟩ I' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F₁ F₂ h₁ h₂ c₁ c₂ p k hp
  have hj := M.j_le
  have hT₁ := h₁.1 p.1
  have hT₂ := h₂.1 p.1
  have hu₁ : IsUnit (F₁.T p.1).det := hT₁.2.isUnit
  have hd₁ := detFac_ne_zero hj p.2 hT₁.1 hT₁.2
  have hd₂ := detFac_ne_zero hj p.2 hT₂.1 hT₂.2
  have hA₁ : (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (c₁ k')
  have hA₂ : (∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (c₂ k')
  have hS : IsBlockDiag j ((F₁.T p.1)⁻¹ * F₂.T p.1) := (hT₁.1.inv hu₁).mul hT₂.1
  refine ⟨detFac j p.2 (F₁.T p.1) * (∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') /
    (detFac j p.2 (F₂.T p.1) * ∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k'),
    div_ne_zero (mul_ne_zero hd₁ hA₂) (mul_ne_zero hd₂ hA₁), fun m I' hI' => ?_⟩
  have hE : IsBlockDiag j (unitCols I' (stepCols N j p.2) hI'.1 : Matrix (Fin N) (Fin N) M.Ω) :=
    unitCols_blockDiag _ _ _ (stepRows_same_side hI')
  have e1 := h₁.2.1 p k hp m _ (hS.mul hE)
  have e2 := h₂.2.1 p k hp m _ hE
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu₁] at e1
  have hm : ∀ I, minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1 * unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2) =
      minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' := fun I => by
    rw [(GlobalTheory.T.block_diagonal_minor_vanishing M.Ω N j p.2 hj).1]
    simp only [minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hr : ∑ I, F₂.u ⟨k, m⟩ I * minorIJ (unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2) =
      F₂.u ⟨k, m⟩ I' := by
    simp only [minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [hm] at e1
  rw [hr] at e2
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hd₂ hA₁)]
  linear_combination (-detFac j p.2 (F₂.T p.1)) * e1 + detFac j p.2 (F₁.T p.1) * e2

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
