import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.FrameExt

section Minors

variable {R : Type} [CommRing R] {S : Type} [CommRing S] {N : ℕ}

theorem minorIJ_map (ρ : R →+* S) (T : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (T.map ρ) I J = ρ (minorIJ T I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]
    rfl
  · simp

theorem detFac_map (ρ : R →+* S) (j : ℕ) (i : Fin N) (T : Matrix (Fin N) (Fin N) R) :
    detFac j i (T.map ρ) = ρ (detFac j i T) := by
  unfold detFac
  simp only [minorIJ_map, map_mul]
  split_ifs <;> simp

def moveMat (R : Type) [CommRing R] (I C : Finset (Fin N)) (e : I.card = C.card) : Matrix (Fin N) (Fin N) R :=
  fun a b => ∑ t : Fin C.card, if a = I.orderEmbOfFin e t ∧ b = C.orderEmbOfFin rfl t then 1 else 0

theorem moveMat_apply (I C : Finset (Fin N)) (e : I.card = C.card) (s t : Fin C.card) :
    moveMat R I C e (I.orderEmbOfFin e s) (C.orderEmbOfFin rfl t) = if s = t then 1 else 0 := by
  unfold moveMat
  rw [Finset.sum_eq_single t]
  · simp
  · intro t' _ h
    rw [if_neg]
    rintro ⟨-, h2⟩
    exact h ((C.orderEmbOfFin rfl).injective h2).symm
  · simp

theorem moveMat_eq_zero (I C : Finset (Fin N)) (e : I.card = C.card) {a b : Fin N}
    (h : ¬ (a ∈ I ∧ b ∈ C)) : moveMat R I C e a b = 0 := by
  unfold moveMat
  refine Finset.sum_eq_zero fun t _ => if_neg ?_
  rintro ⟨rfl, rfl⟩
  exact h ⟨Finset.orderEmbOfFin_mem _ _ _, Finset.orderEmbOfFin_mem _ _ _⟩

theorem moveMat_blockDiag (j : ℕ) (I C : Finset (Fin N)) (e : I.card = C.card)
    (h : ∀ a ∈ I, ∀ b ∈ C, ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)) : IsBlockDiag j (moveMat R I C e) :=
  fun a b hab => moveMat_eq_zero I C e fun hm => hab (h a hm.1 b hm.2)

theorem minorIJ_moveMat (I C I' : Finset (Fin N)) (e : I.card = C.card) :
    minorIJ (moveMat R I C e) I' C = if I' = I then 1 else 0 := by
  by_cases hI : I' = I
  · subst hI
    rw [if_pos rfl]
    unfold minorIJ
    rw [dif_pos e]
    have : (moveMat R I' C e).submatrix (I'.orderEmbOfFin e) (C.orderEmbOfFin rfl) = 1 := by
      ext s t
      rw [Matrix.submatrix_apply, moveMat_apply, Matrix.one_apply]
    rw [this, det_one]
  · rw [if_neg hI]
    unfold minorIJ
    split_ifs with e'
    · have hex : ∃ a ∈ I', a ∉ I := by
        by_contra hc
        push_neg at hc
        exact hI (Finset.eq_of_subset_of_card_le hc (by rw [e, e']))
      obtain ⟨a, ha, haI⟩ := hex
      have hr : a ∈ Set.range (I'.orderEmbOfFin e') := by
        rw [Finset.range_orderEmbOfFin]
        exact ha
      obtain ⟨s, rfl⟩ := hr
      refine det_eq_zero_of_row_eq_zero s fun t => ?_
      rw [Matrix.submatrix_apply]
      exact moveMat_eq_zero I C e fun hm => haI hm.1
    · rfl

theorem stepRows_same (j : ℕ) (hj : j ≤ N) (i : Fin N) {I : Finset (Fin N)} (hI : IsStepRows N j i I) :
    ∀ a ∈ I, ∀ b ∈ stepCols N j i, ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) := by
  intro a ha b hb
  have hi := i.2
  have ha' := hI.2 ha
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  by_cases c : (i : ℕ) + 1 ≤ j
  · rw [if_pos c] at ha' hb
    simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at ha'
    omega
  · rw [if_neg c] at ha' hb
    simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at ha'
    omega

theorem stepCols_nonempty (j : ℕ) (hj : j ≤ N) (i : Fin N) (hp : IsProperStep N j i) :
    stepCols N j i ≠ ∅ := by
  have hi := i.2
  obtain ⟨h1, h2⟩ := hp
  by_cases c : (i : ℕ) + 1 ≤ j
  · refine Finset.Nonempty.ne_empty ⟨⟨N - j, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_pos c]
    omega
  · refine Finset.Nonempty.ne_empty ⟨⟨0, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_neg c]
    omega

theorem coeff_eq (j : ℕ) (hj : j ≤ N) (i : Fin N) (T : Matrix (Fin N) (Fin N) R) (c u : Finset (Fin N) → R) (D P : R)
    (H : ∀ h : Matrix (Fin N) (Fin N) R, IsBlockDiag j h →
      D * ∑ I, c I * minorIJ (T * h) I (stepCols N j i) = P * ∑ I, u I * minorIJ h I (stepCols N j i))
    (I₀ : Finset (Fin N)) (hI : IsStepRows N j i I₀) :
    D * ∑ I, c I * minorIJ T I I₀ = P * u I₀ := by
  have h1 := H (moveMat R I₀ (stepCols N j i) hI.1) (moveMat_blockDiag j _ _ _ (stepRows_same j hj i hI))
  have cb := (GlobalTheory.T.block_diagonal_minor_vanishing R N j i hj).1
  simp only [cb, minorIJ_moveMat, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  exact h1

theorem map_identity (j : ℕ) (hj : j ≤ N) (i : Fin N) (hC : stepCols N j i ≠ ∅) (T : Matrix (Fin N) (Fin N) R)
    (c u : Finset (Fin N) → R) (D P : R)
    (H : ∀ h : Matrix (Fin N) (Fin N) R, IsBlockDiag j h →
      D * ∑ I, c I * minorIJ (T * h) I (stepCols N j i) = P * ∑ I, u I * minorIJ h I (stepCols N j i))
    (ρ : R →+* S) (h : Matrix (Fin N) (Fin N) S) (hh : IsBlockDiag j h) :
    ρ D * ∑ I, ρ (c I) * minorIJ (T.map ρ * h) I (stepCols N j i) =
      ρ P * ∑ I, ρ (u I) * minorIJ h I (stepCols N j i) := by
  have cb := (GlobalTheory.T.block_diagonal_minor_vanishing S N j i hj).1
  have l : ρ D * ∑ I, ρ (c I) * minorIJ (T.map ρ * h) I (stepCols N j i) =
      ∑ I', ρ (D * ∑ I, c I * minorIJ T I I') * minorIJ h I' (stepCols N j i) := by
    simp only [cb, minorIJ_map, map_mul, map_sum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have r : ρ P * ∑ I, ρ (u I) * minorIJ h I (stepCols N j i) =
      ∑ I', ρ (P * u I') * minorIJ h I' (stepCols N j i) := by
    simp only [map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [l, r]
  refine Finset.sum_congr rfl fun I' _ => ?_
  by_cases hI : IsStepRows N j i I'
  · rw [coeff_eq j hj i T c u D P H I' hI]
  · rw [((GlobalTheory.T.block_diagonal_minor_vanishing S N j i hj).2.1 h I' hh hI).resolve_right hC, mul_zero, mul_zero]

end Minors

theorem frame_identity_map : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (S : Type) [CommRing S] (ρ : M.Ω →+* S) (F : FrameData ι Ψ N M.Ω M.blk), M.IsFrame F → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∀ (m : ι k) (h : Matrix (Fin N) (Fin N) S), IsBlockDiag j h → detFac j p.2 ((F.T p.1).map ρ) * ∑ I, ρ (M.coef ⟨k, m⟩ I) * minorIJ ((F.T p.1).map ρ * h) I (stepCols N j p.2) = ρ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * ∑ I, ρ (F.u ⟨k, m⟩ I) * minorIJ h I (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M S _ ρ F hF p k hp m h hh
  have hprop : IsProperStep N j p.2 := by
    by_contra hc
    rw [(M.blk_none p).2 hc] at hp
    exact absurd hp (by simp)
  rw [detFac_map]
  exact map_identity j M.j_le p.2 (stepCols_nonempty j M.j_le p.2 hprop) (F.T p.1) _ _ _ _
    (fun h' hh' => hF.2.1 p k hp m h' hh') ρ h hh

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.FrameExt
