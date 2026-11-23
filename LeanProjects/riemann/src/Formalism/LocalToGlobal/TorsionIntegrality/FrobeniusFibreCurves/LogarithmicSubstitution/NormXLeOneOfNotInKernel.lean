import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.ShiftAnalyticW
import Formalism.EllipticTorsion.FormalGroupPointsNoTorsion
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementJ

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.Half

open Formalism.L2.Th1.F (MulStable IsKerReps)
open Formalism.L2.Th1.E (Unif ptW px IntCurve)
open Formalism.L2.Th1.C (wpShift HasSecondLogDeriv)
open Formalism.ELL (InFormalGroupPoints)

theorem exists_transversal (M : Submodule ℤ ℂ) (A : Finset ℂ) :
    ∃ Sq : Finset ℂ, Sq ⊆ A ∧
      (∀ Q ∈ Sq, ∀ Q' ∈ Sq, (Q - Q' ∈ M ∨ Q + Q' ∈ M) → Q = Q') ∧
      (∀ c ∈ A, ∃ Q ∈ Sq, c - Q ∈ M ∨ c + Q ∈ M) := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | insert a A _ ih =>
    obtain ⟨Sq, h0, h1, h2⟩ := ih
    by_cases ha : ∃ Q ∈ Sq, a - Q ∈ M ∨ a + Q ∈ M
    · refine ⟨Sq, h0.trans (Finset.subset_insert _ _), h1, ?_⟩
      intro c hc
      rcases Finset.mem_insert.1 hc with rfl | hc
      · exact ha
      · exact h2 c hc
    · refine ⟨insert a Sq, Finset.insert_subset_insert _ h0, ?_, ?_⟩
      · intro Q hQ Q' hQ' h
        rcases Finset.mem_insert.1 hQ with rfl | hQs
        · rcases Finset.mem_insert.1 hQ' with rfl | hQ'
          · rfl
          · exact absurd ⟨Q', hQ', h⟩ ha
        · rcases Finset.mem_insert.1 hQ' with rfl | hQ'
          · refine absurd ⟨Q, hQs, ?_⟩ ha
            rcases h with h | h
            · left
              have := M.neg_mem h
              rwa [neg_sub] at this
            · right
              rwa [add_comm] at h
          · exact h1 Q hQs Q' hQ' h
      · intro c hc
        rcases Finset.mem_insert.1 hc with rfl | hc
        · exact ⟨c, Finset.mem_insert_self _ _, Or.inl (by simp)⟩
        · obtain ⟨Q, hQ, h⟩ := h2 c hc
          exact ⟨Q, Finset.mem_insert_of_mem hQ, h⟩

theorem half_fibre_exists_holds : HalfFibreExists := by
  classical
  intro L α ω₀ hα hst _ hno
  obtain ⟨S, hS1, _, hS3⟩ := Formalism.L2.Th1.F.kerRepsExist L α hα hst
  set Q0 : ℂ := (ω₀ / 2) / α with hQ0
  have hαQ0 : α * Q0 = ω₀ / 2 := by rw [hQ0]; field_simp
  obtain ⟨Sq, h0, h1, h2⟩ :=
    exists_transversal L.lattice (insert Q0 (S.image (fun P => Q0 + P)))
  have hfib : ∀ c ∈ insert Q0 (S.image (fun P => Q0 + P)), α * c - ω₀ / 2 ∈ L.lattice := by
    intro c hc
    rcases Finset.mem_insert.1 hc with rfl | hc
    · rw [hαQ0, sub_self]; exact L.lattice.zero_mem
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hc
      have : α * (Q0 + P) - ω₀ / 2 = α * P := by rw [mul_add, hαQ0]; ring
      rw [this]; exact (hS1 P hP).1
  refine ⟨Sq, ?_, h1, ?_⟩
  · intro Q hQ
    exact ⟨hfib Q (h0 hQ), hno Q (hfib Q (h0 hQ))⟩
  · intro z hz
    have hker : α * (z - Q0) ∈ L.lattice := by
      have : α * (z - Q0) = α * z - ω₀ / 2 := by rw [mul_sub, hαQ0]
      rw [this]; exact hz
    obtain ⟨c, hc, hzc⟩ : ∃ c ∈ insert Q0 (S.image (fun P => Q0 + P)), z - c ∈ L.lattice := by
      by_cases hz0 : z - Q0 ∈ L.lattice
      · exact ⟨Q0, Finset.mem_insert_self _ _, hz0⟩
      · obtain ⟨P, hP, h⟩ := hS3 (z - Q0) hker hz0
        refine ⟨Q0 + P, Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨P, hP, rfl⟩), ?_⟩
        have : z - (Q0 + P) = z - Q0 - P := by ring
        rw [this]; exact h
    obtain ⟨Q, hQ, h⟩ := h2 c hc
    refine ⟨Q, hQ, ?_⟩
    rcases h with h | h
    · left
      have : z - Q = (z - c) + (c - Q) := by ring
      rw [this]; exact L.lattice.add_mem hzc h
    · right
      have : z + Q = (z - c) + (c + Q) := by ring
      rw [this]; exact L.lattice.add_mem hzc h

section Alg

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

theorem map_derivative (f : PowerSeries K) :
    PowerSeries.map φ (PowerSeries.derivative K f) =
      PowerSeries.derivative K' (PowerSeries.map φ f) := by
  ext n
  simp [PowerSeries.coeff_derivative]

theorem map_rescale (a : K) (f : PowerSeries K) :
    PowerSeries.map φ (PowerSeries.rescale a f) =
      PowerSeries.rescale (φ a) (PowerSeries.map φ f) := by
  ext n
  simp [PowerSeries.coeff_rescale]

theorem map_wpShift (e : PowerSeries K) (c : K) :
    PowerSeries.map φ (wpShift e c) = wpShift (PowerSeries.map φ e) (φ c) := by
  unfold wpShift
  simp

theorem second_log_derivative_map {f g : PowerSeries K} (h : HasSecondLogDeriv f g) :
    HasSecondLogDeriv (PowerSeries.map φ f) (PowerSeries.map φ g) := by
  unfold HasSecondLogDeriv at h ⊢
  have := congrArg (PowerSeries.map φ) h
  simpa [map_derivative] using this

end Alg

theorem fibre_map_holds : FibreMap := by
  intro K K' _ _ _ _ j P tr ι _ c wp wm al S h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro Q
    have := second_log_derivative_map j (h1 Q)
    have e2 : PowerSeries.map j (2 : PowerSeries K) = 2 := map_ofNat _ 2
    rw [map_wpShift] at this
    simpa [e2] using this
  · have := congrArg (PowerSeries.map j) h2
    simpa [map_rescale] using this

theorem norm_x_le_one_of_not_in_kernel {K : Type} [NormedField K] {W : WeierstrassCurve K}
    (P : W.toAffine.Point) (h : ¬ InFormalGroupPoints P) : ‖px W P‖ ≤ 1 := by
  cases P with
  | zero => exact absurd trivial h
  | some x y hxy => exact not_lt.1 h

open Classical in
theorem points_integral_at_two_holds : PointsIntTwo := by
  intro l _ L ι W hU hW α α' t0 t' t'' hα hα' hinj ht0 h1 h2 h3 h4
  obtain ⟨a1, a2, a3, a4, a6, hΔ⟩ := hW
  have hsub := Formalism.ELL.formal_group_points_subgroup.{0} ℂ_[l] W ⟨a1, a2, a3, a4, a6⟩ hΔ
  have hadd := Formalism.L2.Th1.E.ptWAdd l L ι W hU
  have hzero := Formalism.L2.Th1.E.ptWZero l L ι W hU
  have hlat : ∀ t ∈ L.lattice, InFormalGroupPoints (ptW l L ι W t) := by
    intro t ht
    rw [(hzero t).2 ht]
    trivial
  have hA : ∀ s t, InFormalGroupPoints (ptW l L ι W s) → InFormalGroupPoints (ptW l L ι W t) → InFormalGroupPoints (ptW l L ι W (s + t)) := by
    intro s t hs ht
    rw [hadd]
    exact (hsub _ _ hs ht).1
  have hneg : ∀ t, ptW l L ι W (-t) = - ptW l L ι W t := by
    intro t
    apply eq_neg_of_add_eq_zero_left
    rw [← hadd, neg_add_cancel]
    exact (hzero 0).2 L.lattice.zero_mem
  have hN : ∀ t, InFormalGroupPoints (ptW l L ι W t) → InFormalGroupPoints (ptW l L ι W (-t)) := by
    intro t ht
    rw [hneg]
    exact (hsub _ _ ht ht).2
  have ht0' : ¬ InFormalGroupPoints (ptW l L ι W t0) := by
    intro H
    have e : t'' = α' * t0 + -(α' * t') + -(α' * t'' - t'') := by rw [ht0]; ring
    have : InFormalGroupPoints (ptW l L ι W t'') := by
      rw [e]
      exact hA _ _ (hA _ _ (hα' _ H) (hN _ (hlat _ h1))) (hN _ (hlat _ h2))
    exact h3 (hinj t'' this h4)
  refine ⟨norm_x_le_one_of_not_in_kernel _ ht0', ?_⟩
  intro Q hQ
  apply norm_x_le_one_of_not_in_kernel
  intro H
  apply ht0'
  have e : t0 = α * Q + -(α * Q - t0) := by ring
  rw [e]
  exact hA _ _ (hα _ H) (hN _ (hlat _ hQ))

end Formalism.L2.Th1.B.Half
