import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeTateSurjectivePositiveDim

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

theorem rank_equality : HodgeTateDimensionEquality := by
  intro l _ K _ P M n hS hV hI hJ
  classical
  have hfd : ∀ a, FiniteDimensional K (Hdg M.q a n) := fun a => (P.fin M hS a n).1
  let m : ℕ → ℕ := fun a => Module.finrank K (Hdg M.q a n)
  let bH : ∀ a, Module.Basis (Fin (m a)) K (Hdg M.q a n) := fun a => Module.finBasis K _
  let bV := Module.finBasis ℚ_[l] (M.V n)
  let ι := Σ a : Fin (n + 1), Fin (m a)
  have hcard : Fintype.card ι = ∑ a ∈ Finset.range (n + 1), m a := by
    simp only [ι, Fintype.card_sigma, Fintype.card_fin]
    exact Fin.sum_univ_eq_sum_range (fun a => m a) (n + 1)
  have hdual : ∀ a (v : M.V n) (φ : Module.Dual K (Hdg M.q a n)),
      P.h M a n v φ = ∑ s, kC K (φ (bH a s)) * P.h M a n v ((bH a).coord s) := by
    intro a v φ
    conv_lhs => rw [← (bH a).sum_dual_apply_smul_coord φ]
    rw [map_sum]
    exact Finset.sum_congr rfl fun s _ => P.lin' M a n _ v _
  have hexp : ∀ a (v : M.V n) (φ : Module.Dual K (Hdg M.q a n)),
      P.h M a n v φ = ∑ i, qC l (bV.repr v i) * P.h M a n (bV i) φ := by
    intro a v φ
    conv_lhs => rw [← bV.sum_repr v]
    rw [map_sum, AddMonoidHom.finsetSum_apply]
    exact Finset.sum_congr rfl fun i _ => P.lin M a n _ _ φ
  have h1 : Module.finrank ℚ_[l] (M.V n) ≤ Fintype.card ι := by
    let r : Fin (Module.finrank ℚ_[l] (M.V n)) → (ι → ℂ_[l]) :=
      fun i p => P.h M p.1 n (bV i) ((bH p.1).coord p.2)
    have hr : LinearIndependent ℂ_[l] r := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have hg' : ∀ (a : Fin (n + 1)) s, ∑ i, g i * P.h M a n (bV i) ((bH a).coord s) = 0 := by
        intro a s
        have := congrFun hg ⟨a, s⟩
        simpa [r, Finset.sum_apply] using this
      have hz := hI bV g ?_
      · intro i; exact congrFun hz i
      intro a φ
      by_cases ha : n < a
      · have := (P.fin M hS a n).2 ha
        have h0 : φ = 0 := by
          ext x
          simp [Subsingleton.elim x 0]
        subst h0
        simp
      · have key : ∀ s, ∑ i, g i * P.h M a n (bV i) ((bH a).coord s) = 0 :=
          fun s => hg' ⟨a, Nat.lt_succ_of_le (not_lt.1 ha)⟩ s
        calc ∑ i, g i * P.h M a n (bV i) φ
            = ∑ i, ∑ s, kC K (φ (bH a s)) * (g i * P.h M a n (bV i) ((bH a).coord s)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hdual, Finset.mul_sum]
              refine Finset.sum_congr rfl fun s _ => ?_
              ring
          _ = ∑ s, kC K (φ (bH a s)) * ∑ i, g i * P.h M a n (bV i) ((bH a).coord s) := by
              rw [Finset.sum_comm]
              simp_rw [Finset.mul_sum]
          _ = 0 := by simp [key]
    have := hr.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card] using this
  have h2 : Fintype.card ι ≤ Module.finrank ℚ_[l] (M.V n) := by
    let c : ι → (Fin (Module.finrank ℚ_[l] (M.V n)) → ℂ_[l]) :=
      fun p i => P.h M p.1 n (bV i) ((bH p.1).coord p.2)
    have hc : LinearIndependent ℂ_[l] c := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have hg' : ∀ i, ∑ p : ι, g p * P.h M p.1 n (bV i) ((bH p.1).coord p.2) = 0 := by
        intro i
        have := congrFun hg i
        simpa [c, Finset.sum_apply] using this
      let z : ∀ a, Fin (m a) → ℂ_[l] := fun a s => if h : a < n + 1 then g ⟨⟨a, h⟩, s⟩ else 0
      have e : ∀ i, ∑ a ∈ Finset.range (n + 1), ∑ s, z a s * P.h M a n (bV i) ((bH a).coord s) = 0 := by
        intro i
        rw [Finset.sum_range, ← hg' i, Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
        simp only [z]
        rw [dif_pos a.isLt]
      have hz := hJ bH z ?_
      · rintro ⟨⟨a, ha⟩, s⟩
        have := congrFun (hz a (Nat.lt_succ_iff.1 ha)) s
        simp only [z, dif_pos ha] at this
        exact this
      intro v
      calc ∑ a ∈ Finset.range (n + 1), ∑ s, z a s * P.h M a n v ((bH a).coord s)
          = ∑ a ∈ Finset.range (n + 1), ∑ s, ∑ i,
              qC l (bV.repr v i) * (z a s * P.h M a n (bV i) ((bH a).coord s)) := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
            rw [hexp, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ = ∑ a ∈ Finset.range (n + 1), ∑ i, ∑ s,
              qC l (bV.repr v i) * (z a s * P.h M a n (bV i) ((bH a).coord s)) :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ i, ∑ a ∈ Finset.range (n + 1), ∑ s,
              qC l (bV.repr v i) * (z a s * P.h M a n (bV i) ((bH a).coord s)) := Finset.sum_comm
        _ = ∑ i, qC l (bV.repr v i) * ∑ a ∈ Finset.range (n + 1), ∑ s,
              z a s * P.h M a n (bV i) ((bH a).coord s) := by
            simp_rw [Finset.mul_sum]
        _ = 0 := by simp [e]
    have := hc.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card] using this
  have := le_antisymm h1 h2
  rw [this, hcard]

end CrystallineSemistableComparison.Onto

end
