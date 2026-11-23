import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.FlagUnipotentLattices.AlgebraicIdentityHigherDegree
import Formalism.FormalDegreeBessel.FinalDS

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma MeasureTheory

theorem deg_epsI_empty {N : ℕ} : epsI (∅ : Finset (Fin N)) = 0 := by
  funext x; simp [epsI]

theorem deg_epsI_insert {N : ℕ} (I : Finset (Fin N)) (a : Fin N) (ha : a ∉ I) :
    epsI (insert a I) = epsI I + Pi.single a 1 := by
  funext x
  by_cases hx : x = a
  · subst hx; simp [epsI, ha]
  · simp [epsI, hx]

theorem deg_hc_int {N : ℕ} {μ : Fin N → ℝ} (h : IsHCParam μ) (I : Finset (Fin N)) (x : Fin N) :
    ∃ m : ℤ, (μ + epsI I) x - ((N : ℝ) - 1) / 2 = (m : ℝ) := by
  obtain ⟨m, hm⟩ := h.2 x
  by_cases hx : x ∈ I
  · refine ⟨m + 1, ?_⟩
    simp only [Pi.add_apply, epsI, if_pos hx]
    push_cast
    linarith
  · refine ⟨m, ?_⟩
    simp only [Pi.add_apply, epsI, if_neg hx]
    linarith

theorem deg_hc_diff {N : ℕ} {μ : Fin N → ℝ} (h : IsHCParam μ) (a b : Fin N) : ∃ m : ℤ, μ a - μ b = (m : ℝ) := by
  obtain ⟨m, hm⟩ := h.2 a
  obtain ⟨m', hm'⟩ := h.2 b
  refine ⟨m - m', ?_⟩
  push_cast
  linarith

theorem deg_hc_drop {N : ℕ} {μ : Fin N → ℝ} (h : IsHCParam μ) (I : Finset (Fin N)) (a : Fin N)
    (hmax : ∀ x ∈ I, x < a) (h' : IsHCParam (μ + epsI (insert a I))) : IsHCParam (μ + epsI I) := by
  refine ⟨fun i j hij => ?_, deg_hc_int h I⟩
  have h1 := h.1 hij
  have h2 := h'.1 hij
  have ha : a ∉ I := fun hh => lt_irrefl _ (hmax a hh)
  simp only [Pi.add_apply, epsI, Finset.mem_insert] at h2 ⊢
  by_cases hja : j = a
  · subst hja
    rw [if_neg ha]
    split_ifs <;> linarith
  · by_cases hia : i = a
    · subst hia
      have hj : j ∉ I := fun hh => lt_asymm hij (hmax j hh)
      rw [if_neg ha, if_neg hj]
      linarith
    · simpa [hja, hia] using h2

theorem deg_ind_up {N : ℕ} {μ : Fin N → ℝ} (hμ : IsHCParam μ) (Pr : Finset (Fin N) → Prop) (h0 : Pr ∅)
    (hs : ∀ I a, a ∉ I → IsHCParam (μ + epsI I) → IsHCParam (μ + epsI I + Pi.single a 1) → Pr I → Pr (insert a I)) :
    ∀ I, IsHCParam (μ + epsI I) → Pr I := by
  intro I
  induction I using Finset.induction_on_max with
  | empty => intro _; exact h0
  | insert a I hmax ih =>
    intro h'
    have ha : a ∉ I := fun hh => lt_irrefl _ (hmax a hh)
    have h1 := deg_hc_drop hμ I a hmax h'
    refine hs I a ha h1 ?_ (ih h1)
    rw [add_assoc, ← deg_epsI_insert I a ha]
    exact h'

theorem deg_fdeg_pos {N : ℕ} {μ : Fin N → ℝ} (h : IsHCParam μ) : 0 < fdegHC μ := by
  unfold fdegHC
  apply div_pos
  · exact Finset.prod_pos fun a _ => Finset.prod_pos fun b hb =>
      abs_pos.2 (sub_ne_zero.2 (h.1 (Finset.mem_filter.1 hb).2).ne')
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    have h1 : a.1 < b.1 := (Finset.mem_filter.1 hb).2
    have h2 : (a.1 : ℝ) < b.1 := by exact_mod_cast h1
    linarith

theorem deg_set_bound {N : ℕ} {μ : Fin N → ℝ} (hμ : IsHCParam μ) : ∀ I : Finset (Fin N), IsHCParam (μ + epsI I) →
    ((N : ℝ) ^ I.card)⁻¹ ≤ fdegHC (μ + epsI I) / fdegHC μ ∧ fdegHC (μ + epsI I) / fdegHC μ ≤ (N : ℝ) ^ I.card := by
  have h0 := deg_fdeg_pos hμ
  refine deg_ind_up hμ _ ?_ ?_
  · rw [deg_epsI_empty, add_zero, div_self h0.ne']
    simp
  · intro I a ha h1 h2 ih
    obtain ⟨ihl, ihu⟩ := ih
    have hr := Formalism.QuantumDeterminants.fdegRatio N (μ + epsI I) a h1.1.injective (deg_hc_diff h1) h2.1.injective
    have hb := (Formalism.HermitianLatticeCounting.Final.ExpansionTerms.degStepBound N (μ + epsI I) a h1.1.injective (deg_hc_diff h1)).1 h2.1.injective
    rw [← hr] at hb
    have hN : (0 : ℝ) < N := by
      have : 0 < N := lt_of_le_of_lt (Nat.zero_le _) a.2
      exact_mod_cast this
    have hp1 := deg_fdeg_pos h1
    have e : fdegHC (μ + epsI I + Pi.single a 1) / fdegHC μ =
        (fdegHC (μ + epsI I) / fdegHC μ) * (fdegHC (μ + epsI I + Pi.single a 1) / fdegHC (μ + epsI I)) := by
      field_simp
    rw [deg_epsI_insert I a ha, ← add_assoc, Finset.card_insert_of_notMem ha, pow_succ, e, mul_inv]
    have hq : 0 ≤ fdegHC (μ + epsI I) / fdegHC μ := (div_pos hp1 h0).le
    constructor
    · refine mul_le_mul ihl ?_ (by positivity) hq
      rw [← one_div]; exact hb.1
    · exact mul_le_mul ihu hb.2 (le_trans (by positivity) hb.1) (by positivity)

theorem deg_set_bound' {N : ℕ} {μ : Fin N → ℝ} (hμ : IsHCParam μ) (I : Finset (Fin N)) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (h' : IsHCParam (μ + s • epsI I)) :
    ((N : ℝ) ^ I.card)⁻¹ ≤ fdegHC (μ + s • epsI I) / fdegHC μ ∧ fdegHC (μ + s • epsI I) / fdegHC μ ≤ (N : ℝ) ^ I.card := by
  rcases hs with rfl | rfl
  · rw [one_smul] at h' ⊢
    exact deg_set_bound hμ I h'
  · have e : μ + (-1 : ℝ) • epsI I + epsI I = μ := by
      rw [neg_one_smul, neg_add_cancel_right]
    have h := deg_set_bound h' I (by rw [e]; exact hμ)
    rw [e] at h
    have h0 := deg_fdeg_pos hμ
    have h1 := deg_fdeg_pos h'
    have hx : 0 < fdegHC μ / fdegHC (μ + (-1 : ℝ) • epsI I) := div_pos h0 h1
    rw [← inv_div (fdegHC μ) (fdegHC (μ + (-1 : ℝ) • epsI I))]
    refine ⟨inv_anti₀ hx h.2, ?_⟩
    have h5 := inv_anti₀ (lt_of_lt_of_le (by
      have := hx
      exact inv_pos.2 (lt_of_lt_of_le hx h.2)) le_rfl) h.1
    rwa [inv_inv] at h5

def deg_VandLine (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A →
      ∀ (I : Finset (Fin (2 * D.R.rS + D.R.k + 1))) (s : ℝ), (s = 1 ∨ s = -1) →
        ∀ A' : LocS W, GoodS D (lam' + s • epsI I) A' →
          A'.deg / A.deg = fdegHC (lam' + s • epsI I) / fdegHC lam'

theorem deg_cast_r (D : D7) : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [dimS_eq]

theorem degree_ratio_one_of_vandermonde (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ)
    (h : deg_VandLine D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1) : DegreeRatioUnitShiftBound D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 1 := by
  intro hH τ w w' hTT θ hθ W hW lam' hl A hA I s hs A' hA'
  rw [h hH τ w w' hTT θ hθ W hW lam' hl A hA I s hs A' hA', one_mul, Real.rpow_natCast, ← deg_cast_r]
  exact (deg_set_bound' hA.1 I s hs hA'.1).2

section Fam

variable {eps : ℝ} (Fm : FamP eps)

def deg_VandLineF (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∀ Cn : ℝ, OwnEv Fm fun C' Cl x i => deg_VandLine (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
