import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Dy

section Steps

variable {Ψ : Type} {p q : ℕ}

theorem blkF_ne_inl (K₀ : Type) (r : Ψ × Fin (p + q)) (k : K₀) : blkF Ψ p q K₀ r ≠ some (.inl k) := by
  delta blkF
  split_ifs <;> simp

theorem blkF_eq_inr (K₀ : Type) (r : Ψ × Fin (p + q)) (t : StepIx Ψ p q) :
    blkF Ψ p q K₀ r = some (.inr t) ↔ IsProperStep (p + q) p r.2 ∧ stepOf Ψ p q r = t := by
  delta blkF
  split_ifs with hp <;> simp [hp]

theorem stepOf_eq_left (τ τ' : Ψ) (i : Fin (p + q)) (a : Fin (rk Ψ p q (.inl τ'))) :
    stepOf Ψ p q (τ, i) = ⟨.inl τ', a⟩ ↔ τ = τ' ∧ (i : ℕ) = a := by
  delta stepOf
  dsimp only
  split_ifs with hi
  · constructor
    · intro e
      rcases Sigma.mk.inj_iff.mp e with ⟨h1, h2⟩
      cases h1
      exact ⟨rfl, congrArg Fin.val (eq_of_heq h2)⟩
    · rintro ⟨rfl, h2⟩
      exact Sigma.ext rfl (heq_of_eq (Fin.ext h2))
  · constructor
    · intro e
      exact absurd (Sigma.mk.inj_iff.mp e).1 Sum.inr_ne_inl
    · rintro ⟨-, h2⟩
      have ha : (a : ℕ) < p := a.2
      exfalso
      omega

theorem stepOf_eq_right (τ τ' : Ψ) (i : Fin (p + q)) (a : Fin (rk Ψ p q (.inr τ'))) :
    stepOf Ψ p q (τ, i) = ⟨.inr τ', a⟩ ↔ τ = τ' ∧ (i : ℕ) = p + a := by
  delta stepOf
  dsimp only
  split_ifs with hi
  · constructor
    · intro e
      exact absurd (Sigma.mk.inj_iff.mp e).1 Sum.inl_ne_inr
    · rintro ⟨-, h2⟩
      exfalso
      omega
  · constructor
    · intro e
      rcases Sigma.mk.inj_iff.mp e with ⟨h1, h2⟩
      cases h1
      have h3 : (i : ℕ) - p = a := congrArg Fin.val (eq_of_heq h2)
      exact ⟨rfl, by omega⟩
    · rintro ⟨rfl, h2⟩
      exact Sigma.ext rfl (heq_of_eq (Fin.ext (show (i : ℕ) - p = a by omega)))

end Steps

section Main

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {n : Ψ ⊕ Ψ → ℕ}
  {A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω}
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] {x₀ : (Σ k, J₀ k) → Ω} {m : Ψ ⊕ Ψ → ℕ}

open Classical in

theorem dy_apply (h : ModelOK A x₀ m) (r : Ψ × Fin (p + q)) (k : K₀ ⊕ StepIx Ψ p q) :
    (model A x₀ m h).dy r k =
      if ∀ r', blkF Ψ p q K₀ r' ≠ some k then -twist m r k else if blkF Ψ p q K₀ r = some k then 1 else 0 := by
  delta FlagModel.dy
  by_cases hc : ∀ p', (model A x₀ m h).blk p' ≠ some k
  · rw [dif_pos hc, if_pos (show ∀ r' : Ψ × Fin (p + q), blkF Ψ p q K₀ r' ≠ some k from hc)]
    rfl
  · rw [dif_neg hc, if_neg (show ¬ ∀ r' : Ψ × Fin (p + q), blkF Ψ p q K₀ r' ≠ some k from hc)]
    by_cases hb : (model A x₀ m h).blk r = some k
    · rw [if_pos hb, if_pos (show blkF Ψ p q K₀ r = some k from hb)]
    · rw [if_neg hb, if_neg (show ¬ blkF Ψ p q K₀ r = some k from hb)]

open Classical in

theorem twist_left (τ τ' : Ψ) (i : Fin (p + q)) (a : Fin (rk Ψ p q (.inl τ'))) (ha : (a : ℕ) + 1 = p) :
    twist (K₀ := K₀) m (τ, i) (.inr ⟨.inl τ', a⟩) = -(if τ' = τ ∧ p ≤ (i : ℕ) + 1 then 1 else 0) := by
  delta twist
  dsimp only
  rw [if_neg (show ¬ ((Sum.inl τ' : Ψ ⊕ Ψ) = Sum.inr τ ∧ (a : ℕ) + 1 = q ∧ (i : ℕ) + 1 = p + q) from fun hh => Sum.inl_ne_inr hh.1), add_zero]
  by_cases hc : τ' = τ ∧ p ≤ (i : ℕ) + 1
  · rw [if_pos (show (Sum.inl τ' : Ψ ⊕ Ψ) = Sum.inl τ ∧ (a : ℕ) + 1 = p ∧ p ≤ (i : ℕ) + 1 from ⟨congrArg Sum.inl hc.1, ha, hc.2⟩), if_pos hc]
  · rw [if_neg (show ¬ ((Sum.inl τ' : Ψ ⊕ Ψ) = Sum.inl τ ∧ (a : ℕ) + 1 = p ∧ p ≤ (i : ℕ) + 1) from fun hh => hc ⟨Sum.inl_injective hh.1, hh.2.2⟩), if_neg hc]

open Classical in

theorem twist_right (τ τ' : Ψ) (i : Fin (p + q)) (a : Fin (rk Ψ p q (.inr τ'))) (ha : (a : ℕ) + 1 = q) :
    twist (K₀ := K₀) m (τ, i) (.inr ⟨.inr τ', a⟩) = -(if τ' = τ ∧ (i : ℕ) + 1 = p + q then 1 else 0) := by
  delta twist
  dsimp only
  rw [if_neg (show ¬ ((Sum.inr τ' : Ψ ⊕ Ψ) = Sum.inl τ ∧ (a : ℕ) + 1 = p ∧ p ≤ (i : ℕ) + 1) from fun hh => Sum.inr_ne_inl hh.1), zero_add]
  by_cases hc : τ' = τ ∧ (i : ℕ) + 1 = p + q
  · rw [if_pos (show (Sum.inr τ' : Ψ ⊕ Ψ) = Sum.inr τ ∧ (a : ℕ) + 1 = q ∧ (i : ℕ) + 1 = p + q from ⟨congrArg Sum.inr hc.1, ha, hc.2⟩), if_pos hc]
  · rw [if_neg (show ¬ ((Sum.inr τ' : Ψ ⊕ Ψ) = Sum.inr τ ∧ (a : ℕ) + 1 = q ∧ (i : ℕ) + 1 = p + q) from fun hh => hc ⟨Sum.inr_injective hh.1, hh.2.2⟩), if_neg hc]

open Classical in

theorem dy_left (h : ModelOK A x₀ m) (τ τ' : Ψ) (i : Fin (p + q)) (a : Fin (rk Ψ p q (.inl τ'))) :
    (model A x₀ m h).dy (τ, i) (.inr ⟨.inl τ', a⟩) =
      if τ = τ' ∧ ((i : ℕ) = a ∨ ((a : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) then 1 else 0 := by
  have ha : (a : ℕ) < p := a.2
  have key : ∀ r' : Ψ × Fin (p + q), blkF Ψ p q K₀ r' = some (.inr ⟨.inl τ', a⟩) ↔
      r'.1 = τ' ∧ (r'.2 : ℕ) = a ∧ (a : ℕ) + 1 ≠ p := by
    rintro ⟨σ', j⟩
    rw [blkF_eq_inr, stepOf_eq_left]
    dsimp only
    delta IsProperStep
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h3, h4, by omega⟩
    · rintro ⟨h3, h4, h5⟩
      exact ⟨⟨by omega, by omega⟩, h3, h4⟩
  by_cases hp : (a : ℕ) + 1 = p
  · rw [dy_apply h, if_pos (fun r' e => ((key r').1 e).2.2 hp), twist_left τ τ' i a hp, neg_neg]
    rcases eq_or_ne τ' τ with rfl | hne
    · simp only [eq_self_iff_true, true_and]
      split_ifs <;> omega
    · simp [hne, hne.symm]
  · rw [dy_apply h, if_neg (fun H => H (τ', ⟨(a : ℕ), by omega⟩) ((key _).2 ⟨rfl, rfl, hp⟩))]
    simp only [key]
    rcases eq_or_ne τ τ' with rfl | hne
    · simp only [eq_self_iff_true, true_and]
      split_ifs <;> omega
    · simp [hne]

open Classical in

theorem dy_right (h : ModelOK A x₀ m) (τ τ' : Ψ) (i : Fin (p + q)) (a : Fin (rk Ψ p q (.inr τ'))) :
    (model A x₀ m h).dy (τ, i) (.inr ⟨.inr τ', a⟩) = if τ = τ' ∧ (i : ℕ) = p + a then 1 else 0 := by
  have ha : (a : ℕ) < q := a.2
  have key : ∀ r' : Ψ × Fin (p + q), blkF Ψ p q K₀ r' = some (.inr ⟨.inr τ', a⟩) ↔
      r'.1 = τ' ∧ (r'.2 : ℕ) = p + a ∧ (a : ℕ) + 1 ≠ q := by
    rintro ⟨σ', j⟩
    rw [blkF_eq_inr, stepOf_eq_right]
    dsimp only
    delta IsProperStep
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h3, h4, by omega⟩
    · rintro ⟨h3, h4, h5⟩
      exact ⟨⟨by omega, by omega⟩, h3, h4⟩
  by_cases hq : (a : ℕ) + 1 = q
  · rw [dy_apply h, if_pos (fun r' e => ((key r').1 e).2.2 hq), twist_right τ τ' i a hq, neg_neg]
    rcases eq_or_ne τ' τ with rfl | hne
    · simp only [eq_self_iff_true, true_and]
      split_ifs <;> omega
    · simp [hne, hne.symm]
  · rw [dy_apply h, if_neg (fun H => H (τ', ⟨p + (a : ℕ), by omega⟩) ((key _).2 ⟨rfl, rfl, hq⟩))]
    simp only [key]
    rcases eq_or_ne τ τ' with rfl | hne
    · simp only [eq_self_iff_true, true_and]
      split_ifs <;> omega
    · simp [hne]

end Main

open Classical in

theorem dy_flag : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ) (h : ModelOK A x₀ m) (τ : Ψ) (i : Fin (p + q)), (∀ k, (model A x₀ m h).dy (τ, i) (.inl k) = -((rkW i * m (.inl τ) + rkO i * m (.inr τ) : ℕ) : ℤ)) ∧ ∀ t : StepIx Ψ p q, ((t = stepOf Ψ p q (τ, i) ∨ (t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) → (model A x₀ m h).dy (τ, i) (.inr t) = 1) ∧ (¬ (t = stepOf Ψ p q (τ, i) ∨ (t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) → (model A x₀ m h).dy (τ, i) (.inr t) = 0) := by
  intro Ψ _ p q Ω _ _ n A K₀ _ J₀ _ x₀ m h τ i
  refine ⟨fun k => ?_, fun t => ?_⟩
  · rw [dy_apply h, if_pos (fun r' => blkF_ne_inl K₀ r' k)]
    rfl
  · obtain ⟨s, a⟩ := t
    cases s with
    | inl τ' =>
      have e := (eq_comm.trans (stepOf_eq_left τ τ' i a) :
        (⟨.inl τ', a⟩ : StepIx Ψ p q) = stepOf Ψ p q (τ, i) ↔ _)
      have hc : ((⟨.inl τ', a⟩ : StepIx Ψ p q) = stepOf Ψ p q (τ, i) ∨
          ((Sum.inl τ' : Ψ ⊕ Ψ) = .inl τ ∧ (a : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) ↔
          (τ = τ' ∧ ((i : ℕ) = a ∨ ((a : ℕ) + 1 = p ∧ p ≤ (i : ℕ)))) := by
        rw [e, Sum.inl.injEq]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
          · exact ⟨h1, Or.inl h2⟩
          · exact ⟨h1.symm, Or.inr ⟨h2, h3⟩⟩
        · rintro ⟨h1, h2 | ⟨h2, h3⟩⟩
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1.symm, h2, h3⟩
      refine ⟨fun hc' => ?_, fun hn => ?_⟩
      · rw [dy_left h, if_pos (hc.1 hc')]
      · rw [dy_left h, if_neg (fun h' => hn (hc.2 h'))]
    | inr τ' =>
      have e := (eq_comm.trans (stepOf_eq_right τ τ' i a) :
        (⟨.inr τ', a⟩ : StepIx Ψ p q) = stepOf Ψ p q (τ, i) ↔ _)
      have hc : ((⟨.inr τ', a⟩ : StepIx Ψ p q) = stepOf Ψ p q (τ, i) ∨
          ((Sum.inr τ' : Ψ ⊕ Ψ) = .inl τ ∧ (a : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) ↔
          (τ = τ' ∧ (i : ℕ) = p + a) := by
        rw [e]
        constructor
        · rintro (h1 | ⟨h1, -⟩)
          · exact h1
          · exact absurd h1 Sum.inr_ne_inl
        · intro h1
          exact Or.inl h1
      refine ⟨fun hc' => ?_, fun hn => ?_⟩
      · rw [dy_right h, if_pos (hc.1 hc')]
      · rw [dy_right h, if_neg (fun h' => hn (hc.2 h'))]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Dy
