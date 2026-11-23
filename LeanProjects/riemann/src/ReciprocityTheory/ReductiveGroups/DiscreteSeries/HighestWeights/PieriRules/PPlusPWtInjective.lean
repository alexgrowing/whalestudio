import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem pPlus_fst_ne_snd {ε : Fin n → Bool} {β : Bool} (p : pIdx ε β) : p.1.1 ≠ p.1.2 := by
  intro h
  obtain ⟨h1, h2⟩ := p.2
  rw [h] at h1
  rw [h1] at h2
  cases β <;> simp at h2

theorem pPlus_pAdM_diag (ε : Fin n → Bool) (β : Bool) (a : Fin n) :
    pAdM ε β a a = Matrix.diagonal fun p => ((pWt ε β p a : ℝ) : ℂ) := by
  ext p q
  by_cases hpq : p = q
  · subst hpq
    simp only [pAdM, pWt, Pi.single_apply, Pi.sub_apply, Matrix.diagonal_apply_eq, and_true, and_self]
    by_cases h1 : p.1.1 = a <;> by_cases h2 : p.1.2 = a
    · exact absurd (h1.trans h2.symm) (pPlus_fst_ne_snd p)
    · rw [if_pos h1, if_neg h2, if_pos h1.symm, if_neg (Ne.symm h2)]; simp
    · rw [if_neg h1, if_pos h2, if_neg (Ne.symm h1), if_pos h2.symm]; simp
    · rw [if_neg h1, if_neg h2, if_neg (Ne.symm h1), if_neg (Ne.symm h2)]; simp
  · rw [Matrix.diagonal_apply_ne _ hpq]
    have h1 : ¬ (p.1.1 = a ∧ q.1.1 = a ∧ p.1.2 = q.1.2) := fun h =>
      hpq (Subtype.ext (Prod.ext (h.1.trans h.2.1.symm) h.2.2))
    have h2 : ¬ (q.1.2 = a ∧ p.1.2 = a ∧ p.1.1 = q.1.1) := fun h =>
      hpq (Subtype.ext (Prod.ext h.2.2 (h.2.1.trans h.1.symm)))
    simp only [pAdM, if_neg h1, if_neg h2, sub_self]

theorem pPlus_pWt_injective (ε : Fin n → Bool) (β : Bool) : Function.Injective (pWt ε β) := by
  intro p q h
  have hp := pPlus_fst_ne_snd p
  have e1 := congrFun h p.1.1
  have e2 := congrFun h p.1.2
  simp only [pWt, Pi.sub_apply, Pi.single_apply] at e1 e2
  rw [if_pos trivial, if_neg hp] at e1
  rw [if_neg (Ne.symm hp), if_pos trivial] at e2
  have h1 : p.1.1 = q.1.1 := by
    by_contra hne
    rw [if_neg hne] at e1
    split_ifs at e1 <;> norm_num at e1
  have h2 : p.1.2 = q.1.2 := by
    by_contra hne
    rw [if_neg hne] at e2
    split_ifs at e2 <;> norm_num at e2
  exact Subtype.ext (Prod.ext h1 h2)

theorem pPlus_card_eq_one (ε : Fin n → Bool) (β : Bool) (Λ : Fin n → ℝ) (p : pIdx ε β) :
    Nat.card {q : pIdx ε β // Λ + pWt ε β p = Λ + pWt ε β q} = 1 :=
  Nat.card_eq_one_iff_exists.mpr
    ⟨⟨p, rfl⟩, fun q => Subtype.ext (pPlus_pWt_injective ε β (add_left_cancel q.2).symm)⟩

theorem pPlus_of_parts (hcount : PieriCountStatement) (htens : TensHWStatement)
    (hkt : KTypeIntDomStatement) (hws : WeylSumPStatement)
    (hρ : ∀ (n : ℕ) (ε : Fin n → Bool) (β : Bool),
      ∃ (ρ : KG ε →* unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ))
        (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (pIdx ε β) (pIdx ε β) ℂ),
        Continuous (fun k : KG ε =>
          ((ρ k : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ)) ∧
        (∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
          ∀ i j, HasDerivAt (fun t : ℝ =>
            ((ρ (γ t) : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ) i j)
            (dρ X i j) 0) ∧
        ∀ a b, dρ (Matrix.single a b 1) = pAdM ε β a b)
    (hrel : ∀ (n : ℕ) (ε : Fin n → Bool) (β : Bool), Formalism.REAL.KRel ε (pAdM ε β)) :
    PPlusStatement := by
  intro n ε β Λ T
  obtain ⟨ρ, dρ, hcont, hder, hsingle⟩ := hρ n ε β
  have hfun : (fun a b => dρ (Matrix.single a b 1)) = pAdM ε β := by
    funext a b
    exact hsingle a b
  obtain ⟨hint, hdom⟩ := hkt n ε Λ T
  obtain ⟨hsum, hvan⟩ := hws n ε β Λ hint hdom
  have hc := hcount n ε Λ T (pIdx ε β) ρ dρ (pWt ε β) hcont hder
    (by rw [hfun]; exact hrel n ε β)
    (fun a => by rw [hsingle]; exact pPlus_pAdM_diag ε β a) (pPlus_pWt_injective ε β)
    (by rw [hsum, Nat.card_eq_fintype_card]) hvan
  rw [hfun] at hc
  obtain ⟨hexist, hall⟩ := hc
  have ht := htens T.V n ε (kunits T) Λ T.w (pIdx ε β) (pAdM ε β) (pWt ε β) (KType.kRel T) (KType.kUnit T)
    (KType.kHighest_w T) (KType.kSpan_eq_top T) (hrel n ε β) (pPlus_pAdM_diag ε β)
  refine ⟨hall, fun p => ?_, hexist⟩
  calc Module.finrank ℂ (khwSub ε (tensAct (kunits T) (pAdM ε β)) (Λ + pWt ε β p))
      ≤ Nat.card {q : pIdx ε β // Λ + pWt ε β p = Λ + pWt ε β q} := (ht.2 _).2
    _ = 1 := pPlus_card_eq_one ε β Λ p

end ReciprocityTheory.ChartRestriction.DS.HW
