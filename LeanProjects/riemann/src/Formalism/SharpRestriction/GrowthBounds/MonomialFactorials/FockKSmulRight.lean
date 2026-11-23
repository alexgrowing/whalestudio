import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BejjSmulLeft

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def GramWindow : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (n del h Y0 : ℕ) (E La0 : ℝ) (t0 : ℤ)
    (Ψ : ℕ → MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p]) (e : Fin n → MvPolynomial σ ℚ_[p])
    (s : ℕ → ℚ_[p]) (c : Fin n → Fin n → ℕ → ℚ_[p]) (lead : ℚ_[p]) (roots : Multiset ℚ_[p]),
    LinearIndependent ℤ_[p] e →
    (∀ j (a : ℚ_[p]) u v, Ψ j (a • u) v = a * Ψ j u v) → (∀ j u u' v, Ψ j (u + u') v = Ψ j u v + Ψ j u' v) →
    (∀ j (a : ℚ_[p]) u v, Ψ j u (a • v) = a * Ψ j u v) → (∀ j u v v', Ψ j u (v + v') = Ψ j u v + Ψ j u v') →
    0 < Y0 → Y0 ≤ p ^ h → del + 1 ≤ p ^ h → 1 ≤ E → lead ≠ 0 → (∀ a b k, ‖c a b k‖ ≤ 1) →
    (Formalism.GM.binMatK ℚ_[p] del c).det =
      Polynomial.C lead * (roots.map (fun ζ => Polynomial.X - Polynomial.C ζ)).prod →
    -Real.logb p ‖lead‖ + (roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n : ℝ) * La0 →
    (∀ j ∈ Finset.range Y0, s j ≠ 0 ∧ ‖s j‖ ≤ 1 ∧ ∀ a b,
      s j * Ψ j (e a) (e b) =
        ((Formalism.GM.binMatK ℚ_[p] del c).map (Polynomial.eval ((t0 + (j : ℤ) : ℤ) : ℚ_[p]))) a b) →
    (∑ j ∈ Finset.range Y0, (Formalism.GM.M.bad p (Ψ j) (Submodule.span ℤ_[p] (Set.range e)) (⌈E⌉ - 1) : ℝ)) ≤
      (Y0 : ℝ) * ((n : ℝ) * ((del : ℝ) / Y0 + (La0 + (del : ℝ) * h / Y0) / E))

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestWinInst (CM : ℝ) : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    ∀ (n₁ : ℕ) (e : Fin n₁ → MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop 0 x.1).T.t) ℚ_[X.p]),
      (∀ a, e a ∈ Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) → LinearIndependent ℤ_[X.p] e →
      (∀ a b, a ≠ b → bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e b) = 0) →
      (∀ a, bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e a) ≠ 0 ∧
        (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 (e a) (e a)).valuation ≤
          ⌊D1r C0 CE1 CE2 X CM⌋) →
      ∃ (del h : ℕ) (La0 : ℝ) (t0 : ℤ) (s : ℕ → ℚ_[X.p]) (c : Fin n₁ → Fin n₁ → ℕ → ℚ_[X.p]) (lead : ℚ_[X.p])
        (roots : Multiset ℚ_[X.p]),
        X.winA.card ≤ X.p ^ h ∧ del + 1 ≤ X.p ^ h ∧ lead ≠ 0 ∧ (∀ a b k, ‖c a b k‖ ≤ 1) ∧
        (Formalism.GM.binMatK ℚ_[X.p] del c).det =
          Polynomial.C lead * (roots.map (fun ζ => Polynomial.X - Polynomial.C ζ)).prod ∧
        -Real.logb X.p ‖lead‖ + (roots.card : ℝ) / ((X.p : ℝ) - 1) ≤ (n₁ : ℝ) * La0 ∧
        (∀ j ∈ Finset.range X.winA.card, s j ≠ 0 ∧ ‖s j‖ ≤ 1 ∧ ∀ a b,
          s j * bejj X.p (r := X.r) (gB C0 CE1 CE2 X aTop (X.L.a + j) x.1) x.2.1 x.2.2 (e a) (e b) =
            ((Formalism.GM.binMatK ℚ_[X.p] del c).map (Polynomial.eval ((t0 + (j : ℤ) : ℤ) : ℚ_[X.p]))) a b) ∧
        (X.winA.card : ℝ) * ((n₁ : ℝ) * ((del : ℝ) / X.winA.card +
          (La0 + (del : ℝ) * h / X.winA.card) / ((⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ) + 1))) ≤
          (X.winA.card : ℝ) * (5 / X.L.Y * n₁)

end Formalism.MainNotions.G.SymmetricFormBlocks

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem winA_sum (X : flipOneThree.Inst) (f : ℕ → ℝ) :
    ∑ aPlus ∈ X.winA, f aPlus = ∑ j ∈ Finset.range X.winA.card, f (X.L.a + j) := by
  unfold flipOneThree.Inst.winA
  rw [Nat.card_Icc, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

end Formalism.MainNotions.G.SymmetricFormBlocks

end
