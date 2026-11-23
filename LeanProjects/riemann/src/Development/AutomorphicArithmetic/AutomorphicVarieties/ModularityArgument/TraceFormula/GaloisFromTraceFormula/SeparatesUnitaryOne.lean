import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem inv_eq_of_eig {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) {n : ℕ}
    {B : Multiset ℂˣ} (hB : B.card = n)
    (h : ∀ i ≤ n, satEig (qV E w) n B n * satEig (qV E w) n B i = satEig (qV E w) n B (n - i)) :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.inv B = B := by
  have hne : satEig (qV E w) n B n ≠ 0 := GlobalTheory.LFun.SatCompare.satEig_self_ne_zero hB
  have hI : (UpperTheory.V.Z.Tf.GlobalTraceComparison.inv B).card = n := by simpa [UpperTheory.V.Z.Tf.GlobalTraceComparison.inv] using hB
  refine eq_of_satEig_eq (qV_ne_zero w) hI hB fun j hj => ?_
  have e := GlobalTheory.LFun.ConjPlace.satEig_inv_mul (q := qV E w) hB hj
  rw [← h j hj, mul_comm] at e
  exact mul_left_cancel₀ hne e

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.unitary_one_characters_separated_by_eigenvalues :
    SeparatesUnitaryOne := by
  intro E _ _ _ w a b B₁ B₂ h₁ h₂ hns
  by_cases hz : ∀ p : Fin (a + 1) × Fin (b + 1), ev2 a b w (dEx p) B₁ B₂ = 0
  · exfalso
    have hs₁ : satEig (qV E w) a B₁ a ≠ 0 := GlobalTheory.LFun.SatCompare.satEig_self_ne_zero h₁
    have hs₂ : satEig (qV E w) b B₂ b ≠ 0 := GlobalTheory.LFun.SatCompare.satEig_self_ne_zero h₂
    have key : ∀ p : Fin (a + 1) × Fin (b + 1),
        satEig (qV E w) a B₁ a * satEig (qV E w) b B₂ b *
            (satEig (qV E w) a B₁ p.1 * satEig (qV E w) b B₂ p.2) =
          satEig (qV E w) a B₁ (a - p.1) * satEig (qV E w) b B₂ (b - p.2) := by
      intro p
      have := hz p
      simp only [ev2, dEx, Ex.ev, Fin.val_last, Fin.val_rev] at this
      have e₁ : a + 1 - ((p.1 : ℕ) + 1) = a - p.1 := by omega
      have e₂ : b + 1 - ((p.2 : ℕ) + 1) = b - p.2 := by omega
      rw [e₁, e₂] at this
      linear_combination this
    refine hns ⟨inv_eq_of_eig w h₁ fun i hi => ?_, inv_eq_of_eig w h₂ fun j hj => ?_⟩
    · have := key (⟨i, Nat.lt_succ_of_le hi⟩, 0)
      simp only [Fin.val_zero, GlobalTheory.LFun.ConjPlace.satEig_zero, mul_one, Nat.sub_zero] at this
      refine mul_right_cancel₀ hs₂ ?_
      linear_combination this
    · have := key (0, ⟨j, Nat.lt_succ_of_le hj⟩)
      simp only [Fin.val_zero, GlobalTheory.LFun.ConjPlace.satEig_zero, one_mul, Nat.sub_zero] at this
      refine mul_left_cancel₀ hs₁ ?_
      linear_combination this
  · push_neg at hz
    obtain ⟨p, hp⟩ := hz
    refine ⟨_, U1.step (-(ev2 a b w (dEx p) B₁ B₂)⁻¹) p, ?_⟩
    have e : ev2 a b w (Ex.add Ex.one (Ex.smul (-(ev2 a b w (dEx p) B₁ B₂)⁻¹) (dEx p))) B₁ B₂ =
        1 + -(ev2 a b w (dEx p) B₁ B₂)⁻¹ * ev2 a b w (dEx p) B₁ B₂ := rfl
    rw [e, neg_mul, inv_mul_cancel₀ hp]
    ring
