import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem satEig_rev_of_stable {q n : ℕ} {B : Multiset ℂˣ} (hB : B.card = n) (hs : inv B = B)
    (i : Fin (n + 1)) : satEig q n B (i.rev : ℕ) = satEig q n B n * satEig q n B (i : ℕ) := by
  have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
  have h := GlobalTheory.LFun.ConjPlace.satEig_inv_mul (q := q) hB hi
  have hs' : B.map (·⁻¹) = B := hs
  rw [hs'] at h
  have hr : (i.rev : ℕ) = n - (i : ℕ) := by
    rw [Fin.val_rev]; omega
  rw [hr, ← h, mul_comm]

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.hecke_eigenvalues_unitary_one_factor :
    EvaluationAtUnitaryOne := by
  intro E _ _ _ w a b e he B₁ B₂ h₁ h₂ s₁ s₂
  induction he with
  | one => simp [ev2, Ex.ev]
  | step c p =>
    have r₁ := satEig_rev_of_stable (q := qV E w) h₁ s₁ p.1
    have r₂ := satEig_rev_of_stable (q := qV E w) h₂ s₂ p.2
    simp only [ev2, Ex.ev, dEx, Fin.val_last, r₁, r₂]
    ring
  | mul _ _ ih₁ ih₂ =>
    simp only [ev2, Ex.ev] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂, one_mul]
