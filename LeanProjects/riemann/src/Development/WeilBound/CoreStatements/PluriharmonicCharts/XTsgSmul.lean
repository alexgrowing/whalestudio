import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.tsg_smul

theorem toWt_inj (Ψ : Type) (N : ℕ) :
    Function.Injective (toWt : MvPolynomial (Ψ × Fin N) ℝ → MvPolynomial (Ψ × Fin N) ℝ) := by
  classical
  let S : Ψ × Fin N → MvPolynomial (Ψ × Fin N) ℝ := fun p => ∑ k ∈ Finset.Ici p.2, X (p.1, k)
  have key : ∀ p, aeval S (gapX p) = X p := by
    intro p
    obtain ⟨a, i⟩ := p
    have h1 : Finset.Ici i = insert i (Finset.Ioi i) := (Finset.Ioi_insert i).symm
    simp only [gapX]
    split_ifs with h
    · have h2 : Finset.Ioi i = Finset.Ici (⟨i.1 + 1, h⟩ : Fin N) := by
        ext k
        simp only [Finset.mem_Ioi, Finset.mem_Ici, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Fin.val_mk]
        omega
      have hn : i ∉ Finset.Ici (⟨i.1 + 1, h⟩ : Fin N) := by
        simp only [Finset.mem_Ici, Fin.le_iff_val_le_val, Fin.val_mk]
        omega
      simp only [S, map_sub, aeval_X, h1, h2]
      rw [Finset.sum_insert hn]
      ring
    · have h2 : Finset.Ioi i = ∅ := by
        ext k
        constructor
        · intro hk
          rw [Finset.mem_Ioi, Fin.lt_iff_val_lt_val] at hk
          have := k.isLt
          exfalso
          omega
        · intro hk
          simp at hk
      simp only [S, map_sub, map_zero, aeval_X, h1, h2, sub_zero]
      simp
  have hcomp : (aeval S).comp (toWt : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] _) = AlgHom.id ℝ _ := by
    apply MvPolynomial.algHom_ext
    intro p
    rw [AlgHom.comp_apply, AlgHom.id_apply]
    show aeval S (aeval gapX (X p)) = X p
    rw [aeval_X, key]
  have e : ∀ q, aeval S (toWt q) = q := fun q => by
    simpa using AlgHom.congr_fun hcomp q
  intro f g hfg
  rw [← e f, ← e g, hfg]

end PositivityTheory.Xgp.tsg_smul

theorem PositivityTheory.Xgp.t_tsg_smul : (∀ (D : ℕ) (κ : ℕ → ℝ) (v : ℝ) (Q : Polynomial ℝ), tsgPoly D κ (Polynomial.C v * Q) = Polynomial.C v * tsgPoly D κ Q) ∧ (∀ (σ : Type) (c : σ → ℝ) (e : σ → ℤ) (v : ℝ) (Q : MvPolynomial σ ℝ), linePoly c e (C v * Q) = Polynomial.C v * linePoly c e Q) ∧ ∀ (Ψ : Type) (N : ℕ), Function.Injective (toWt : MvPolynomial (Ψ × Fin N) ℝ → MvPolynomial (Ψ × Fin N) ℝ) := by
  refine ⟨?_, ?_, fun Ψ N => PositivityTheory.Xgp.tsg_smul.toWt_inj Ψ N⟩
  · intro D κ v Q
    by_cases hv : v = 0
    · subst hv
      simp [tsgPoly]
    · simp only [tsgPoly, Polynomial.natDegree_C_mul hv, Polynomial.coeff_C_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs
      · simp only [Polynomial.C_mul]
        ring
      · simp
  · intro σ c e v Q
    simp [linePoly, Polynomial.algebraMap_eq]
