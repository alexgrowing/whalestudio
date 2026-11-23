import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.CasselmanShalikaStandardVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

namespace GlobalTheory.CompanionTheory.GL2Factorization.WthCont

theorem WthR_continuous : ∀ n : ℤ, Continuous (GL2LocalData.WthR n) := by
  intro n
  have hv : Continuous fun g : GL (Fin 2) ℝ => (g.val : Matrix (Fin 2) (Fin 2) ℝ) :=
    Units.continuous_val
  have hent : ∀ i j, Continuous fun g : GL (Fin 2) ℝ => (g.val i j : ℝ) := fun i j =>
    hv.matrix_elem i j
  have hdet : Continuous fun g : GL (Fin 2) ℝ => (g.val).det := hv.matrix_det
  have hne : ∀ g : GL (Fin 2) ℝ, (g.val).det ≠ 0 := fun g =>
    (Matrix.isUnits_det_units g).ne_zero
  have hopen : IsOpen {g : GL (Fin 2) ℝ | 0 < (g.val).det} := isOpen_lt continuous_const hdet
  have hclosed : IsClosed {g : GL (Fin 2) ℝ | 0 < (g.val).det} := by
    have e : {g : GL (Fin 2) ℝ | 0 < (g.val).det} = {g : GL (Fin 2) ℝ | 0 ≤ (g.val).det} := by
      ext g
      simp only [Set.mem_setOf_eq]
      exact ⟨fun h => le_of_lt h, fun h => lt_of_le_of_ne h (hne g).symm⟩
    rw [e]
    exact isClosed_le continuous_const hdet
  have hc : ∀ i j, Continuous fun g : GL (Fin 2) ℝ => ((g.val i j : ℝ) : ℂ) := fun i j =>
    Complex.continuous_ofReal.comp (hent i j)
  have hq : Continuous fun g : GL (Fin 2) ℝ =>
      ((g.val 1 1 : ℂ) + Complex.I * (g.val 1 0 : ℂ)) :=
    (hc 1 1).add (continuous_const.mul (hc 1 0))
  have hp : Continuous fun g : GL (Fin 2) ℝ =>
      ((g.val 0 1 : ℂ) + Complex.I * (g.val 0 0 : ℂ)) :=
    (hc 0 1).add (continuous_const.mul (hc 0 0))
  have hq0 : ∀ g : GL (Fin 2) ℝ, ((g.val 1 1 : ℂ) + Complex.I * (g.val 1 0 : ℂ)) ≠ 0 := by
    intro g h0
    have h1 : (g.val 1 1 : ℝ) = 0 := by
      have := congrArg Complex.re h0
      simpa using this
    have h2 : (g.val 1 0 : ℝ) = 0 := by
      have := congrArg Complex.im h0
      simpa using this
    apply hne g
    rw [Matrix.det_fin_two, h1, h2]
    ring
  have hfun : GL2LocalData.WthR n = fun g : GL (Fin 2) ℝ =>
      if 0 < (g.val).det then
        (((g.val).det : ℝ) : ℂ) ^ (((n.natAbs + 1 : ℕ) : ℂ) / 2) *
          ((g.val 1 1 : ℂ) + Complex.I * (g.val 1 0 : ℂ)) ^ (-((n.natAbs + 1 : ℕ) : ℤ)) *
          Complex.exp (2 * Real.pi * Complex.I * (((g.val 0 1 : ℂ) + Complex.I * (g.val 0 0 : ℂ)) /
            ((g.val 1 1 : ℂ) + Complex.I * (g.val 1 0 : ℂ))))
      else 0 := rfl
  rw [hfun]
  refine continuous_if ?_ ?_ continuousOn_const
  · intro a ha
    have hcl : IsClopen {g : GL (Fin 2) ℝ | 0 < (g.val).det} := ⟨hclosed, hopen⟩
    rw [hcl.frontier_eq] at ha
    exact absurd ha (Set.notMem_empty a)
  · rw [hclosed.closure_eq]
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · refine ContinuousOn.cpow_const ?_ ?_
      · exact (Complex.continuous_ofReal.comp hdet).continuousOn
      · intro g hg
        exact Complex.ofReal_mem_slitPlane.mpr hg
    · exact (hq.zpow₀ _ (fun g => Or.inl (hq0 g))).continuousOn
    · exact (Complex.continuous_exp.comp
        (continuous_const.mul (hp.div hq hq0))).continuousOn

end GlobalTheory.CompanionTheory.GL2Factorization.WthCont
