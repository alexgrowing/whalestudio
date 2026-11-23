import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.GlobalTheory.GL3.LinkThetaStatementFamily
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.RCauchy

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.IsomTheta

theorem isTheta_eNat_comp : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → δ ≠ 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), S.d = D.host.d → (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → (∀ x y, JMB.hf S.Hm (e x) (e y) = Hf D B.tor x y) → S.IsTheta (fun z => B.eNat χ N N' L L' (e.symm z)) := by
  intro D cc δ B χ hcc hδ hχ h0 N N' L L' hA g S e hd hLa hH
  have hS : B.StdOK := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ
  have hmem := (B.vec_mem_ne hcc hδ h0 hS χ hχ N N' L L' hA).1
  have hQ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.rational_integrality_link D cc hcc δ hδ B N N' L L' hA
  simp only [Th, ThSp, Set.mem_setOf_eq] at hmem
  refine ⟨?_, ?_⟩
  · have hdiff : Differentiable ℂ (fun z => B.eNat χ N N' L L' (e.symm z)) :=
      hmem.1.comp e.symm.differentiable
    exact ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_differentiable hdiff
  · intro x hx
    have hx0 : e.symm x ∈ La D B.tor L L' := by
      rw [← hLa]; simpa using hx
    obtain ⟨m, hm⟩ := hQ _ hx0
    funext z
    have key := hmem.2 (e.symm x) hx0 (e.symm z)
    have h1 : JMB.hf S.Hm z x = Hf D B.tor (e.symm z) (e.symm x) := by
      simpa using hH (e.symm z) (e.symm x)
    have h2 : JMB.hf S.Hm x x = Hf D B.tor (e.symm x) (e.symm x) := by
      simpa using hH (e.symm x) (e.symm x)
    have hre : (JMB.beta S.d S.Hm x x).re = (m : ℝ) := by
      rw [JMB.beta, h2, hd, Complex.re_ofReal_mul]; exact hm
    have hal : al D B.tor (e.symm x) = (-1 : ℂ) ^ m := by
      rw [al, hm, round_intCast]
    have hph : Complex.exp ((Real.pi : ℂ) * Complex.I * (((JMB.beta S.d S.Hm x x).re : ℝ) : ℂ)) = (-1 : ℂ) ^ m := by
      rw [hre, show (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * ((Real.pi : ℂ) * Complex.I) by push_cast; ring,
        Complex.exp_int_mul, Complex.exp_pi_mul_I]
    show Complex.exp ((Real.pi : ℂ) * Complex.I * (((JMB.beta S.d S.Hm x x).re : ℝ) : ℂ)) *
        (B.eNat χ N N' L L' (e.symm (z + x)) *
          Complex.exp (-(Real.pi : ℂ) * JMB.hf S.Hm z x - (Real.pi : ℂ) / 2 * JMB.hf S.Hm x x)) =
      B.eNat χ N N' L L' (e.symm z)
    rw [← key, hph, ← hal, h1, h2, map_add]
    unfold U
    ring_nf

end GlobalTheory.IsomTheta
