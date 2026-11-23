import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.normIff :
    UpperTheory.ConvolutionTheory.Dp.NormIff := by
  intro E _ _ _ n π
  constructor
  · intro h ψ hψ
    refine mem_centralCuspForms.2 fun s x => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact congrArg ψ.1 (Subsingleton.elim _ _)
    · have hc : ((n : ℝ) * Module.finrank ℚ E) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.2 hn.ne') (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
      have hs : (⟨Real.exp (n * Module.finrank ℚ E * (Real.log s.1 / (n * Module.finrank ℚ E))), Real.exp_pos _⟩ :
          {r : ℝ // 0 < r}) = s := Subtype.ext (by
        change Real.exp _ = s.1
        rw [mul_div_cancel₀ _ hc, Real.exp_log s.2])
      have e := UpperTheory.V.KernelIndexFullLattice.splitEq_holds E n (Real.log s.1 / (n * Module.finrank ℚ E))
      rw [hs] at e
      have key := h (Cm.ofCusp E n ψ) hψ (Real.log s.1 / (n * Module.finrank ℚ E)) x
      rw [e] at key
      exact key
  · intro h φ hφ t g
    have hφ' : φ ∈ (Cm.carrier π).map (Cm.ofCusp E n) := by
      rw [Cm.map_carrier]; exact hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ'
    rw [UpperTheory.V.KernelIndexFullLattice.splitEq_holds E n t]
    exact h hψ _ g
