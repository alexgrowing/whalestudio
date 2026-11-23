import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CasselmanWallachOfHyp

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace

namespace PositivityTheory.CW

namespace DerivativeContinuity

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem continuousOn_Dw (hU : IsURepOn (UJset ε) σ) (hI : IsIrredOn (UJset ε) σ) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) :
    ContinuousOn (fun g => Dw σ l (σ g w)) (UJset ε) :=
  continuousOn_iff_continuous_restrict.2
    (continuous_word_orbit (isUnit_Jm ε) hU (GlobalTheory.CWGeneral.dense_smoothAll_of_irred hU hI) continuous_subtype_val
      (fun t => t.2) l hl hw)

theorem hasDerivAt_Dw (hU : IsURepOn (UJset ε) σ) (hI : IsIrredOn (UJset ε) σ) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) {X : Mx n} (hX : X ∈ lieSet ε) :
    HasDerivAt (fun t : ℝ => Dw σ l (σ (NormedSpace.exp (t • X)) w)) (Dw σ l (dRep σ X w)) 0 := by
  have hden : Dense (smooth (Jm ε) σ : Set H) :=
    (GlobalTheory.CWGeneral.dense_smoothAll_of_irred hU hI).mono (smoothAll_le (isUnit_Jm ε))
  have hw' : Sm ε σ (dRep σ X w) := dRep_mem (isUnit_Jm ε) hU hw hX
  have hc : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) →
      Continuous fun t : ℝ => Dw σ l (σ (NormedSpace.exp (t • X)) (dRep σ X w)) := fun l hl =>
    (continuousOn_Dw hU hI hl hw').comp_continuous (continuous_exp_smul X) (exp_mem_UJ hX)
  have e0 : ∀ z, σ (NormedSpace.exp ((0 : ℝ) • X)) z = z := fun z => by
    rw [zero_smul, NormedSpace.exp_zero, sigma_one hU]
  have key : ∀ t : ℝ, Dw σ l (σ (NormedSpace.exp (t • X)) w) =
      Dw σ l w + ∫ s in (0 : ℝ)..t, Dw σ l (σ (NormedSpace.exp (s • X)) (dRep σ X w)) := by
    intro t
    have h0 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
      (fun s _ => hasDerivAt_orbit hU hw hX s) ((hc [] (by simp)).intervalIntegrable 0 t)
    rw [e0] at h0
    refine hden.eq_of_inner_right ℂ fun y hy => ?_
    have i1 := fun (z : H) (l : List (Mx n)) (hl : ∀ X ∈ l, X ∈ lieSet ε) =>
      (innerSL ℂ z).intervalIntegral_comp_comm ((hc l hl).intervalIntegrable (μ := volume) 0 t)
    simp only [innerSL_apply_apply] at i1
    have i2 := i1 (Dw σ l.reverse y) [] (by simp)
    simp only [Dw, List.foldr_nil] at i2
    rw [inner_add_right, ← i1 y l hl, inner_Dw hU hl hy (hw.translate hU (exp_mem_UJ hX t)), inner_Dw hU hl hy hw]
    simp only [fun s => inner_Dw hU hl hy (hw'.translate hU (exp_mem_UJ hX s))]
    rw [intervalIntegral.integral_const_mul, i2, h0, inner_sub_right]
    ring
  simp only [key]
  have := ((hc l hl).integral_hasStrictDerivAt 0 0).hasDerivAt.const_add (Dw σ l w)
  rwa [e0] at this

end DerivativeContinuity

theorem c6 : C6 := fun _ _ _ _ _ _ _ hU hI _ hl _ hw _ hX => DerivativeContinuity.hasDerivAt_Dw hU hI hl hw hX

end PositivityTheory.CW
