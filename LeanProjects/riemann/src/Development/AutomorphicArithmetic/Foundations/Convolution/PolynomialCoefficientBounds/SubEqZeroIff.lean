import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ShiftPow
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.LiftSingleAlt

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

theorem UpperTheory.ConvolutionTheory.FX.sub_eq_zero_iff :
    ∀ (ι κ : Type) [Fintype ι] (b : Fam ι κ) (F : KF ι κ), b.sub F = 0 ↔ ∀ Λ h, b.Mem Λ h → evK Λ h F = 0 := by
  intro ι κ _ b F
  have key : ∀ lam : Fin b.r → ℂ, ev lam (b.sub F) =
      evK (fun i => b.Λ i + ∑ j, (b.emb i j : ℂ) * lam j) (fun k => ev lam (b.h k)) F := fun lam => by
    have : (ev lam).comp b.sub = evK (fun i => b.Λ i + ∑ j, (b.emb i j : ℂ) * lam j) (fun k => ev lam (b.h k)) :=
      MvPolynomial.ringHom_ext (fun f => by
        simpa [Fam.sub, evK] using (UpperTheory.ConvolutionTheory.FX.subst ι _ b.Λ b.emb f).1 lam) (fun k => by simp [Fam.sub, evK])
    exact RingHom.congr_fun this F
  refine ⟨fun h0 Λ h ⟨lam, h1, h2⟩ => ?_, fun h => UpperTheory.ConvolutionTheory.FX.ev_inj _ _ fun lam => ?_⟩
  · rw [funext h1, funext h2, ← key, h0, map_zero]
  · rw [key]
    exact h _ _ ⟨lam, fun _ => rfl, fun _ => rfl⟩
