import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.WeakStable
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SameSat
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.LiftAll
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SmoEq
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CarryLift
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreLift
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PowTwist
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Published UpperTheory.CBC

private theorem weak_same {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    [IsTotallyComplex F] [IsTotallyComplex E] {n : ℕ} (hp : (Module.finrank F E).Prime) (π : CuspSub F n)
    {sat sat' : Pl E → Multiset ℂˣ → Prop} (H : WeakBC (CG.mk π).HasSat sat) (H' : WeakBC (CG.mk π).HasSat sat') :
    ∀ᶠ w : Pl E in cofinite, ∃ B, sat w B ∧ sat' w B := by
  have hN := (places F E hp).2.2.2.2.1
  filter_upwards [H, H'] with w a b
  obtain ⟨B, hB, hB'⟩ := a _ (hN w)
  obtain ⟨C, hC, hC'⟩ := b _ (hN w)
  obtain rfl := hB.unique hC
  exact ⟨_, hB', hC'⟩

theorem UpperTheory.ConvolutionTheory.Sph.weakStable :
    UpperTheory.ConvolutionTheory.Sph.WeakStable := by
  intro K M _ _ _ _ _ _ _ _ hp n hn π P hW
  refine ⟨?_, fun v => ?_, fun w => ?_⟩
  · haveI : Fact (Module.finrank K M).Prime := ⟨hp⟩
    haveI : FiniteDimensional K M := Module.finite_of_finrank_pos hp.pos
    haveI : IsCyclic (M ≃ₐ[K] M) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K M)
    obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := M ≃ₐ[K] M)
    let μE : Measure (normOneGL M n) := Measure.haar
    let μF : Measure (normOneGL K n) := Measure.haar
    obtain ⟨s, χ, χ', V, -, -, hχ, hχ', hV, -, -, -, hW', hOff, -⟩ :=
      UpperTheory.ConvolutionTheory.Sph.norm K M σ hσ hp n hn μE μF π P hW
    obtain ⟨-, htw⟩ := powTwist K M
    obtain ⟨hi, hi', h1⟩ := htw s χ χ' hχ hχ'
    obtain ⟨-, hback, -⟩ := h1 n hn
    obtain ⟨-, -, h2⟩ := htw (-s) χ⁻¹ χ'⁻¹ hi hi'
    obtain ⟨-, -, -, hCj, -⟩ := h2 n hn
    obtain ⟨c1, -, c3, -, -, θ, hθ, c6⟩ := carryLift K M σ hσ hp n hn μE μF
    obtain ⟨Λ, t, hAt⟩ := c1 V hV.summand
    obtain ⟨V₂, hV₂, hst, hAt₂⟩ :=
      coreLift ci Sph.gm K M σ hσ hp n hn μE μF θ hθ V Λ t hV.summand hAt (hOff Λ t hAt)
    obtain ⟨P₂, hP₂, -⟩ := Dp.exCusp M n μE V₂ hV₂
    have hl := c3 _ P₂ V V₂ Λ t _ _ hV hP₂ hAt hAt₂ rfl (Filter.Eventually.of_forall fun _ => rfl)
    have e : P₂ = P.twist χ' := Sph.smoEq M n hn P₂ (P.twist χ') (weak_same hp (π.twist χ) hl.1 hW')
    rw [e] at hP₂
    intro g
    have h := hCj (P.twist χ') _ ((c6 _ V₂ hP₂).2 hst g)
    rwa [hback] at h
  · exact (LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL K n π v).imp fun _ h => h.1
  · exact (LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL M n P w).imp fun _ h => h.1
