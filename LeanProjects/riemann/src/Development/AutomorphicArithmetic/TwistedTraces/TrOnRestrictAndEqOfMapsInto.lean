import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

section SlopeTestRemainingChoices

open scoped InnerProductSpace

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem prj_eq (E : Submodule ℂ H) [FiniteDimensional ℂ E] : UpperTheory.ConvolutionTheory.C.prj E = E.starProjection := by
  have h : E.topologicalClosure = E := E.closed_of_finiteDimensional.submodule_topologicalClosure_eq
  unfold UpperTheory.ConvolutionTheory.C.prj
  congr 1

private noncomputable def cprs (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) : Module.End ℂ E :=
  (E.orthogonalProjection : H →ₗ[ℂ] E) ∘ₗ (T : H →ₗ[ℂ] H) ∘ₗ E.subtype

private theorem cprs_coe (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) (v : E) :
    (cprs E T v : H) = E.starProjection (T v) := rfl

private theorem trOn_eq (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) :
    UpperTheory.ConvolutionTheory.C.trOn E T = LinearMap.trace ℂ E (cprs E T) := by
  let b := stdOrthonormalBasis ℂ E
  rw [LinearMap.trace_eq_sum_inner _ b, UpperTheory.ConvolutionTheory.C.trOn, prj_eq, GroundTheory.Automorphic.trace]
  set S : H →L[ℂ] H := T ∘L E.starProjection with hS
  refine HasSum.tsum_eq ?_
  have h := hasSum_sum (s := Finset.univ) fun k _ =>
    (GroundTheory.Automorphic.stdHilbertBasis ℂ H).hasSum_inner_mul_inner (ContinuousLinearMap.adjoint S (b k : H)) (b k : H)
  convert h using 1
  · rfl
  · funext i
    rw [ContinuousLinearMap.comp_apply, b.starProjection_eq_sum_rankOne]
    simp only [ContinuousLinearMap.sum_apply, inner_sum, InnerProductSpace.rankOne_apply, inner_smul_right,
      ContinuousLinearMap.adjoint_inner_left]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, Submodule.coe_inner, cprs_coe, hS, ContinuousLinearMap.comp_apply,
      Submodule.starProjection_eq_self_iff.2 (b k).2, ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (b k).2]

private theorem trOn_of_restrict (E : Submodule ℂ H) [FiniteDimensional ℂ E] (B : H →L[ℂ] H) (b : Module.End ℂ E)
    (hb : ∀ v : E, ((b v : E) : H) = B v) : UpperTheory.ConvolutionTheory.C.trOn E B = LinearMap.trace ℂ E b := by
  rw [trOn_eq]
  congr 1
  ext v
  rw [cprs_coe, ← hb, Submodule.starProjection_eq_self_iff.2 (b v).2]

end SlopeTestRemainingChoices

theorem UpperTheory.trOn_restrict_and_eq_of_maps_into :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (X Y : Submodule ℂ H) [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y] (B : H →L[ℂ] H), (∀ b : Module.End ℂ X, (∀ v : X, ((b v : X) : H) = B v) → trOn X B = LinearMap.trace ℂ X b) ∧ (X ≤ Y → (∀ v ∈ Y, B v ∈ X) → trOn Y B = trOn X B) := by
  intro H _ _ _ X Y _ _ B
  refine ⟨fun b hb => trOn_of_restrict X B b hb, fun hXY hY => ?_⟩
  let p : Y →ₗ[ℂ] X := LinearMap.codRestrict X ((B : H →ₗ[ℂ] H) ∘ₗ Y.subtype) fun v => hY v v.2
  let i : X →ₗ[ℂ] Y := Submodule.inclusion hXY
  rw [trOn_of_restrict Y B (i ∘ₗ p) fun v => rfl, trOn_of_restrict X B (p ∘ₗ i) fun v => rfl]
  exact LinearMap.trace_comp_comm' p i
