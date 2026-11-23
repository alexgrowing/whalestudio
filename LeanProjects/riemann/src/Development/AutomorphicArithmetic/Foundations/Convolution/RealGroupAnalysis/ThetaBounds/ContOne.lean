import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThBoundH
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Vol
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThMeas
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContinuousAb
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtBound
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.EmbPiInjective
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ActCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.UnitsCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]

private theorem top_GL (E : Type) [Field E] [NumberField E] :
    LocallyCompactSpace (GL (Fin 2) (Cinf E)) ∧ FirstCountableTopology (GL (Fin 2) (Cinf E)) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (Cinf E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → Cinf E))
  haveI : FirstCountableTopology (Matrix (Fin 2) (Fin 2) (Cinf E)) :=
    inferInstanceAs (FirstCountableTopology (Fin 2 → Fin 2 → Cinf E))
  haveI : FirstCountableTopology (Matrix (Fin 2) (Fin 2) (Cinf E))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin 2) (Fin 2) (Cinf E))).symm.isInducing.firstCountableTopology
  have h := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin 2) (Fin 2) (Cinf E))
  exact ⟨h.locallyCompactSpace, h.isEmbedding.isInducing.firstCountableTopology⟩

private theorem om_L {D : Dat F E} (W : Weil D) (g : G1 F) (h : GL (Fin 2) (A E))
    (hh : nu F h = 1) (φ : S4 F) : W.Om g (W.L h φ) = W.L h (W.Om g φ) := by
  have e := congrArg (fun T : Module.End ℂ (S4 F) => T φ) (W.comm h g)
  simp only [Module.End.mul_apply, hh] at e
  rw [e, UpperTheory.ConvolutionTheory.R2.M.cD_one]

private theorem term_cont (D : Dat F E) (W : Weil D) (Ψ : S4 F) (v : V4 F) :
    Continuous fun y : GL (Fin 2) (Cinf E) => (W.L (infGL E 2 y) Ψ).1 v := by
  obtain ⟨ρ, hρ, hact, hnu, hinf, -⟩ := actCont F E D
  have hΨ := (wtBound F Ψ).1
  have e : (fun y : GL (Fin 2) (Cinf E) => (W.L (infGL E 2 y) Ψ).1 v) = fun y =>
      (((ab (nu F (infGL E 2 y)))⁻¹ : ℝ) : ℂ) * Ψ.1 ((ρ (infGL E 2 y)⁻¹).val *ᵥ v) := by
    funext y
    rw [W.L_apply, hact]
  rw [e]
  refine Continuous.mul ?_ ?_
  · exact Complex.continuous_ofReal.comp
      ((continuous_ab.comp (hnu.comp hinf)).inv₀ fun _ => (ab_pos _).ne')
  · refine hΨ.comp ?_
    have h1 : Continuous fun y : GL (Fin 2) (Cinf E) => ρ (infGL E 2 y)⁻¹ :=
      hρ.comp (continuous_inv.comp hinf)
    exact (Units.continuous_val.comp h1).matrix_mulVec continuous_const

private theorem th_cont (D : Dat F E) (W : Weil D) (Ψ : S4 F) (S : Set (GL (Fin 2) (Cinf E)))
    (hS : IsCompact S) : ContinuousOn (fun y => Th (W.L (infGL E 2 y) Ψ).1) S := by
  obtain ⟨n, hn⟩ := wtSum F
  obtain ⟨ρ, -, -, -, hinf, -⟩ := actCont F E D
  obtain ⟨K, hK, hb⟩ := lDom F E D W Unit Set.univ (fun _ => Ψ) (wtBound F Ψ).2
    (infGL E 2 '' S) (hS.image hinf)
  obtain ⟨B, hB⟩ := hb n
  obtain ⟨C, hC⟩ := hn K hK 1 one_pos
  obtain ⟨hs, -⟩ := hC 1 (by rw [ab_one])
  have e : (fun ξ : Fin 4 → F => wt K n (sc (1 : (A F)ˣ) ξ)) = fun ξ => wt K n fun i => rt (ξ i) := by
    funext ξ
    congr 1
    funext i
    change ((1 : (A F)ˣ) : A F) * rt (ξ i) = rt (ξ i)
    rw [Units.val_one, one_mul]
  rw [e] at hs
  unfold Th
  refine continuousOn_tsum (fun ξ => (term_cont D W Ψ _).continuousOn) (hs.mul_left B) ?_
  intro ξ y hy
  exact hB (infGL E 2 y, ()) ⟨⟨y, hy, rfl⟩, trivial⟩ _

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Ff.contOne :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ContOne W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ y₀ hy₀
  obtain ⟨ρ, -, -, hnu, hinf, -⟩ := actCont F E D
  obtain ⟨hlc, hfc⟩ := top_GL E
  have hfcont : Continuous f.1 := (decay F π f hf).1
  obtain ⟨S, hS, hSmem⟩ := exists_compact_mem_nhds y₀
  have hcl : IsClosed {y : GL (Fin 2) (Cinf E) | UpperTheory.ConvolutionTheory.R2.Ff.One F y} :=
    isClosed_eq (hnu.comp hinf) continuous_const
  have hC' := hS.inter_right hcl
  obtain ⟨B, hB⟩ := thBoundH F E D W π f hf φ hφ 1 {1} isCompact_singleton _ hC' (fun y hy => hy.2)
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using vol F M⟩
  have key : ContinuousWithinAt (fun y : GL (Fin 2) (Cinf E) =>
      ∫ g, f.1 (gl g) * Th (W.Om g (W.L (infGL E 2 y) φ)).1 ∂(M.μ.restrict M.D))
      {y | UpperTheory.ConvolutionTheory.R2.Ff.One F y} y₀ := by
    refine continuousWithinAt_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const _) ?_
    · filter_upwards with y
      exact ((hfcont.comp continuous_gl).measurable.mul
        (thMeas F E D W (W.L (infGL E 2 y) φ)).1).aestronglyMeasurable
    · have hev : ∀ᶠ y in 𝓝[{y | UpperTheory.ConvolutionTheory.R2.Ff.One F y}] y₀,
          y ∈ S ∩ {y | UpperTheory.ConvolutionTheory.R2.Ff.One F y} :=
        inter_mem (mem_nhdsWithin_of_mem_nhds hSmem) self_mem_nhdsWithin
      filter_upwards [hev] with y hy
      refine ae_of_all _ fun g => ?_
      simpa using hB g 1 rfl y hy
    · refine ae_of_all _ fun g => ?_
      have h1 : ContinuousAt (fun y => Th (W.L (infGL E 2 y) (W.Om g φ)).1) y₀ :=
        (th_cont D W (W.Om g φ) S hS).continuousAt hSmem
      have h2 : ContinuousWithinAt (fun y => Th (W.Om g (W.L (infGL E 2 y) φ)).1)
          {y | UpperTheory.ConvolutionTheory.R2.Ff.One F y} y₀ :=
        h1.continuousWithinAt.congr (fun y hy => by rw [om_L W g _ hy]) (by rw [om_L W g _ hy₀])
      exact continuousWithinAt_const.mul h2
  refine key.congr (fun y hy => ?_) ?_
  · have hy' : nu F (infGL E 2 y) = 1 := hy
    simp only [lift, hy', dM_one, mul_one]
  · have hy' : nu F (infGL E 2 y₀) = 1 := hy₀
    simp only [lift, hy', dM_one, mul_one]
