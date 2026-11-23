import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContinuousScalarFour
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContinuousAb
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.EmbPiInjective
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ActCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private theorem om_L' {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {D : Dat ℚ E} (W : Weil D)
    (g : G1 ℚ) (h : GL (Fin 2) (A E)) (hh : nu ℚ h = 1) (φ : S4 ℚ) :
    W.Om g (W.L h φ) = W.L h (W.Om g φ) := by
  have e := congrArg (fun T : Module.End ℂ (S4 ℚ) => T φ) (W.comm h g)
  simp only [Module.End.mul_apply, hh] at e
  rw [e, UpperTheory.ConvolutionTheory.R2.M.cD_one]

private theorem term_eq {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {D : Dat ℚ E} (W : Weil D)
    (g : G1 ℚ) (h : GL (Fin 2) (A E)) (hh : nu ℚ h = 1) (φ : S4 ℚ) (v : V4 ℚ) :
    (W.Om g (W.L h φ)).1 v = (W.Om g φ).1 (D.act h⁻¹ v) := by
  rw [om_L' W g h hh, W.L_apply, hh, ab_one]
  simp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.thCont :
    ThCont := by
  intro E _ _ _ D W _ _ _ ph hph S p₀ hp₀
  obtain ⟨ρ, hρ, hact, -, -, -⟩ := actCont ℚ E D
  obtain ⟨n, hn⟩ := wtSum ℚ
  obtain ⟨S₁, hS₁, hm₁⟩ := exists_compact_mem_nhds p₀.1
  obtain ⟨S₂, hS₂, hm₂⟩ := exists_compact_mem_nhds p₀.2
  obtain ⟨K, hK, hb⟩ := lDom ℚ E D W (G1 ℚ) S₁ (fun g => W.Om g ph)
    (omCpt ℚ E D W ph hph S₁ hS₁) S₂ hS₂
  obtain ⟨B, hB⟩ := hb n
  obtain ⟨C, hC⟩ := hn K hK 1 one_pos
  obtain ⟨hs, -⟩ := hC 1 (by rw [ab_one])
  have e : (fun ξ : Fin 4 → ℚ => wt K n (sc (1 : (A ℚ)ˣ) ξ)) = fun ξ => wt K n (rp ξ) := by
    funext ξ
    congr 1
    funext i
    change ((1 : (A ℚ)ˣ) : A ℚ) * rt (ξ i) = rt (ξ i)
    rw [Units.val_one, one_mul]
  rw [e] at hs
  have key : ContinuousOn (fun p : G1 ℚ × GL (Fin 2) (A E) => ThOn S (W.Om p.1 (W.L p.2 ph)).1)
      ((S₁ ×ˢ S₂) ∩ {p | nu ℚ p.2 = 1}) := by
    unfold ThOn
    refine continuousOn_tsum (u := fun ξ : S => B * wt K n (rp ξ.1)) (fun ξ => ?_)
      ((hs.mul_left B).subtype S) fun ξ p hp => ?_
    · have hc : Continuous fun p : G1 ℚ × GL (Fin 2) (A E) =>
          (W.Om p.1 ph).1 ((ρ p.2⁻¹).val *ᵥ rp ξ.1) :=
        (W.cont ph).comp (continuous_fst.prodMk
          ((Units.continuous_val.comp (hρ.comp (continuous_inv.comp continuous_snd))).matrix_mulVec
            continuous_const))
      refine hc.continuousOn.congr fun p hp => ?_
      rw [term_eq W p.1 p.2 hp.2, hact]
    · have hnorm := hB (p.2, p.1) ⟨hp.1.2, hp.1.1⟩ (rp ξ.1)
      have e' : (W.Om p.1 (W.L p.2 ph)).1 (rp ξ.1) = (W.L p.2 (W.Om p.1 ph)).1 (rp ξ.1) := by
        rw [om_L' W p.1 p.2 hp.2]
      rw [e']
      exact hnorm
  have hT : (S₁ ×ˢ S₂) ∩ {p : G1 ℚ × GL (Fin 2) (A E) | nu ℚ p.2 = 1} ∈
      𝓝[{p : G1 ℚ × GL (Fin 2) (A E) | nu ℚ p.2 = 1}] p₀ :=
    inter_mem (mem_nhdsWithin_of_mem_nhds (prod_mem_nhds hm₁ hm₂)) self_mem_nhdsWithin
  exact (key p₀ ⟨⟨mem_of_mem_nhds hm₁, mem_of_mem_nhds hm₂⟩, hp₀⟩).mono_of_mem_nhdsWithin hT
