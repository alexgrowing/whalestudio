import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.SaturationTransportPair

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.F.RS

attribute [local instance] borelG borelF borelA borelH

section Back

open PositivityTheory.Rg.BcB.F.RS.JetMatrixAlgebra GlobalTheory.ThetaSatake
open GlobalTheory.LFun.ConjPlace (dGL invT dGL_comm invT_dGL)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem fx_dGL_inv (x : Pl E) (n : ℕ) (p : (x.adicCompletion E)ˣ) :
    fx x n (dGL n p n)⁻¹ =
      dGL n (Units.map ((cloc x).symm : x.adicCompletion E →* (cw x).adicCompletion E) p) n := by
  have hc : Commute (dGL n p n) (PhiU n (x.adicCompletion E)) := dGL_comm p _
  have e : (PhiU n (x.adicCompletion E))⁻¹ * (dGL n p n)⁻¹ * PhiU n (x.adicCompletion E) = (dGL n p n)⁻¹ := by
    rw [mul_assoc, hc.inv_left.eq, inv_mul_cancel_left]
  change invT (cloc x).symm n ((MulAut.conj (PhiU n (x.adicCompletion E))).symm (dGL n p n)⁻¹) = _
  rw [MulAut.conj_symm_apply, e]
  exact invT_dGL (cloc x).symm p n

private theorem Tj_fx_symm (x : Pl E) (n : ℕ) {p : x.adicCompletion E} (hp : IsUnifV E x p) (hp0 : p ≠ 0) {i : ℕ}
    (hi : i ≤ n) (g : GLw n (cw x)) :
    Tj ℂ n (Ov E x) p i ((fx x n).symm g) =
      Tj ℂ n (Ov E (cw x))
        ((Units.map ((cloc x).symm : x.adicCompletion E →* (cw x).adicCompletion E) (Units.mk0 p hp0) :
          ((cw x).adicCompletion E)ˣ) : (cw x).adicCompletion E) (n - i)
        (dGL n (Units.map ((cloc x).symm : x.adicCompletion E →* (cw x).adicCompletion E) (Units.mk0 p hp0)) n * g) := by
  have h := Tj_fx x n hp hp0 (Nat.sub_le n i) ((dGL n (Units.mk0 p hp0) n)⁻¹ * (fx x n).symm g)
  rw [map_mul, fx_dGL_inv, MulEquiv.apply_symm_apply, mul_inv_cancel_left, Nat.sub_sub_self hi] at h
  exact h.symm

private theorem satake_conjugate_inverse {a b : ℕ} (x : Pl E) {G : H E a b → ℂ} {B₁ B₂ : Multiset ℂˣ}
    (hs : IsSat2 (cw x) (pairRtT a b (cw x)) G B₁ B₂) :
    IsSat2 x (pairRt a b x) G (B₁.map (·⁻¹)) (B₂.map (·⁻¹)) := by
  rw [pairRtT_cw] at hs
  have h := saturation_transport_pair ((fx x a).prodCongr (fx x b)).symm (fun g => ?_) (absNorm_cw x).symm
    (fun ϖ' hϖ' => ?_) hs
  · have e : ((pairRt a b x).comp ((fx x a).prodCongr (fx x b)).symm.toMonoidHom).comp
        ((fx x a).prodCongr (fx x b)).symm.symm.toMonoidHom = pairRt a b x := by
      ext1 g
      simp
    rw [e] at h
    exact h
  · show g ∈ (KGL (cw x) a).prod (KGL (cw x) b) ↔
      ((fx x a).prodCongr (fx x b)).symm g ∈ (KGL x a).prod (KGL x b)
    rw [Subgroup.mem_prod, Subgroup.mem_prod]
    have h1 := mem_fx_iff x a ((fx x a).symm g.1)
    have h2 := mem_fx_iff x b ((fx x b).symm g.2)
    rw [MulEquiv.apply_symm_apply] at h1 h2
    exact and_congr h1.symm h2.symm
  · have hp0 : ϖ' ≠ 0 := fun e => by simp [IsUnifV, e] at hϖ'
    refine ⟨Units.map ((cloc x).symm : x.adicCompletion E →* (cw x).adicCompletion E) (Units.mk0 ϖ' hp0),
      (cloc_symm_v x ϖ').trans hϖ', fun i hi j hj g => ?_⟩
    exact congrArg₂ (· * ·) (Tj_fx_symm x a hϖ' hp0 hi g.1) (Tj_fx_symm x b hϖ' hp0 hj g.2)

end Back

theorem UpperTheory.Zero.ConvolutionTheory.EB.sat2Back :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (G : H E a b → ℂ) (B₁ B₂ : Multiset ℂˣ), IsSplitAt w → IsSat2 w (pairRtT a b w) G B₁ B₂ →
    IsSat2 (cPl w) (pairRt a b (cPl w)) G (inv B₁) (inv B₂) := by
  intro E _ _ _ a b w G B₁ B₂ _ hs
  have e : GlobalTheory.ThetaSatake.cw (GlobalTheory.ThetaSatake.cw w) = w := GlobalTheory.ThetaPull.conjSrc_conjSrc w
  have hs' : IsSat2 (GlobalTheory.ThetaSatake.cw (GlobalTheory.ThetaSatake.cw w))
      (pairRtT a b (GlobalTheory.ThetaSatake.cw (GlobalTheory.ThetaSatake.cw w))) G B₁ B₂ := by
    rw [e]
    exact hs
  exact satake_conjugate_inverse (GlobalTheory.ThetaSatake.cw w) hs'
