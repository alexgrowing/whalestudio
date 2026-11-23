import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.ExistsGap
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.WdValAppend

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private lemma wdVal_map {B C Γ : Type} [CommRing B] [StarRing B] [Algebra ℂ B] [Ring C] [StarRing C] [Algebra ℂ C]
    (f : B →⋆ₐ[ℂ] C) (gen : Γ → B) (w : List (Γ × Bool)) :
    f (wdVal gen w) = wdVal (fun x => f (gen x)) w := by
  induction w with
  | nil => simp [wdVal]
  | cons p w ih =>
    simp only [wdVal, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    split_ifs <;> simp [map_star]

theorem peakAlg : PeakAlg := by
  intro H _ _ _ Q _ Γ op v 𝔄 arch a₀ x ρ ha hv hρ hs
  let gen : {γ // arch γ} → 𝔄.B := fun γ => 𝔄.ι γ
  let A : StarSubalgebra ℂ 𝔄.B := StarAlgebra.adjoin ℂ (Set.range gen)
  have hmem : ∀ γ : {γ // arch γ}, 𝔄.ι γ ∈ A := fun γ =>
    StarAlgebra.subset_adjoin ℂ (Set.range gen) (Set.mem_range_self γ)
  let p : A →⋆ₐ[ℂ] ℂ := 𝔄.P.comp A.subtype
  let a₁ : A := ⟨𝔄.ι a₀, hmem ⟨a₀, ha⟩⟩
  obtain ⟨g, hg, hn⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.peak 𝔄.B Q 𝔄.R A p a₁ (𝔄.ι x) ρ
    (by
      change 𝔄.P (𝔄.ι a₀) = 1
      rw [𝔄.hP, hv])
    hρ
    (fun s hb hsa => hs s hb fun γ hγ => by
      have h1 := hsa ⟨𝔄.ι γ, hmem ⟨γ, hγ⟩⟩
      have h2 : p ⟨𝔄.ι γ, hmem ⟨γ, hγ⟩⟩ = v γ := by
        change 𝔄.P (𝔄.ι γ) = v γ
        exact 𝔄.hP γ
      rw [← h2]
      exact h1)
  obtain ⟨J, hJ, c, w, L, -, hgw, -⟩ := PositivityTheory.Rg.BcB.F.adjWords _ _ gen (g : 𝔄.B) g.2
  refine ⟨J, hJ, c, w, ?_, ?_⟩
  · have hp : 𝔄.P (g : 𝔄.B) = 1 := hg
    rw [hgw, map_sum] at hp
    rw [← hp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, wdVal_map, smul_eq_mul]
    congr 2
    funext γ
    exact (𝔄.hP γ).symm
  · have hF : op x * ((∑ j, c j • wdVal (fun γ : {γ // arch γ} => op γ) (w j)) * op a₀) =
        𝔄.F (𝔄.ι x * ((g : 𝔄.B) * 𝔄.ι a₀)) := by
      rw [map_mul, map_mul, 𝔄.hF, 𝔄.hF, hgw, map_sum]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, wdVal_map]
      congr 2
      funext γ
      exact (𝔄.hF γ).symm
    rw [hF]
    have hnorm : ‖𝔄.F (𝔄.ι x * ((g : 𝔄.B) * 𝔄.ι a₀)) ∘L Q.subtypeL‖ =
        ‖𝔄.R (𝔄.ι x * ((g : 𝔄.B) * 𝔄.ι a₀))‖ := by
      refine ContinuousLinearMap.opNorm_ext _ _ fun q => ?_
      change ‖𝔄.F _ (q : H)‖ = ‖(𝔄.R _ q)‖
      rw [← 𝔄.hR]
      rfl
    rw [hnorm]
    exact hn

end UpperTheory.Zero.ConvolutionTheory.EB
