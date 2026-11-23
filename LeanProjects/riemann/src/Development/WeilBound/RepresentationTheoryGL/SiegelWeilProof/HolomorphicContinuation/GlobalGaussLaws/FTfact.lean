import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CompAtNeg

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open Classical

set_option synthInstance.maxHeartbeats 400000 in
theorem fTfact : FTfact := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι ctx w hw
  have hθ := ctx.hθ
  have hψ := ctx.hψ
  have hl := ctx.hl
  have hfr := ctx.hfr
  have hω := ctx.hω
  obtain ⟨𝓕, hcov⟩ := ctx.hμ
  have : μ.IsAddHaarMeasure := hcov.1
  have ht : tLoc l τ ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (lNe D ψ θ l hψ hθ hl τ)
  have hmt : -tLoc l τ ≠ 0 := neg_ne_zero.2 ht
  obtain ⟨c₀, hc₀⟩ := FTH.ww_act hω w hw
  refine ⟨1, FTH.Aw ψ V θ τ fr μ, fun Ψ x => c₀ * FTH.Aw ψ V θ τ fr μ Ψ (-x), one_ne_zero, fun Ψ hΨ => ?_⟩
  have hW : ∀ f (hf : IsSch f), (ω w ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 =
      tens θ τ fr (fun u => 1 * ftLoc ε (tLoc l τ) f u) (FTH.Aw ψ V θ τ fr μ Ψ) :=
    fun f hf => FTH.weyl_tens hθ hψ hl hfr μ hω w hw Ψ hΨ f hf
  have hWi : ∀ f (hf : IsSch f), (ω w⁻¹ ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 =
      tens θ τ fr (fun u => (1 : ℂ)⁻¹ * ftLoc ε (-tLoc l τ) f u) (fun x => c₀ * FTH.Aw ψ V θ τ fr μ Ψ (-x)) := by
    intro f hf
    rw [FTH.inv_eq_www w hw, map_mul]
    funext x
    rw [Module.End.mul_apply, hc₀, congrFun (hW f hf) (-x)]
    simp only [tens, FTH.compAt_neg, Matrix.mul_neg, inv_one, one_mul]
    have h := FTD.ftLoc_neg ε (tLoc l τ) f (fr⁻¹ * compAt θ τ x)
    erw [h]
    ring
  have hneg : ∀ x x' : Mx D V.rank n, (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') →
      x.map (finPart D) = x'.map (finPart D) →
      (∀ τ', τ' ≠ τ → compAt θ τ' (-x) = compAt θ τ' (-x')) ∧ (-x).map (finPart D) = (-x').map (finPart D) := by
    intro x x' hx hf
    refine ⟨fun τ' h => by rw [FTH.compAt_neg, FTH.compAt_neg, hx τ' h], ?_⟩
    ext i j
    have := congrFun (congrFun hf i) j
    simp only [Matrix.map_apply, Matrix.neg_apply, RingHom.map_neg] at this ⊢
    rw [this]
  refine ⟨⟨fun x x' hx hf => FTH.Aw_away hθ hfr.1 ψ μ Ψ x x' hx hf, fun g hg => ?_⟩,
    ⟨fun x x' hx hf => ?_, fun g hg => ?_⟩, fun f hf => ⟨FTD.isSch_ftLoc ε _ ht 1 f hf,
      FTD.isSch_ftLoc ε _ hmt (1 : ℂ)⁻¹ f hf, hW f hf, hWi f hf⟩⟩
  · obtain ⟨f, hf, hfg⟩ := FTD.ftLoc_surj ε (tLoc l τ) ht g hg
    have e : tens θ τ fr g (FTH.Aw ψ V θ τ fr μ Ψ) = (ω w ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 := by
      rw [hW f hf, ← hfg]; simp only [one_mul]
    rw [e]; exact (ω w _).2
  · obtain ⟨h1, h2⟩ := hneg x x' hx hf
    show c₀ * FTH.Aw ψ V θ τ fr μ Ψ (-x) = c₀ * FTH.Aw ψ V θ τ fr μ Ψ (-x')
    rw [FTH.Aw_away hθ hfr.1 ψ μ Ψ (-x) (-x') h1 h2]
  · obtain ⟨f, hf, hfg⟩ := FTD.ftLoc_surj ε (-tLoc l τ) hmt g hg
    have e : tens θ τ fr g (fun x => c₀ * FTH.Aw ψ V θ τ fr μ Ψ (-x)) = (ω w⁻¹ ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 := by
      rw [hWi f hf, ← hfg]; simp only [inv_one, one_mul]
    rw [e]; exact (ω w⁻¹ _).2

end PositivityTheory.Rg.Sw.Glob
