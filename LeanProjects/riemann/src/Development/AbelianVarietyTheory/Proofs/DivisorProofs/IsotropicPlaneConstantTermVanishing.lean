import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviIsoPlaneUnique
open scoped TensorProduct NNReal Matrix ContDiff
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.DescB.GenCont

theorem one_mem_kInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n : ℕ} (Y : Spc F E n) (τ : ∀ w : InfinitePlace F, EmbOver E w) : (1 : UA σ Y.J) ∈ KInf σ Y τ := by
  have h1 : mat (1 : UA σ Y.J) = 1 := rfl
  refine ⟨?_, fun w => ?_⟩
  · show At (evI F) (mat (1 : UA σ Y.J) - 1)
    rw [h1, sub_self]
    unfold At
    simp
  · rw [h1, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Commute.one_left _

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E), B.IsGood σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (P : Plane E n n₁), (∀ i j, σ (Y.J j i) = -Y.J i j) →
      IsIsoPlane σ B P Y Y₁ →
      ∀ (c : E) (hc : c ≠ 0), σ c = -c →
      ∀ fa : UA σ Y.J → ℂ, (∀ K : Subgroup (GAd σ (c • Y.J.map σ)), (∀ x ∈ K, (toGAd hσ Y.J hc).symm x ∈ KInf σ Y B.emb) →
        IsAutOn σ (c • Y.J.map σ) ((unip σ Y P).map (toGAd hσ Y.J hc).toMonoidHom) K (fun x => fa ((toGAd hσ Y.J hc).symm x))) →
      ∀ h ∈ finK σ Y B.emb, (∀ h₁ : UA σ Y₁.J, ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) P 1 h₁ m) →
      ∀ g : UA σ Y₁.J → ℂ, (∀ h₁ m, IsLevi (W₁ := Y₁) P 1 h₁ m → g h₁ = fa (m * h)) →
      Continuous (fun x => g ((toGAd hσ Y₁.J hc).symm x)) := by
  intro F E _ _ _ _ _ σ hσ B _ n n₁ Y Y₁ P hsk hP c hc _ fa hfa h _ _ g hg
  have hd : Y₁.J.det ≠ 0 := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    exact GlobalTheory.LeviUniqueCartan.det_ne_zero_of_isCartan _ _ _ (hP.2.2.2.2.2.2.2 w)
  obtain ⟨M, hMc, hM, -⟩ :=
    (GlobalTheory.ThK.GLTwo.IsIsoPlane.isHypPlane hP).exists_leviHom hσ hsk hd
  have hA := (hfa ⊥ fun x hx => by
    rw [Subgroup.mem_bot.1 hx, map_one]; exact one_mem_kInf Y B.emb).cont
  have hfc : Continuous fa :=
    (hA.comp (GlobalTheory.ThK.GLTwo.continuous_toGAd hσ Y.J hc).1).congr fun x => by
      simp only [Function.comp_apply, MulEquiv.symm_apply_apply]
  haveI := (GlobalTheory.UnipCT.topFacts σ Y.J).1
  have hgc : Continuous g := (hfc.comp (hMc.mul continuous_const)).congr fun h₁ => (hg h₁ (M h₁) (hM h₁)).symm
  exact hgc.comp (GlobalTheory.ThK.GLTwo.continuous_toGAd hσ Y₁.J hc).2

end GlobalTheory.ThK.DescB.GenCont

end
