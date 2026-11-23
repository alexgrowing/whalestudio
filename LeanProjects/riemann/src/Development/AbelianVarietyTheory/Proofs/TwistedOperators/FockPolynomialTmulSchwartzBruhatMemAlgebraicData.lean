import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGaussEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix

noncomputable section

namespace GlobalTheory.SquareAgree

theorem pureA_mem_algD : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), M.IsGood ψ →
    ∀ f ∈ M.Pol ψ τ, ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F),
      GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.SquareAgree.algD M ψ τ := by
  intro F E _ _ _ _ _ σ n d X W M ψ τ hM f hf g hg
  obtain ⟨m, c, φ, hφSB, hφstd, hgeq⟩ := GlobalTheory.EvAdm.exists_sum_finprod hg
  have hφvac : ∀ k, ∀ᶠ v in Filter.cofinite, φ k v = M.vac v := fun k =>
    ((hφstd k).and hM.std).mono fun v h => h.1.trans h.2.symm
  have h1 : GlobalTheory.WeilM.pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) g =
      ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
    rw [hgeq]
    funext x
    simp only [GlobalTheory.WeilM.pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [mul_left_comm]
    rfl
  rw [h1]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, φ k, hf, hφSB k, hφvac k, rfl⟩)

end GlobalTheory.SquareAgree

end
