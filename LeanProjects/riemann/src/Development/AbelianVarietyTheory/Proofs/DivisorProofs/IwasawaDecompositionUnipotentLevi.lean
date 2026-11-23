import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryFiniteInfiniteSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompInfiniteIsotropicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicLeviUnipotentSplitStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.IwasawaLine

theorem iwasawa : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ →
    ∀ g : UA σ G.W.J, ∃ n ∈ unip σ G.W H', ∃ (t : (AE F E)ˣ) (m₁ : UA σ G.W.J), IsLevi (W₁ := W₁) H' t 1 m₁ ∧
      ∃ (h₁ : UA σ W₁.J) (m₂ : UA σ G.W.J), IsLevi (W₁ := W₁) H' 1 h₁ m₂ ∧ ∃ k ∈ finK σ G.W B.emb, g = n * m₁ * m₂ * k := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH g
  have hcm := hT.base.cm
  have hW := hT.geo.hW
  have hx : H'.x ≠ 0 := by
    intro h0
    have := hH.xy
    rw [h0] at this
    simp [form] at this
  obtain ⟨gi, hgi, gf, hgf, rfl⟩ := GlobalTheory.T.adelic_unitary_finite_infinite_split F E σ G.W g
  obtain ⟨p, t, hpt, k, hk, rfl⟩ := GlobalTheory.T.iwasawa_decomp_infinite_isotropic F E σ B G.W _ _ H'.x hcm hW hx hH.xx gi hgi
  obtain ⟨n, hn, m₁, hm₁, h₁, m₂, hm₂, rfl⟩ := GlobalTheory.T.parabolic_levi_unipotent_split F E σ B G.W W₁ H' _ _ i₀ i₁ hcm hW hH p t hpt
  exact ⟨n, hn, t, m₁, hm₁, h₁, m₂, hm₂, k * gf, ⟨k, hk, gf, hgf, rfl⟩, by simp only [mul_assoc]⟩

end GlobalTheory.ThK.IwasawaLine
