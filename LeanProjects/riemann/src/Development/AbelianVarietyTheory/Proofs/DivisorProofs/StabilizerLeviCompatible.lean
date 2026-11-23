import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingMultiplicativeStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.IwDec

theorem iwasawa_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    ∀ g : UA σ G.V.J, ∃ n ∈ unip σ G.V H, ∃ l g₀, ∃ k ∈ K, g = n * m l g₀ * k := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁ K hK m hm g
  obtain ⟨p, hp, k, hk, rfl⟩ := GlobalTheory.IwLine.iwasawa B hB hG.hV hC.hH g
  have hkK : k ∈ K := (hK k).2 ((GlobalTheory.StabHaar.isStab_stabK (σ := σ) B G.V k).1 hk)
  obtain ⟨⟨n, l, g₀⟩, hz, -⟩ :=
    (GlobalTheory.T.levi_embedding_multiplicative F E σ B (b + 2) b G.V G₁.V _ _ _ _ 0 (b + 1) H hB hG.hV hG₁.hV hC.hH m hm).2.2.2.1 p hp
  exact ⟨n.1, n.2, l, g₀, k, hkK, by rw [hz]⟩

end GlobalTheory.IwDec
