import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartLeFixedPartImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerUpperFixedPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowDegreeLeFixedDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedPartIrreducibleStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine

theorem lowPartInf_irred : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ N : Submodule ℂ R.Pi, N ≤ lowPartInf B G.M R.p →
        (∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
          Acts (evI F) (om (1, k)) f f₁ → R.p f ∈ N → R.p f₁ ∈ N) →
        N = ⊥ ∨ N = lowPartInf B G.M R.p := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM N hNV hN
  have hA := GlobalTheory.T.low_part_le_fixed_part_image hK F E σ B a a' G X om om' R Rf hM
  have hB := GlobalTheory.T.stabilizer_upper_fixed_part hK F E σ B a a' G X om om' hM.triple (lowDegInf B G.M R.p)
  have hC := GlobalTheory.T.fixed_part_irreducible hK F E σ B a a' G X om om' hM.triple (lowDegInf B G.M R.p)
    (GlobalTheory.T.low_degree_le_fixed_degree hK F E σ B a a' G X om om' R Rf hM)
  have hP := fixPart_le_pol B G.M om (lowDegInf B G.M R.p)
  rcases hC (fixPart B G.M om (lowDegInf B G.M R.p) ⊓ N.comap R.p) inf_le_left
      (fun k hk f hf f₁ h1 => ⟨hB k hk f hf.1 f₁ h1, hN k hk f (hP hf.1) f₁ h1 hf.2⟩) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨f, hf, rfl⟩ := hA (hNV hx)
    have hf' : f ∈ fixPart B G.M om (lowDegInf B G.M R.p) ⊓ N.comap R.p := ⟨hf, hx⟩
    rw [h, Submodule.mem_bot] at hf'
    rw [hf', map_zero]
    exact Submodule.zero_mem _
  · right
    refine le_antisymm hNV fun x hx => ?_
    obtain ⟨f, hf, rfl⟩ := hA hx
    rw [← h] at hf
    exact hf.2

end GlobalTheory.IndLine
