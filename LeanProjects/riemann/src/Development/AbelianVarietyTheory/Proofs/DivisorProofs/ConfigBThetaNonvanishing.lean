import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartCompactStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartEndomorphismScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBRealPlaceH1BranchStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine

theorem config_b_real_place_h1 : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ V : Submodule ℂ R.Pi, V ≠ ⊥ ∧ KStab B G.M om R.p V ∧
        ∀ φ φ' : R.Pi →ₗ[ℂ] R₁.Pi, IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.β ((a : ℝ) / 2) φ →
          IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.β ((a : ℝ) / 2) φ' →
          (∀ v ∈ V, φ v = 0) ∨ ∃ c : ℂ, ∀ v ∈ V, φ' v = c • φ v := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  have hS := (GlobalTheory.T.low_part_compact_stable) hKP F E σ B a (b + 2) G X om om' R Rf hM
  have hMu := (GlobalTheory.T.low_part_endomorphism_scalar) hKP F E σ B a b G₁ X om₁ om₁' R₁ Rf₁ hM₁
  obtain ⟨π, hπ', hπ⟩ := (GlobalTheory.T.config_b_real_place_h1_branch) hKP F E σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  refine ⟨lowPartInf B G.M R.p, ?_, hS, ?_⟩
  · apply lowPartInf_ne_bot
    haveI := hM.real.nontriv
    obtain ⟨y, hy⟩ := exists_ne (0 : R.Pi)
    have hy' : y ∈ (G.M.Pol B.ψ B.emb).map R.p := by rw [hM.real.quot.onto]; trivial
    obtain ⟨f, hf, rfl⟩ := hy'
    exact ⟨f, hf, hy⟩
  · intro φ φ' hφ hφ'
    obtain ⟨T, hT, hφT⟩ := hπ φ hφ
    obtain ⟨T', hT', hφT'⟩ := hπ φ' hφ'
    obtain ⟨c, hc⟩ := hMu T hT
    obtain ⟨c', hc'⟩ := hMu T' hT'
    by_cases h0 : c = 0
    · left
      intro v hv
      rw [hφT v hv, hc _ (hπ' v hv), h0, zero_smul]
    · right
      refine ⟨c' / c, fun v hv => ?_⟩
      rw [hφT' v hv, hφT v hv, hc' _ (hπ' v hv), hc _ (hπ' v hv), smul_smul, div_mul_cancel₀ _ h0]

end GlobalTheory.IndLine
