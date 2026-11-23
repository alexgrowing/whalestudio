import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedRealMapArchimedeanActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAMatchedRealizationStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine

theorem twPart_le_map_lowPart : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ s : R₁.Pi →ₗ[ℂ] R.Pi,
        twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p) ≤ (lowPartInf B G₁.M R₁.p).map s ∧
        ∀ k₁ ∈ KInf σ G₁.W B.emb, ∀ k ∈ KInf σ G.W B.emb, IsLevi H' 1 k₁ k →
          ∀ g ∈ G₁.M.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin b × Fin (b + a')), Acts (evI F) (om₁ (1, k₁)) g g₁ →
            R₁.p g ∈ lowPartInf B G₁.M R₁.p →
          ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin (b + 2) × Fin (b + 2 + a')), Acts (evI F) (om (1, k)) f f₁ →
            s (R₁.p g) = R.p f → s (R₁.p g₁) = R.p f₁ := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  obtain ⟨s, hle, hne, heq⟩ := GlobalTheory.T.config_a_matched_realization hKP F E σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  refine ⟨s, ?_, heq⟩
  by_cases h0 : twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p) = ⊥
  · rw [h0]; exact bot_le
  have hK : KStabL B G.M om R.p G₁.W H' ((lowPartInf B G₁.M R₁.p).map s) := by
    intro k hk k₁ hk₁ hL f hf f₁ hf₁ hpf
    obtain ⟨y, hy, hye⟩ := hpf
    obtain ⟨g, hg, rfl⟩ := hy
    have hgP : g ∈ G₁.M.Pol B.ψ B.emb := fockDeg_le_pol G₁.M B.ψ B.emb _ hg
    have hyl : R₁.p g ∈ lowPartInf B G₁.M R₁.p := ⟨g, hg, rfl⟩
    obtain ⟨A, hA⟩ := GlobalTheory.T.exists_archOperator_compact_unitaryW F E σ B _ _ G₁.V G₁.W G₁.M om₁ X.β (X.β / X.α) hM₁.triple.base
      hM₁.triple.geo.hM hM₁.triple.weil k₁ hk₁
    have h1 := heq k₁ hk₁ k hk hL g hgP (A g) (hA g) hyl f hf f₁ hf₁ hye
    exact ⟨R₁.p (A g), GlobalTheory.T.matched_real_map_archimedean_action F E σ B b a' G₁ X om₁ om₁' R₁ Rf₁ hM₁ k₁ hk₁ g hgP (A g) (hA g) hyl, h1⟩
  rcases (GlobalTheory.T.config_a_theta_local_factor hKP F E σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁).2.2 _ hle hK with h | h
  · exact absurd h (hne h0)
  · exact h.symm.le

end GlobalTheory.IndLine
