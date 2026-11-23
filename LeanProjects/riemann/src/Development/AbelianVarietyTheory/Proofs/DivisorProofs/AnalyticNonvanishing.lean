import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTowerPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroThetaLiftAnisotropicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroDualThetaLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigATripleCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroThetaLiftRelevantSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroDualThetaLiftRelevantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroThetaLiftSoTypeStatement

noncomputable section

namespace GlobalTheory.ThKNonZero

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem partV (hK : KP) : ∀ n : ℕ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.p = 0 → G.q = n → ∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro F E _ _ _ _ _ σ B a a' G X om om' h hp hq
    exact GlobalTheory.T.exists_nonzero_theta_lift_anisotropic hK F E σ B a a' G X om om' h hp hq
  | succ n ih =>
    intro F E _ _ _ _ _ σ B a a' G X om om' h hp hq
    obtain ⟨b, rfl⟩ : ∃ b, a' = b + 2 := ⟨a' - 2, by have := h.geo.aBig; omega⟩
    obtain ⟨-, hTB⟩ := GlobalTheory.T.theta_tower_properties hK.base
    obtain ⟨h0, -⟩ := GlobalTheory.T.theta_evaluation_zero_cone hK.base
    obtain ⟨V, V', W, t, G₁, H, H', c, om₁, om₁', t₁⟩ := hTB F E σ B a b G X om om' h (by omega)
    have hp₁ : G₁.p = 0 := c.ep.trans hp
    have hq₁ : G₁.q = n := by have := c.eq; simp only [reG] at this; omega
    obtain ⟨Φ₁, hΦ₁, hne⟩ := ih F E σ B a b G₁ X om₁ om₁' t₁ hp₁ hq₁
    have hev := h0 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV t) _ _ _ H' _ _ G₁.M c.eV c.hH' t₁.geo.hM
    obtain ⟨e, he⟩ := hev.1
    have hmap := hev.2 e he
    have hm : Φ₁ ∈ (PolData B (reG G V V' W).M).map e := hmap ▸ hΦ₁
    obtain ⟨Φ, hΦ, rfl⟩ := Submodule.mem_map.1 hm
    exact GlobalTheory.T.nonzero_theta_lift_relevant_space hK F E σ B a (b + 2) G X om om' V V' W h t hp
      ⟨Φ, hΦ, fun hz => hne (GlobalTheory.T.config_b_triple_compatibility hK F E σ B a b (reG G V V' W) G₁ H H' X om om' om₁ om₁' c t t₁ hp e he Φ hΦ hz)⟩

theorem partV' (hK : KP) : ∀ n : ℕ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.q = 0 → G.p = n → ∃ Φ' ∈ PolData B G.M', G.M'.I om' Φ' ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro F E _ _ _ _ _ σ B a a' G X om om' h hq hp
    exact GlobalTheory.T.exists_nonzero_dual_theta_lift hK F E σ B a a' G X om om' h hp hq
  | succ n ih =>
    intro F E _ _ _ _ _ σ B a a' G X om om' h hq hp
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by have := h.geo.aBig; have := h.geo.lt; omega⟩
    obtain ⟨hTA, -⟩ := GlobalTheory.T.theta_tower_properties hK.base
    obtain ⟨h0, -⟩ := GlobalTheory.T.theta_evaluation_zero_cone hK.base
    obtain ⟨V, V', W, t, G₁, H, H', c, om₁, om₁', t₁⟩ := hTA F E σ B b a' G X om om' h hq (by omega)
    have hq₁ : G₁.q = 0 := c.q1
    have hp₁ : G₁.p = n := by have := c.ep; simp only [reG] at this; omega
    obtain ⟨Φ₁, hΦ₁, hne⟩ := ih F E σ B b a' G₁ X om₁ om₁' t₁ hq₁ hp₁
    have hev := h0 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' t) _ _ _ H' _ _ G₁.M' c.eV c.hH' t₁.geo.hM'
    obtain ⟨e, he⟩ := hev.1
    have hmap := hev.2 e he
    have hm : Φ₁ ∈ (PolData B (reG G V V' W).M').map e := hmap ▸ hΦ₁
    obtain ⟨Φ, hΦ, rfl⟩ := Submodule.mem_map.1 hm
    exact GlobalTheory.T.nonzero_dual_theta_lift_relevant hK F E σ B (b + 2) a' G X om om' V V' W h t hq
      ⟨Φ, hΦ, fun hz => hne (GlobalTheory.T.config_a_triple_compatibility hK F E σ B b a' (reG G V V' W) G₁ H H' X om om' om₁ om₁' c t t₁ e he Φ hΦ hz)⟩

theorem nonZeroAn (hK : KP) : NonZeroAn := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h
  refine ⟨fun hp => partV hK _ F E σ B a a' G X om om' h hp rfl, fun hq => ?_⟩
  obtain ⟨Φ', hΦ', hne⟩ := partV' hK _ F E σ B a a' G X om om' h hq rfl
  exact GlobalTheory.T.exists_nonzero_theta_lift_so_type hK F E σ B a a' G X om om' h hq Φ' hΦ' hne

end GlobalTheory.ThKNonZero

end
