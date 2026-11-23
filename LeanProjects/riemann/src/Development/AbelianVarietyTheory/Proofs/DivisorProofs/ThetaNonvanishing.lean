import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermsVanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigConstantTermConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallConstantTermConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitExistenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTowerPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroThetaRelevantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroDualThetaRelevantSoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementSkewCmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigATripleEigenFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleEigenFactorStatement

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKNZ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem split2_zero {a a' d₁ : ℕ} {W : Spc F E (a + a')} (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (X : Chars F E) :
    Split2 (σ := σ) (W := W) W₁ H' X 0 0 0 :=
  ⟨fun _ _ _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩

theorem om_one {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (om : Rep σ Y W) : om (1, 1) = 1 := by
  rw [← Prod.one_eq_mk, map_one]

theorem claimV (hK : GlobalTheory.ThK.KP) (n : ℕ) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    G.p + G.q = n → IsTriple B G X om om' → ∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F E _ _ _ _ _ σ B a a' G X om om' hn hT
  by_cases hp : G.p = 0
  · exact (GlobalTheory.T.analytic_nonvanishing hK F E σ B a a' G X om om' hT).1 hp
  by_cases hq : 1 ≤ G.q
  · obtain ⟨b, rfl⟩ : ∃ b, a' = b + 2 := ⟨a' - 2, by have := hT.geo.aBig; omega⟩
    obtain ⟨V, V', W, hT', G₁, H, H', hC, om₁, om₁', hT₁⟩ := (GlobalTheory.T.theta_tower_properties hK.base).2 F E σ B a b G X om om' hT hq
    refine GlobalTheory.T.exists_nonzero_theta_relevant hK F E σ B a (b + 2) G X om om' V V' W hT hT' ?_
    have hn₁ : G₁.p + G₁.q < n := by have := hC.ep; have := hC.eq; simp only [reG] at *; omega
    obtain ⟨Φ₁, hΦ₁, hI₁⟩ := ih _ hn₁ F E σ B a b G₁ X om₁ om₁' rfl hT₁
    obtain ⟨h₁, hh₁⟩ := Function.ne_iff.1 hI₁
    obtain ⟨m, hm⟩ := GlobalTheory.T.exists_levi_element_skew_cm F E σ B _ _ _ G₁.W H' _ _ _ _ hT'.base.cm hT'.geo.hW hC.hH' h₁
    have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT').1
    obtain ⟨⟨e, he⟩, hmap⟩ := (GlobalTheory.T.theta_evaluation_zero_cone hK.base).1 F E σ B _ _ (reG G V V' W).V (reG G V V' W).W (reG G V V' W).M _ _ om _ _ _ _ hP (a + b) G₁.V G₁.W H' a (a + b + 1)
      G₁.M hC.eV hC.hH' hT₁.geo.hM
    rw [← hmap e he] at hΦ₁
    obtain ⟨Φ, hΦ, rfl⟩ := hΦ₁
    obtain ⟨C, hC0, hCT⟩ := (GlobalTheory.T.constant_terms_vanish hK).1 F E σ B a b (reG G V V' W) G₁ H H' hC e he
    obtain ⟨x, hx, hu⟩ := ((GlobalTheory.T.split_existence hK) F E σ B a (b + 2) (reG G V V' W) X om om' hT' (a + b) G₁.W H' a (a + b + 1) hC.hH').1 Φ hΦ
    refine ⟨Φ, hΦ, fun h0 => hh₁ ?_⟩
    have hx0 : (0, 0) = x := hu (0, 0) (by rw [h0]; exact split2_zero _ _ _)
    have := hCT X om om' om₁ om₁' hT' hT₁ Φ hΦ x.1 x.2 hx h₁ m hm 1
    rw [← hx0] at this
    simp only [LinearMap.map_zero, Prod.snd_zero] at this
    erw [om_one] at this
    rw [mul_one] at this
    simpa [hC0] using this.symm
  · have hq0 : G.q = 0 := by omega
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by have := hT.geo.aBig; have := hT.geo.lt; omega⟩
    obtain ⟨V, V', W, hT', G₁, H, H', hC, om₁, om₁', hT₁⟩ :=
      (GlobalTheory.T.theta_tower_properties hK.base).1 F E σ B b a' G X om om' hT hq0 (Nat.one_le_iff_ne_zero.2 hp)
    refine GlobalTheory.T.exists_nonzero_theta_relevant hK F E σ B (b + 2) a' G X om om' V V' W hT hT' ?_
    have hn₁ : G₁.p + G₁.q < n := by have := hC.ep; have := hC.q1; simp only [reG] at *; omega
    have hI₁ := ih _ hn₁ F E σ B b a' G₁ X om₁ om₁' rfl hT₁
    have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT').1
    obtain ⟨⟨e, he⟩, -⟩ := (GlobalTheory.T.theta_evaluation_zero_cone hK.base).2 F E σ B _ _ (reG G V V' W).V (reG G V V' W).W (reG G V V' W).M _ _ om _ _ _ _ hP b (b + a') G₁.V G₁.W H H' 0 (b + 1) 0 (b + 1)
      G₁.M hC.hH hC.hH' hT₁.geo.hM
    obtain ⟨K, μK, μ, hK1, -, hK3, hK4⟩ := (GlobalTheory.T.theta_stabilizer_exists hK.base) F E σ B _ _ _ _ hT'.base hT'.geo.hV
    obtain ⟨Φ, hΦ, h, h₁, m, hm, hne⟩ := GlobalTheory.T.config_a_triple_eigen_factor hK F E σ B b a' (reG G V V' W) G₁ H H' X om om' om₁ om₁' hC hT' hT₁ e he K μK μ hK1 hK3 hK4 hI₁
    obtain ⟨C, hC0, hCT⟩ := (GlobalTheory.T.big_constant_term_cone hK) F E σ B b a' (reG G V V' W) G₁ H H' hC e he K μK μ hK1 hK3 hK4
    obtain ⟨x, hx, hu⟩ := ((GlobalTheory.T.split_existence hK) F E σ B (b + 2) a' (reG G V V' W) X om om' hT' (b + a') G₁.W H' 0 (b + 1) hC.hH').1 Φ hΦ
    refine ⟨Φ, hΦ, fun h0 => hne ?_⟩
    have hx0 : (0, 0) = x := hu (0, 0) (by rw [h0]; exact split2_zero _ _ _)
    have := hCT X om om' om₁ om₁' hT' hT₁ Φ hΦ x.1 x.2 hx h₁ m hm h
    rw [← hx0] at this
    simpa [hC0] using this.symm

theorem claimV' (hK : GlobalTheory.ThK.KP) (n : ℕ) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    G.p + G.q = n → IsTriple B G X om om' → ∃ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, G.M'.I om' Φ' ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F E _ _ _ _ _ σ B a a' G X om om' hn hT
  by_cases hq : G.q = 0
  · exact (GlobalTheory.T.analytic_nonvanishing hK F E σ B a a' G X om om' hT).2 hq
  obtain ⟨b, rfl⟩ : ∃ b, a' = b + 2 := ⟨a' - 2, by have := hT.geo.aBig; omega⟩
  obtain ⟨V, V', W, hT', G₁, H, H', hC, om₁, om₁', hT₁⟩ :=
    (GlobalTheory.T.theta_tower_properties hK.base).2 F E σ B a b G X om om' hT (Nat.one_le_iff_ne_zero.2 hq)
  refine GlobalTheory.T.nonzero_dual_theta_relevant_so hK F E σ B a (b + 2) G X om om' V V' W hT hT' ?_
  have hn₁ : G₁.p + G₁.q < n := by have := hC.ep; have := hC.eq; simp only [reG] at *; omega
  have hI₁ := ih _ hn₁ F E σ B a b G₁ X om₁ om₁' rfl hT₁
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT').2
  obtain ⟨-, e', he'⟩ := (GlobalTheory.T.theta_evaluation_zero_cone hK.base).2 F E σ B _ _ (reG G V V' W).V' (reG G V V' W).W (reG G V V' W).M' _ _ om' _ _ _ _ hP b (a + b) G₁.V' G₁.W H H' a (a + b + 1) 0 (b + 1)
    G₁.M' hC.hH hC.hH' hT₁.geo.hM'
  obtain ⟨K, μK, μ, hK1, -, hK3, hK4⟩ := (GlobalTheory.T.theta_stabilizer_exists hK.base) F E σ B _ _ _ _ hT'.base hT'.geo.hV'
  obtain ⟨Φ', hΦ', h, h₁, m, hm, hne⟩ := GlobalTheory.T.config_b_triple_eigen_factor hK F E σ B a b (reG G V V' W) G₁ H H' X om om' om₁ om₁' hC hT' hT₁ e' he' K μK μ hK1 hK3 hK4 hI₁
  obtain ⟨C, hC0, hCT⟩ := (GlobalTheory.T.small_constant_term_cone hK) F E σ B a b (reG G V V' W) G₁ H H' hC e' he' K μK μ hK1 hK3 hK4
  obtain ⟨x, hx, hu⟩ := ((GlobalTheory.T.split_existence hK) F E σ B a (b + 2) (reG G V V' W) X om om' hT' (a + b) G₁.W H' a (a + b + 1) hC.hH').2 Φ' hΦ'
  refine ⟨Φ', hΦ', fun h0 => hne ?_⟩
  have hx0 : (0, 0) = x := hu (0, 0) (by rw [h0]; exact split2_zero _ _ _)
  have := hCT X om om' om₁ om₁' hT' hT₁ Φ' hΦ' x.1 x.2 hx h₁ m hm h
  rw [← hx0] at this
  simpa [hC0] using this.symm

theorem nonZero : GlobalTheory.ThK.KP → GlobalTheory.ThK.NonZero := fun hK F E _ _ _ _ _ σ B a a' G X om om' hT =>
  ⟨claimV hK _ F E σ B a a' G X om om' rfl hT, claimV' hK _ F E σ B a a' G X om om' rfl hT⟩

end GlobalTheory.ThKNZ
