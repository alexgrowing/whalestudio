import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinThetaPairingStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinHaarStabilizerUnfoldingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinHaarStabilizerIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeromorphicContinuationDistinctConstantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConeRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitExistenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviTorusElementCm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorIdeleNormalizedAbsIdeleHalfAtInfinity

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ConeSmallCT

theorem ne_of_re_ne {u v : Circle} {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) {w w' : ℂ} (h : w.re ≠ w'.re) :
    (u : ℂ) * (r : ℂ) ^ w ≠ (v : ℂ) * (r : ℂ) ^ w' := by
  intro heq
  have hn := congrArg norm heq
  simp only [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr] at hn
  apply h
  have hl := congrArg Real.log hn
  rw [Real.log_rpow hr, Real.log_rpow hr] at hl
  exact mul_right_cancel₀ (Real.log_ne_zero_of_pos_of_ne_one hr hr1) hl

theorem ctSmall_eq_cone : GlobalTheory.ThK.KP → GlobalTheory.ConeSmall.EisAtMinusRho → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∃ fa : UA σ G.W.J → ℂ, HasLaw G₁.W H' X.α (((b + 2 : ℕ) : ℝ) / 2) fa ∧
        IsCT H' (G.M'.I om' Φ') (fa + fun h => C * GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (((a - (b + 2)) / 2 + 1 : ℕ) : ℂ) h) := by
  intro hKP hEis F E _ _ _ _ _ σ B a b G G₁ H H' hCfg e' he' K μK μ hK hμK hμ
  obtain ⟨C, hC0, hD⟩ := GlobalTheory.T.config_b_stabilizer_integral_factor hKP F E σ B a b G G₁ H H' hCfg e' he' K μK μ hK hμK hμ
  refine ⟨C, hC0, ?_⟩
  intro X om om' om₁ om₁' hT hT₁ Φ' hΦ'
  obtain ⟨Eis, hSer, hE1, hE2⟩ := hEis F E σ B a b G G₁ H H' hCfg X om om' hT K hK
  have hEG : EisGood (σ := σ) b Eis := ⟨hE1, hE2⟩
  obtain ⟨⟨fa, fb⟩, ⟨hct, hla, hlb⟩, -⟩ :=
    (GlobalTheory.T.split_existence hKP F E σ B a (b + 2) G X om om' hT (a + b) G₁.W H' a (a + b + 1) hCfg.hH').2 Φ' hΦ'
  replace hla : HasLaw G₁.W H' X.α (((b + 2 : ℕ) : ℝ) / 2) fa := hla
  replace hlb : HasLaw G₁.W H' X.β ((a : ℝ) / 2) fb := hlb
  replace hct : IsCT H' (G.M'.I om' Φ') (fa + fb) := hct
  refine ⟨fa, hla, ?_⟩
  intro μ₁ 𝓕 hμ₁ h𝓕 h𝓕1 h
  have hlt : b + 2 < a := hT.geo.lt
  obtain ⟨s₁d, hd⟩ := hD X om om' om₁ om₁' hT hT₁ Φ' hΦ' Eis hSer
  obtain ⟨s₁e, he⟩ := GlobalTheory.T.config_b_constant_term_four_summands_hasLawC hKP F E σ B a b G G₁ H H' hCfg e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ'
  obtain ⟨Tr, hTr⟩ := GlobalTheory.T.exists_cone_representatives F E σ (a + (b + 2)) G.W.J H'.x
  have hcm := hT.base.cm
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.ThK.exists_isLevi F E σ B _ _ G.W G₁.W H' _ _ _ _ hcm hT.geo.hW hCfg.hH' (GlobalTheory.Eis.Conv.halfE F E)
  have habs := GlobalTheory.Eis.Conv.absE_halfE F E σ hcm
  have hcard : 0 < Fintype.card (InfinitePlace F) := by
    obtain ⟨τ⟩ : Nonempty (F →+* ℂ) := inferInstance
    exact Fintype.card_pos_iff.2 ⟨InfinitePlace.mk τ⟩
  have hr0 : (0 : ℝ) < (absE F E (GlobalTheory.Eis.Conv.halfE F E) : ℝ) := by
    rw [habs]; positivity
  have hr1 : (absE F E (GlobalTheory.Eis.Conv.halfE F E) : ℝ) ≠ 1 := by
    rw [habs]; push_cast
    have h4 : (1 : ℝ) < 4 ^ Fintype.card (InfinitePlace F) := one_lt_pow₀ (by norm_num) hcard.ne'
    intro h1; rw [inv_eq_one] at h1; linarith
  have hrc : ((absE F E (GlobalTheory.Eis.Conv.halfE F E) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'

  let c₁ : ℂ → ℂ := fun s => (X.β (GlobalTheory.Eis.Conv.halfE F E) : ℂ) *
    ((absE F E (GlobalTheory.Eis.Conv.halfE F E) : ℝ) : ℂ) ^ ((s + ((a : ℂ) + 1) / 2) + (b : ℂ) / 2)
  let c₂ : ℂ → ℂ := fun s => (X.β (GlobalTheory.Eis.Conv.halfE F E) : ℂ) *
    ((absE F E (GlobalTheory.Eis.Conv.halfE F E) : ℝ) : ℂ) ^ (-s + ((a + b + 1 : ℕ) : ℂ) / 2)
  let c₃ : ℂ → ℂ := fun _ => (X.α (GlobalTheory.Eis.Conv.halfE F E) : ℂ) *
    ((absE F E (GlobalTheory.Eis.Conv.halfE F E) : ℝ) : ℂ) ^ (((b + 2 : ℕ) : ℂ) / 2)
  let c₄ : ℂ → ℂ := fun _ => (X.β (GlobalTheory.Eis.Conv.halfE F E) : ℂ) *
    ((absE F E (GlobalTheory.Eis.Conv.halfE F E) : ℝ) : ℂ) ^ (((a + 2 : ℕ) : ℂ) / 2)
  let s₀ : ℂ := -((((b + 2 : ℕ) : ℂ) - 1) / 2)
  let Ω : Set ℂ := {s | -(((a : ℝ) - 1) / 2) < s.re}
  let Ω₁ : Set ℂ := {s | max (max s₁d s₁e) 0 < s.re}
  let Bf : ℂ → UA σ G.W.J → ℂ := fun s y => ∫ u in 𝓕, Bint G.M' om' Φ' Eis s (u.1 * y) ∂μ₁
  let Fm : ℂ → UA σ G.W.J → ℂ := fun s y => C * GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2) y
  have hΩ1 : ∀ s ∈ Ω₁, s₁d < s.re ∧ s₁e < s.re ∧ s ∈ Ω := by
    intro s hs
    simp only [Ω₁, Ω, Set.mem_setOf_eq, max_lt_iff] at hs ⊢
    refine ⟨hs.1.1, hs.1.2, ?_⟩
    have : (1 : ℝ) ≤ a := by exact_mod_cast (by omega : 1 ≤ a)
    linarith
  have hs₀ : s₀ ∈ Ω := by
    have e0 : s₀ = ((-(((b : ℝ) + 2 - 1) / 2) : ℝ) : ℂ) := by simp only [s₀]; push_cast; ring
    simp only [Ω, Set.mem_setOf_eq, e0, Complex.ofReal_re]
    have : ((b : ℝ) + 2) + 1 ≤ a := by exact_mod_cast hlt
    linarith
  have hz₀ : s₀ + ((a : ℂ) + 1) / 2 = (((a - (b + 2)) / 2 + 1 : ℕ) : ℂ) := by
    obtain ⟨k, hk⟩ := hT.geo.even
    have h2 : (a - (b + 2)) / 2 = a - (b + 2 + (a - (b + 2)) / 2) := by omega
    have hk' : a = b + 2 + 2 * ((a - (b + 2)) / 2) := by omega
    simp only [s₀]
    rw [show (a : ℂ) = ((b + 2 + 2 * ((a - (b + 2)) / 2) : ℕ) : ℂ) by rw [← hk']]
    push_cast; ring
  have e1 : s₀ + ((a : ℂ) + 1) / 2 + (b : ℂ) / 2 = (((a : ℝ) / 2 : ℝ) : ℂ) := by simp only [s₀]; push_cast; ring
  have e2 : -s₀ + ((a + b + 1 : ℕ) : ℂ) / 2 = (((a : ℝ) / 2 + b + 1 : ℝ) : ℂ) := by simp only [s₀]; push_cast; ring
  have e3 : ((b + 2 : ℕ) : ℂ) / 2 = ((((b : ℝ) + 2) / 2 : ℝ) : ℂ) := by push_cast; ring
  have e4 : ((a + 2 : ℕ) : ℂ) / 2 = ((((a : ℝ) + 2) / 2 : ℝ) : ℂ) := by push_cast; ring
  have hb0 : (0 : ℝ) ≤ b := b.cast_nonneg
  have hab : (b : ℝ) + 2 + 1 ≤ a := by exact_mod_cast hlt
  have n12 : c₁ s₀ ≠ c₂ s₀ := by
    simp only [c₁, c₂]; rw [e1, e2]
    exact ne_of_re_ne hr0 hr1 (by simp only [Complex.ofReal_re]; intro h; linarith)
  have n13 : c₁ s₀ ≠ c₃ s₀ := by
    simp only [c₁, c₃]; rw [e1, e3]
    exact ne_of_re_ne hr0 hr1 (by simp only [Complex.ofReal_re]; intro h; linarith)
  have n14 : c₁ s₀ ≠ c₄ s₀ := by
    simp only [c₁, c₄]; rw [e1, e4]
    exact ne_of_re_ne hr0 hr1 (by simp only [Complex.ofReal_re]; intro h; linarith)
  have key := GlobalTheory.T.meromorphic_continuation_distinct_constants (UA σ G.W.J) (fun y => m₀ * y) c₁ c₂ c₃ c₄
    (by
      refine Differentiable.const_mul (Differentiable.const_cpow (by fun_prop) (Or.inl hrc)) _)
    (by
      refine Differentiable.const_mul (Differentiable.const_cpow (by fun_prop) (Or.inl hrc)) _)
    (differentiable_const _) (differentiable_const _) Ω Ω₁ s₀
    (isOpen_lt continuous_const Complex.continuous_re) (convex_halfSpace_re_gt _).isPreconnected
    (isOpen_lt continuous_const Complex.continuous_re)
    ⟨((max (max s₁d s₁e) 0 + 1 : ℝ) : ℂ), by simp only [Ω₁, Set.mem_setOf_eq, Complex.ofReal_re]; linarith⟩ (fun s hs => (hΩ1 s hs).2.2) hs₀
    n12 n13 n14
    Bf Fm
    (fun y s _ => (GlobalTheory.T.eisenstein_theta_pairing_stabilizer hKP F E σ B a b G G₁ H H' hCfg X om om' hT K hK Φ' hΦ' Eis hSer hEG μ₁ 𝓕 hμ₁ h𝓕 h𝓕1 y).1 s)
    (fun y => (GlobalTheory.T.eisenstein_theta_pairing_stabilizer hKP F E σ B a b G G₁ H H' hCfg X om om' hT K hK Φ' hΦ' Eis hSer hEG μ₁ 𝓕 hμ₁ h𝓕 h𝓕1 y).2)
    (by
      intro y
      have hb := GlobalTheory.T.eisenstein_haar_stabilizer_unfolding hKP F E σ B a b G G₁ H H' hCfg e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' y
      refine DifferentiableOn.const_mul (hb.comp (by fun_prop) ?_) C
      intro s hs
      have ez : s + ((a : ℂ) + 1) / 2 = s + ((((a : ℝ) + 1) / 2 : ℝ) : ℂ) := by push_cast; ring
      simp only [Ω, Set.mem_setOf_eq] at hs ⊢
      rw [ez, Complex.add_re, Complex.ofReal_re]
      linarith)
    (by
      intro s _ y
      have hc := GlobalTheory.T.eisenstein_haar_stabilizer_integral hKP F E σ B a b G G₁ H H' hCfg e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' (s + ((a : ℂ) + 1) / 2)
        _ m₀ hm₀ y
      simp only [Fm, c₁, hc]; ring)
    (by
      intro s hs
      obtain ⟨hsd, hse, -⟩ := hΩ1 s hs
      obtain ⟨hLU, hHS⟩ := hd Tr hTr s hsd
      obtain ⟨T₂, T₃, T₄, hCT, h2, h3, h4⟩ := he Tr hTr s hse hLU
      refine ⟨C • T₂, C • T₃, C • T₄, ?_, ?_, ?_, ?_⟩
      · intro y
        have hB : ∀ h, Bint G.M' om' Φ' Eis s h = C * ∑' t : Tr, GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2) (t.1 * h) := fun h => by
          rw [← (hHS h).tsum_eq, tsum_mul_left]
        have hc := hCT μ₁ 𝓕 hμ₁ h𝓕 h𝓕1 y
        simp only [Bf, Fm, hB, integral_const_mul, ← hc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · intro y; simp only [Pi.smul_apply, smul_eq_mul, h2 _ m₀ hm₀ y, c₂]; ring
      · intro y; simp only [Pi.smul_apply, smul_eq_mul, h3 _ m₀ hm₀ y, c₃]; ring
      · intro y; simp only [Pi.smul_apply, smul_eq_mul, h4 _ m₀ hm₀ y, c₄]; ring)
    fa fb
    (by
      intro y
      obtain ⟨U, -, C', N', hU⟩ := hE2
      have hI : ∀ h, Bint G.M' om' Φ' Eis s₀ h = G.M'.I om' Φ' h := fun h => by
        simp only [Bint, Model.I, s₀, (hU _).2.2, mul_one]
      have := hct μ₁ 𝓕 hμ₁ h𝓕 h𝓕1 y
      simp only [Bf, hI, Pi.add_apply] at this ⊢
      exact this.symm)
    (by
      intro y
      rw [hla _ m₀ hm₀ y]
      simp only [c₃]
      rw [Complex.ofReal_cpow hr0.le]
      push_cast; ring)
    (by
      intro y
      rw [hlb _ m₀ hm₀ y]
      simp only [c₁]
      rw [Complex.ofReal_cpow hr0.le]
      have : s₀ + ((a : ℂ) + 1) / 2 + (b : ℂ) / 2 = (((a : ℝ) / 2 : ℝ) : ℂ) := by simp only [s₀]; push_cast; ring
      rw [this])
  have := hct μ₁ 𝓕 hμ₁ h𝓕 h𝓕1 h
  rw [key] at this
  simpa only [Fm, hz₀] using this

end GlobalTheory.ConeSmallCT

end
