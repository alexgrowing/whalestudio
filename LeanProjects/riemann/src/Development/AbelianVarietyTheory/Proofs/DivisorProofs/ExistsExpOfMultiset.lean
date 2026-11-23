import Mathlib
import CompanionTheory.EightfoldTheory.VariationTheory.PublishedTheorems.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.IsHermOfInner
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.UnitTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.ExistsZalgOfCenterU
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FoundBridge
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterAbsoluteValuePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterRamifiedFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeEigenvalueLeCardCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTjCosetsFiniteCardLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTnScalarUniformiserSingleTranslationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormRootLeCardMulBoundOfEsymmNormLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormInvLePowCardOfNormProdEqOneStatement

noncomputable section

open NumberField IsDedekindDomain UpperTheory.V
open Formalism.L2.Host

namespace GlobalTheory.HenQ

theorem local_bound (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V)
    (Bf : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (h1 : ∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) (h2 : ∀ x, x ≠ 0 → 0 < (Bf x x).re)
    (h3 : ∀ g x y, Bf (ρ g x) (ρ g y) = Bf x y) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w ρ B) :
    ∀ b ∈ B, ‖(b : ℂ)‖ ≤ ((Formalism.UG.qV E w : ℝ) ^ (n * n + n)) ∧
      ‖((b⁻¹ : ℂˣ) : ℂ)‖ ≤ ((Formalism.UG.qV E w : ℝ) ^ (n * n + n)) ^ n := by
  obtain ⟨x, hx0, hxK, hcard, hT⟩ := hB.exists_vec
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  set q := Formalism.UG.qV E w with hqdef
  have hq2 : 2 ≤ q := GlobalTheory.LFun.one_lt_absNorm w
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)

  have he : ∀ j, 1 ≤ j → j ≤ n → ‖(B.map fun b : ℂˣ => (b : ℂ)).esymm j‖ ≤ (q : ℝ) ^ (n * n) := by
    intro j _ hjn
    obtain ⟨hfin, hc⟩ := GlobalTheory.T.heckeTj_cosets_finite_card_le E w n ϖ hϖ j hjn
    have hh : ∀ g, ‖Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j g‖ ≤ 1 := fun g => by
      unfold Formalism.UG.Tj
      exact (norm_indicator_le_norm_self _ _).trans (by simp)
    have k1 := GlobalTheory.T.norm_heckeEigenvalue_le_card_cosets _ (GlobalTheory.LFun.KGL w n) V ρ Bf h1 h2 h3 _ x _ hh hfin hx0 (hT ϖ hϖ j hjn)
    have k2 : ‖(B.map fun b : ℂˣ => (b : ℂ)).esymm j‖ ≤ ‖GlobalTheory.LFun.satEig q n B j‖ := by
      unfold GlobalTheory.LFun.satEig
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
      refine le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_rpow hq1 ?_)
      have : (((j : ℂ) * ((n : ℂ) - j)) / 2).re = (j : ℝ) * ((n : ℝ) - j) / 2 := by simp
      rw [this]
      have : (j : ℝ) ≤ n := by exact_mod_cast hjn
      positivity
    refine k2.trans (k1.trans ?_)
    refine le_trans ((Nat.cast_le (α := ℝ)).2 hc) ?_
    push_cast
    exact pow_le_pow_right₀ hq1 (Nat.mul_le_mul_left n hjn)
  have hnq : (n : ℝ) ≤ (q : ℝ) ^ n := by
    have : n < 2 ^ n := Nat.lt_two_pow_self
    have h2n : (2 : ℝ) ^ n ≤ (q : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hq2) n
    have : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast this.le
    linarith
  have hup : ∀ b ∈ B, ‖(b : ℂ)‖ ≤ (q : ℝ) ^ (n * n + n) := by
    intro b hb
    refine (GlobalTheory.T.norm_root_le_card_mul_bound_of_esymm_norm_le n B _ hcard (one_le_pow₀ hq1) he b hb).trans ?_
    rw [pow_add, mul_comm]
    exact mul_le_mul_of_nonneg_left hnq (by positivity)
  refine fun b hb => ⟨hup b hb, ?_⟩

  obtain ⟨g, hg⟩ := GlobalTheory.T.heckeTn_scalar_uniformiser_single_translation E w n V ρ ϖ hϖ x hxK
  have hn := hT ϖ hϖ n le_rfl
  have hsat : GlobalTheory.LFun.satEig q n B n = (B.map fun b : ℂˣ => (b : ℂ)).prod := by
    unfold GlobalTheory.LFun.satEig
    simp only [sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul]
    have : (B.map fun b : ℂˣ => (b : ℂ)).card = n := by rw [Multiset.card_map, hcard]
    rw [← this, Multiset.esymm, Multiset.powersetCard_self]
    simp
  rw [hg, hsat] at hn
  have hp : ‖(B.map fun b : ℂˣ => (b : ℂ)).prod‖ = 1 := by
    set c := (B.map fun b : ℂˣ => (b : ℂ)).prod
    have e := h3 g x x
    rw [hn, map_smul, map_smulₛₗ, LinearMap.smul_apply] at e
    have hx : Bf x x ≠ 0 := fun h0 => by simpa [h0] using h2 x hx0
    simp only [smul_eq_mul] at e
    have e2 : starRingEnd ℂ c * c = 1 := by
      refine mul_right_cancel₀ hx ?_
      rw [one_mul]
      nth_rewrite 2 [← e]
      ring
    have e3 : ‖c‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      have : (Complex.normSq c : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self]; exact e2
      exact_mod_cast this
    nlinarith [norm_nonneg c]
  have := GlobalTheory.T.norm_inv_le_pow_card_of_norm_prod_eq_one' B _ (one_le_pow₀ hq1) hup hp b hb
  rwa [hcard] at this

end GlobalTheory.HenQ
