import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModerateGrowthSobolevSizeRightTranslatePolyBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NcardRationalPointsTranslatedCompactLePow
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NormInfSubmultiplicativeLeAdelicHeight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
noncomputable section

open GlobalTheory.KernelSeminorm GlobalTheory.Size GlobalTheory.FockCompare GlobalTheory.ThetaGrowth
open scoped NNReal

namespace GlobalTheory.WeilSobolev

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
  {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem sobO_om_le (hom : IsWeilDatumO ψ S T χS χT om) (hc : Chart θ σ) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (g : GA D S) (h : GA D T) {ρ : ℝ≥0}
    (hρ : ∀ a, ‖mov θ g⁻¹ h⁻¹ (letter a)‖ ≤ ρ) (d : ℕ) :
    ∀ f, IsThetaFunO ψ S T f → sobO ψ θ μ 𝓕 d (om (g, h) f) ≤
      ((1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) *
        (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ) : ℝ≥0) : ℝ≥0∞) ^ d * sobO ψ θ μ 𝓕 d f := by
  induction d with
  | zero =>
    intro f hf
    rw [sobO_zero, sobO_zero, l2O_om_apply_eq_of_isThetaFunO hom hμ h𝓕 hf, pow_zero, one_mul]
  | succ d ih =>
    intro f hf
    have e1 : sobO ψ θ μ 𝓕 (d + 1) (om (g, h) f) =
        l2O μ 𝓕 (om (g, h) f) + ∑ a, sobO ψ θ μ 𝓕 d (heisDer ψ θ a (om (g, h) f)) :=
      Translate.wordSum_succ _ _ d _
    have e2 : ∀ a, sobO ψ θ μ 𝓕 d (heisDer ψ θ a (om (g, h) f)) ≤
        ((1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) *
          (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ) : ℝ≥0) : ℝ≥0∞) ^ d *
        (((Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ : ℝ≥0) : ℝ≥0∞) * sobO ψ θ μ 𝓕 (d + 1) f) := by
      intro a
      rw [← dv_letter hc hom.std a, dv_om hom hc g h (letter a) hf]
      refine (ih _ (theta_dv hc hom.std _ hf)).trans (mul_le_mul_of_nonneg_left ?_ zero_le)
      exact sobO_dvL_le hc hom.std d (hρ a) ⟨f, hf⟩
    have e3 : l2O μ 𝓕 (om (g, h) f) ≤ sobO ψ θ μ 𝓕 (d + 1) f := by
      rw [l2O_om_apply_eq_of_isThetaFunO hom hμ h𝓕 hf]
      exact (sobO_zero (ψ := ψ) (θ := θ)).ge.trans (sobO_mono (Nat.zero_le _))
    rw [e1]
    refine (add_le_add e3 (Finset.sum_le_sum fun a _ => e2 a)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h1 : (1 : ℝ≥0∞) ≤ ((1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) *
        (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ) : ℝ≥0) : ℝ≥0∞) ^ d :=
      one_le_pow₀ (ENNReal.one_le_coe_iff.2 le_self_add)
    rw [pow_succ]
    generalize sobO ψ θ μ 𝓕 (d + 1) f = s at *
    generalize ((1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) *
        (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ) : ℝ≥0) : ℝ≥0∞) ^ d = q at *
    calc s + (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) : ℝ≥0∞) *
          (q * (((Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ : ℝ≥0) : ℝ≥0∞) * s))
        ≤ q * s + (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) : ℝ≥0∞) *
          (q * (((Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ : ℝ≥0) : ℝ≥0∞) * s)) :=
          add_le_add (le_mul_of_one_le_left' h1) le_rfl
      _ = _ := by push_cast; ring

theorem sobO_weil_le_height : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (Φ : WO M X → ℂ) (hΦ : IsThetaFunO ψ (sgn ε M) X Φ)
    (C₁ : Set (GA D M)) (hC₁ : IsCompact C₁)
    (μ : Measure (WO (sgn ε M) X)) (𝓕 : Set (WO (sgn ε M) X)) (hμ : IsCovolOne (ratL X (sgn ε M)) μ 𝓕) (k : ℕ),
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ y ∈ C₁, ∀ h : GA D X,
      (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k (ω (y, h) Φ)).toReal ≤
        C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N := by
  intro D ψ θ hθ ε M X χ χ' ω hω Φ hΦ C₁ hC₁ μ 𝓕 hμ k
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hψ : IsStdChar D ψ (-1) := hω.std
  obtain ⟨B, hB⟩ := (hC₁.image (continuous_ofSgn_symm ε M)).exists_bound_of_continuousOn
    (GlobalTheory.RatCount.continuous_normInf hθ (sgn ε M)).continuousOn
  obtain ⟨CT, hCT⟩ := (GlobalTheory.SmoothForms.normInf_mul_le_and_le_height D θ X).2
  obtain ⟨L, hL, hL0⟩ : ∃ L : ℝ, (∀ a, ‖(letter a : GlobalTheory.FockCompare.RW X (sgn ε M))‖ ≤ L) ∧ 0 ≤ L :=
    ⟨∑ a, ‖(letter a : GlobalTheory.FockCompare.RW X (sgn ε M))‖,
      fun a => Finset.single_le_sum (f := fun a => ‖(letter a : GlobalTheory.FockCompare.RW X (sgn ε M))‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ a), by positivity⟩
  obtain ⟨c0, hc0, hc0'⟩ : ∃ c0 : ℝ, c0 = |CT| * L * |B| ∧ 0 ≤ c0 := ⟨_, rfl, by positivity⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0, K = (Fintype.card (D.what₂.Tau × Fin X.rank × Fin (sgn ε M).rank × Bool) : ℝ≥0) :=
    ⟨_, rfl⟩
  refine ⟨k, (1 + (K : ℝ) * K * c0) ^ k * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Φ).toReal,
    by positivity, fun y hy h => ?_⟩
  have hy' : (ofSgn ε M).symm y ∈ (ofSgn ε M).symm '' C₁ := ⟨y, hy, rfl⟩
  have eω : ω (y, h) Φ = (ω.toSgn ε) ((ofSgn ε M).symm y, h) Φ := by
    simp [WRep.toSgn]
  have hH : (1 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) := by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ X h
  obtain ⟨H, hH'⟩ : ∃ H : ℝ, H = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) := ⟨_, rfl⟩
  rw [← hH'] at hH ⊢
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ≥0, (ρ : ℝ) = c0 * H := ⟨⟨c0 * H, by positivity⟩, rfl⟩
  have hρ : ∀ a, ‖mov θ ((ofSgn ε M).symm y)⁻¹ h⁻¹ (letter a)‖ ≤ ρ := by
    intro a
    refine (norm_mov_le_normInf _ _ _).trans ?_
    rw [inv_inv, GlobalTheory.RatCount.normInf_inv]
    have h1 : normInf θ X h ≤ |CT| * H := (hCT h).trans (by rw [← hH']; exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
    have h2 : normInf θ (sgn ε M) ((ofSgn ε M).symm y) ≤ |B| :=
      (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hB _ hy').trans (le_abs_self _))
    have h3 := GlobalTheory.RatCount.normInf_nonneg θ X h
    have h4 := GlobalTheory.RatCount.normInf_nonneg θ (sgn ε M) ((ofSgn ε M).symm y)
    rw [hρdef]
    calc normInf θ X h * ‖(letter a : GlobalTheory.FockCompare.RW X (sgn ε M))‖ * normInf θ (sgn ε M) ((ofSgn ε M).symm y)
        ≤ (|CT| * H) * L * |B| := by gcongr; exact hL a
      _ = c0 * H := by rw [hc0]; ring
  have key := GlobalTheory.WeilSobolev.sobO_om_le hω hc hμ.1 hμ.2.1 ((ofSgn ε M).symm y) h hρ k Φ hΦ
  rw [eω]
  have hs := sobO_ne_top hψ hθ hμ.1 hμ.2.1 hΦ k
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hs) key).trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, ← hK]
  have hQ : ((1 + K * (K * ρ) : ℝ≥0) : ℝ) ≤ (1 + (K : ℝ) * K * c0) * H := by
    push_cast
    rw [hρdef]
    have : (0 : ℝ) ≤ K := K.2
    nlinarith [mul_nonneg (mul_nonneg this this) hc0']
  calc _ ≤ ((1 + (K : ℝ) * K * c0) * H) ^ k * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Φ).toReal :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (NNReal.coe_nonneg _) hQ k) ENNReal.toReal_nonneg
    _ = (1 + (K : ℝ) * K * c0) ^ k * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Φ).toReal * H ^ k := by
        rw [mul_pow]; ring

end GlobalTheory.WeilSobolev

end
