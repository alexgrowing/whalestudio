import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualDirectionDerivativeMixedCoordinateBound
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergSupSobolevSeminormThetaLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsBis
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.MixWeight

theorem trace_mul_single {m r : ℕ} (M : Matrix (Fin r) (Fin m) ℂ) (i : Fin m) (j : Fin r) (c : ℂ) :
    (M * Matrix.single i j c).trace = M j i * c := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single j (fun b _ hb => Finset.sum_eq_zero fun c' _ => by
    rw [if_neg fun h => hb h.2.symm, mul_zero]) (by simp)]
  rw [Finset.sum_eq_single i (fun b _ hb => by rw [if_neg fun h => hb h.1.symm, mul_zero]) (by simp)]
  simp

theorem norm_le_forms {m r : ℕ} (B : Matrix (Fin r) (Fin m) ℂ) (ξ : ℂ) (hξ : ξ ≠ 0) (i : Fin m) (j : Fin r) :
    ‖B j i‖ ≤ ‖ξ‖⁻¹ * ∑ b : Bool, |2 * (ξ * (B * Matrix.single i j (if b then Complex.I else 1)).trace).re| := by
  have hξn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, ite_true, ite_false, trace_mul_single, mul_one]
  rw [le_inv_mul_iff₀ hξn, ← norm_mul]
  have h1 := Complex.norm_le_abs_re_add_abs_im (ξ * B j i)
  have e1 : |2 * (ξ * (B j i * Complex.I)).re| = 2 * |(ξ * B j i).im| := by
    rw [← mul_assoc, Complex.mul_I_re, abs_mul, abs_neg, abs_two]
  have e2 : |2 * (ξ * B j i).re| = 2 * |(ξ * B j i).re| := by rw [abs_mul, abs_two]
  rw [e1, e2]
  linarith [abs_nonneg (ξ * B j i).re, abs_nonneg (ξ * B j i).im]

theorem sum_norm_le {m r : ℕ} (G : Matrix (Fin m) (Fin m) ℂ) (hG : IsUnit G.det) (ξ : ℂ) (hξ : ξ ≠ 0) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : Matrix (Fin m) (Fin r) ℂ,
      ∑ k, ∑ j, ‖x k j‖ ≤ A * ∑ i : Fin m, ∑ j : Fin r, ∑ b : Bool,
        |2 * (ξ * (xᴴ * G * Matrix.single i j (if b then Complex.I else 1)).trace).re| := by
  have hg0 : 0 ≤ ∑ i, ∑ k, ‖G⁻¹ i k‖ := by positivity
  refine ⟨m * (∑ i, ∑ k, ‖G⁻¹ i k‖) * ‖ξ‖⁻¹, by positivity, fun x => ?_⟩
  have hx : x = (xᴴ * G * G⁻¹)ᴴ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one, Matrix.conjTranspose_conjTranspose]
  have hxkj : ∀ k j, ‖x k j‖ ≤ (∑ i, ∑ k, ‖G⁻¹ i k‖) * ∑ i, ‖(xᴴ * G) j i‖ := by
    intro k j
    rw [hx, Matrix.conjTranspose_apply, norm_star, Matrix.mul_apply, ← hx]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact (Finset.single_le_sum (f := fun k' => ‖G⁻¹ i k'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun i' => ∑ k', ‖G⁻¹ i' k'‖) (fun _ _ => by positivity) (Finset.mem_univ i))
  have key : ∑ k, ∑ j, ‖x k j‖ ≤ m * (∑ i, ∑ k, ‖G⁻¹ i k‖) * ‖ξ‖⁻¹ * ∑ i : Fin m, ∑ j : Fin r, ∑ b : Bool,
      |2 * (ξ * (xᴴ * G * Matrix.single i j (if b then Complex.I else 1)).trace).re| := by
    calc ∑ k, ∑ j, ‖x k j‖ ≤ ∑ _k : Fin m, ∑ j, (∑ i, ∑ k, ‖G⁻¹ i k‖) * ∑ i, ‖(xᴴ * G) j i‖ :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun j _ => hxkj k j
      _ = m * (∑ i, ∑ k, ‖G⁻¹ i k‖) * ∑ j, ∑ i, ‖(xᴴ * G) j i‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, mul_assoc]
      _ = m * (∑ i, ∑ k, ‖G⁻¹ i k‖) * ∑ i, ∑ j, ‖(xᴴ * G) j i‖ := by congr 1; exact Finset.sum_comm
      _ ≤ m * (∑ i, ∑ k, ‖G⁻¹ i k‖) * ∑ i, ∑ j, ‖ξ‖⁻¹ * ∑ b : Bool,
            |2 * (ξ * (xᴴ * G * Matrix.single i j (if b then Complex.I else 1)).trace).re| := by
          gcongr with i _ j _
          exact norm_le_forms _ ξ hξ i j
      _ = _ := by
          rw [mul_assoc ((m : ℝ) * ∑ i, ∑ k, ‖G⁻¹ i k‖) ‖ξ‖⁻¹, Finset.mul_sum (a := ‖ξ‖⁻¹)]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          rfl
  exact key

end GlobalTheory.MixWeight

namespace GlobalTheory.MixWeight

open GlobalTheory.MixModel

variable {D : D7}

theorem enorm_mixS_le' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V V₀ W : HSp D} {ρ : ℕ}
    (d : HypDec V V₀ ρ) (v : GlobalTheory.Unf.VolM D W.rank ρ) (φ : WO V W → ℂ) (x : Mx D W.rank ρ) (w : WO V₀ W) :
    ‖d.mixS W ψ v.μ v.𝓕 φ x w‖ₑ ≤ GlobalTheory.HeisTaylor.supN φ := by
  simp only [HypDec.mixS, HypDec.integrandS_eq]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ a in v.𝓕, ‖ψ (symplOH V W (d.extY W a) (d.extX W x)) * φ (d.extY W a + d.extX W x + d.ext0 W w)‖ₑ ∂v.μ
      ≤ ∫⁻ _ in v.𝓕, GlobalTheory.HeisTaylor.supN φ ∂v.μ := by
        refine lintegral_mono fun a => ?_
        rw [enorm_mul, ← ofReal_norm (ψ _), hψ.1.2.1, ENNReal.ofReal_one, one_mul]
        exact GlobalTheory.HeisTaylor.enorm_le_supN φ _
    _ = _ := by rw [setLIntegral_const, v.covol.2.2, mul_one]

theorem one_add_pow_le {L : ℝ} (hL : 0 ≤ L) (N : ℕ) : (1 + L) ^ N ≤ 2 ^ N * (1 + L ^ N) := by
  first
  | exact @_root_.GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le
  | exact _root_.GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le
  | (apply _root_.GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OneAddPowBoundTwistedOperators.one_add_pow_le ..)

theorem mixS_weight_le : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (V X S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec V S₀ r) (μ' : Measure (Mx D X.rank r))
    (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' → ∀ N : ℕ,
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ Ψ : WO V X → ℂ, IsThetaFunO ψ V X Ψ → ∀ x : Mx D X.rank r,
      ‖d.mixS X ψ μ' 𝓕' Ψ x 0‖ₑ * ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖) ^ N) ≤
        ENNReal.ofReal C * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) GlobalTheory.HeisTaylor.supN k Ψ := by
  intro D ψ hψ θ hθ V X S₀ r d μ' 𝓕' hμ N
  let v : GlobalTheory.Unf.VolM D X.rank r := ⟨μ', 𝓕', hμ⟩
  let zA : D.what₂.Tau × Fin X.rank × Fin r × Bool → Matrix (Fin X.rank) (Fin r) ℂ :=
    fun a => Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)
  let ℓ : D.what₂.Tau × Fin X.rank × Fin r × Bool → Mx D X.rank r → ℝ := fun a x =>
    |2 * (tauE D a.1 D.host.xi0 * ((compAt θ a.1 x)ᴴ * gramAt D X a.1 * zA a).trace).re|
  choose Z hZ using fun a : D.what₂.Tau × Fin X.rank × Fin r × Bool =>
    GlobalTheory.Unf.norm_mixS_dRho_ge D ψ hψ θ hθ V S₀ X r d v a.1 (zA a)
  have laws := GlobalTheory.Unf.SupFin.supSob_laws D ψ hψ θ hθ V X
  choose C hC using fun a : D.what₂.Tau × Fin X.rank × Fin r × Bool => (laws.2.1 a.1 (Z a)).2
  let K : NNReal := ∑ a, C a
  have hL0 : ∀ x, 0 ≤ ∑ a, ℓ a x := fun x => Finset.sum_nonneg fun a _ => abs_nonneg _

  have hpow : ∀ n : ℕ, ∀ f : WO V X → ℂ, IsThetaFunO ψ V X f → ∀ x,
      ENNReal.ofReal ((∑ a, ℓ a x) ^ n) * ‖d.mixS X ψ μ' 𝓕' f x 0‖ₑ ≤
        ((K ^ n : NNReal) : ENNReal) * GlobalTheory.Unf.supSob ψ θ n f := by
    intro n
    induction n with
    | zero =>
      intro f hf x
      rw [pow_zero, ENNReal.ofReal_one, one_mul, pow_zero, ENNReal.coe_one, one_mul]
      exact (enorm_mixS_le' hψ d v f x 0).trans (GlobalTheory.Size.wordSum_zero _ _ _).ge
    | succ n ih =>
      intro f hf x
      have step : ∀ a, ENNReal.ofReal ((∑ a, ℓ a x) ^ n) * (ENNReal.ofReal (ℓ a x) * ‖d.mixS X ψ μ' 𝓕' f x 0‖ₑ) ≤
          ((K ^ n : NNReal) : ENNReal) * ((C a : ENNReal) * GlobalTheory.Unf.supSob ψ θ (n + 1) f) := by
        intro a
        have hg := GlobalTheory.OrientedHeis.theta_dRho hθ hψ a.1 (Z a) hf
        have h1 : ENNReal.ofReal (ℓ a x) * ‖d.mixS X ψ μ' 𝓕' f x 0‖ₑ ≤
            ‖d.mixS X ψ μ' 𝓕' (dRho (heisO ψ V X) θ a.1 (Z a) f) x 0‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (abs_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (hZ a f hf x 0)
        calc _ ≤ ENNReal.ofReal ((∑ a, ℓ a x) ^ n) *
              ‖d.mixS X ψ μ' 𝓕' (dRho (heisO ψ V X) θ a.1 (Z a) f) x 0‖ₑ := by gcongr
          _ ≤ ((K ^ n : NNReal) : ENNReal) * GlobalTheory.Unf.supSob ψ θ n (dRho (heisO ψ V X) θ a.1 (Z a) f) := ih _ hg x
          _ ≤ _ := by gcongr; exact hC a n f hf
      calc ENNReal.ofReal ((∑ a, ℓ a x) ^ (n + 1)) * ‖d.mixS X ψ μ' 𝓕' f x 0‖ₑ
          = ∑ a, ENNReal.ofReal ((∑ a, ℓ a x) ^ n) * (ENNReal.ofReal (ℓ a x) * ‖d.mixS X ψ μ' 𝓕' f x 0‖ₑ) := by
            rw [pow_succ, ENNReal.ofReal_mul (pow_nonneg (hL0 x) n),
              ENNReal.ofReal_sum_of_nonneg (fun a _ => abs_nonneg _), Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun a _ => ?_
            ring
        _ ≤ ∑ a, ((K ^ n : NNReal) : ENNReal) * ((C a : ENNReal) * GlobalTheory.Unf.supSob ψ θ (n + 1) f) :=
            Finset.sum_le_sum fun a _ => step a
        _ = ((K ^ (n + 1) : NNReal) : ENNReal) * GlobalTheory.Unf.supSob ψ θ (n + 1) f := by
            rw [← Finset.mul_sum, ← Finset.sum_mul, pow_succ]
            simp only [K, ENNReal.coe_mul, ENNReal.ofNNReal_finsetSum]
            ring

  have hG : ∀ τ : D.what₂.Tau, IsUnit (gramAt D X τ).det := fun τ => by
    have e : (gramAt D X τ).det = tauE D τ (HSpace.gram X).det := by rw [RingHom.map_det]; rfl
    rw [isUnit_iff_ne_zero, e]
    exact (map_ne_zero_iff _ (tauE D τ).injective).2 (gram_det_ne X)
  have hξ : ∀ τ : D.what₂.Tau, tauE D τ D.host.xi0 ≠ 0 := fun τ =>
    (map_ne_zero_iff _ (tauE D τ).injective).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  choose A hA0 hA using fun τ : D.what₂.Tau => sum_norm_le (r := r) (gramAt D X τ) (hG τ) _ (hξ τ)
  have hAt : 0 ≤ ∑ τ, A τ := Finset.sum_nonneg fun τ _ => hA0 τ
  have hrs : ∀ x : Mx D X.rank r, ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖ ≤ (∑ τ, A τ) * ∑ a, ℓ a x := by
    intro x
    have e : ∑ a, ℓ a x = ∑ τ, ∑ i : Fin X.rank, ∑ j : Fin r, ∑ b : Bool, ℓ (τ, i, j, b) x := by
      simp only [Fintype.sum_prod_type]
    rw [e, Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => (hA τ (compAt θ τ x)).trans ?_
    refine mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := A) (fun τ _ => hA0 τ) (Finset.mem_univ τ)) ?_
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨N, (1 + ∑ τ, A τ) ^ N * 2 ^ N * (1 + ((K ^ N : NNReal) : ℝ)), by positivity, fun Ψ hΨ x => ?_⟩
  show _ ≤ _ * GlobalTheory.Unf.supSob ψ θ N Ψ
  have hLn := hL0 x
  have hb : (1 + ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖) ^ N ≤
      (1 + ∑ τ, A τ) ^ N * 2 ^ N * (1 + (∑ a, ℓ a x) ^ N) := by
    have h1 : 1 + ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖ ≤ (1 + ∑ τ, A τ) * (1 + ∑ a, ℓ a x) := by
      nlinarith [hrs x]
    calc (1 + ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖) ^ N ≤ ((1 + ∑ τ, A τ) * (1 + ∑ a, ℓ a x)) ^ N :=
          pow_le_pow_left₀ (by positivity) h1 N
      _ = (1 + ∑ τ, A τ) ^ N * (1 + ∑ a, ℓ a x) ^ N := mul_pow _ _ _
      _ ≤ (1 + ∑ τ, A τ) ^ N * (2 ^ N * (1 + (∑ a, ℓ a x) ^ N)) := by gcongr; exact one_add_pow_le hLn N
      _ = _ := by ring
  have h0 := hpow 0 Ψ hΨ x
  have hN := hpow N Ψ hΨ x
  rw [pow_zero, ENNReal.ofReal_one, one_mul, pow_zero, ENNReal.coe_one, one_mul] at h0
  have hmono : GlobalTheory.Unf.supSob ψ θ 0 Ψ ≤ GlobalTheory.Unf.supSob ψ θ N Ψ := GlobalTheory.Size.wordSum_mono (Nat.zero_le N) Ψ
  calc ‖d.mixS X ψ μ' 𝓕' Ψ x 0‖ₑ * ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖) ^ N)
      ≤ ‖d.mixS X ψ μ' 𝓕' Ψ x 0‖ₑ * ENNReal.ofReal ((1 + ∑ τ, A τ) ^ N * 2 ^ N * (1 + (∑ a, ℓ a x) ^ N)) := by
        gcongr
    _ = ENNReal.ofReal ((1 + ∑ τ, A τ) ^ N * 2 ^ N) * (‖d.mixS X ψ μ' 𝓕' Ψ x 0‖ₑ +
          ENNReal.ofReal ((∑ a, ℓ a x) ^ N) * ‖d.mixS X ψ μ' 𝓕' Ψ x 0‖ₑ) := by
        rw [ENNReal.ofReal_mul (p := (1 + ∑ τ, A τ) ^ N * 2 ^ N) (by positivity),
          ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]
        ring
    _ ≤ ENNReal.ofReal ((1 + ∑ τ, A τ) ^ N * 2 ^ N) * (GlobalTheory.Unf.supSob ψ θ N Ψ +
          ((K ^ N : NNReal) : ENNReal) * GlobalTheory.Unf.supSob ψ θ N Ψ) :=
        mul_le_mul_of_nonneg_left (add_le_add (h0.trans hmono) hN) zero_le
    _ = ENNReal.ofReal ((1 + ∑ τ, A τ) ^ N * 2 ^ N * (1 + ((K ^ N : NNReal) : ℝ))) * GlobalTheory.Unf.supSob ψ θ N Ψ := by
        rw [ENNReal.ofReal_mul (p := (1 + ∑ τ, A τ) ^ N * 2 ^ N) (by positivity),
          ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal]
        ring

end GlobalTheory.MixWeight

end
