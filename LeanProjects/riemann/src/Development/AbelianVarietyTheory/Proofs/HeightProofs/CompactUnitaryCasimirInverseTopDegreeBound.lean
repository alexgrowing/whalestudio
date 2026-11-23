import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivative
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCoordFunMulEqSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

variable {n : ℕ}

theorem casInv_expK_zero {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    expK ε Y 0 = 1 := by
  have h := group_exponential_facts n ε Y hY.1
  apply Subtype.ext
  rw [(h.2.2.2 hY).1 0, h.1]
  rfl

theorem casInv_integrable {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] {f : KG ε → E}
    (hf : Continuous f) : Integrable f (muK ε) := by
  haveI : IsFiniteMeasure (muK ε) := ⟨isCompact_univ.measure_lt_top⟩
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem casInv_rder_zero (ε : Fin n → Bool) (L : List (Matrix (Fin n) (Fin n) ℂ)) :
    rder ε L (0 : KG ε → ℂ) = 0 := by
  induction L with
  | nil => rfl
  | cons Y L ih =>
    funext k
    rw [rder_cons, ih]
    simp

theorem casInv_rder_pair (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (φ : KG ε → ℂ) :
    rder ε [Y, Y] φ = rder ε [Y] (rder ε [Y] φ) := rfl

theorem casInv_rder_mem {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) {d : ℕ}
    {φ : KG ε → ℂ} (hφ : φ ∈ polyV ε d) : rder ε [Y] φ ∈ polyV ε d :=
  (rder_mem_and_hasDerivAt ε d φ hφ Y hY).1

theorem casInv_rder2_mem {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) {d : ℕ}
    {φ : KG ε → ℂ} (hφ : φ ∈ polyV ε d) : rder ε [Y, Y] φ ∈ polyV ε d := by
  rw [casInv_rder_pair]
  exact casInv_rder_mem hY (casInv_rder_mem hY hφ)

theorem casInv_rder_add {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) {d : ℕ}
    {φ ψ : KG ε → ℂ} (hφ : φ ∈ polyV ε d) (hψ : ψ ∈ polyV ε d) :
    rder ε [Y] (φ + ψ) = rder ε [Y] φ + rder ε [Y] ψ := by
  funext k
  exact ((rder_mem_and_hasDerivAt ε d _ (add_mem hφ hψ) Y hY).2 k).unique
    (((rder_mem_and_hasDerivAt ε d φ hφ Y hY).2 k).add ((rder_mem_and_hasDerivAt ε d ψ hψ Y hY).2 k))

theorem casInv_rder_smul {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) {d : ℕ}
    {φ : KG ε → ℂ} (hφ : φ ∈ polyV ε d) (c : ℂ) :
    rder ε [Y] (c • φ) = c • rder ε [Y] φ := by
  funext k
  exact ((rder_mem_and_hasDerivAt ε d _ (Submodule.smul_mem _ c hφ) Y hY).2 k).unique
    (((rder_mem_and_hasDerivAt ε d φ hφ Y hY).2 k).const_mul c)

theorem casInv_rder_star {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) {d : ℕ}
    {φ : KG ε → ℂ} (hφ : φ ∈ polyV ε d) :
    rder ε [Y] (fun k => star (φ k)) = fun k => star (rder ε [Y] φ k) := by
  funext k
  exact ((rder_mem_and_hasDerivAt ε d _ (star_mem hφ) Y hY).2 k).unique
    ((rder_mem_and_hasDerivAt ε d φ hφ Y hY).2 k).star

theorem casInv_byParts {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) {d : ℕ}
    {a b : KG ε → ℂ} (ha : a ∈ polyV ε d) (hb : b ∈ polyV ε d) :
    ∫ k, rder ε [Y] a k * b k ∂(muK ε) = -∫ k, a k * rder ε [Y] b k ∂(muK ε) := by
  have hra := rder_mem_and_hasDerivAt ε d a ha Y hY
  have hrb := rder_mem_and_hasDerivAt ε d b hb Y hY
  have ca := continuous_of_mem ha
  have cb := continuous_of_mem hb
  have cra := continuous_of_mem hra.1
  have crb := continuous_of_mem hrb.1
  have h0 := casInv_expK_zero hY
  have key := compact_integration_by_parts n ε ℂ (fun k => a k * b k)
    (fun k => rder ε [Y] a k * b k + a k * rder ε [Y] b k) Y hY
    (ca.mul cb) ((cra.mul cb).add (ca.mul crb)) (fun k => by
      have := (hra.2 k).fun_mul (hrb.2 k)
      simpa only [h0, mul_one] using this)
  rw [integral_add (casInv_integrable (f := fun k => rder ε [Y] a k * b k) (cra.mul cb))
    (casInv_integrable (f := fun k => a k * rder ε [Y] b k) (ca.mul crb))] at key
  exact eq_neg_of_add_eq_zero_left key

end GlobalTheory.KFourier

namespace GlobalTheory.KFourier

open MeasureTheory

variable {n : ℕ}

section Lap

variable {ε : Fin n → Bool} {r : ℕ} (X : Fin r → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ j, inK ε (X j))
include hX

theorem casInv_lap_mem {d : ℕ} {φ : KG ε → ℂ} (hφ : φ ∈ polyV ε d) :
    (∑ j, rder ε [X j, X j] φ) ∈ polyV ε d :=
  Submodule.sum_mem _ fun j _ => casInv_rder2_mem (hX j) hφ

theorem casInv_lap_add {d : ℕ} {φ ψ : KG ε → ℂ} (hφ : φ ∈ polyV ε d) (hψ : ψ ∈ polyV ε d) :
    (∑ j, rder ε [X j, X j] (φ + ψ)) = (∑ j, rder ε [X j, X j] φ) + ∑ j, rder ε [X j, X j] ψ := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [casInv_rder_pair, casInv_rder_pair, casInv_rder_pair, casInv_rder_add (hX j) hφ hψ,
    casInv_rder_add (hX j) (casInv_rder_mem (hX j) hφ) (casInv_rder_mem (hX j) hψ)]

theorem casInv_lap_smul {d : ℕ} {φ : KG ε → ℂ} (hφ : φ ∈ polyV ε d) (c : ℂ) :
    (∑ j, rder ε [X j, X j] (c • φ)) = c • ∑ j, rder ε [X j, X j] φ := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [casInv_rder_pair, casInv_rder_pair, casInv_rder_smul (hX j) hφ,
    casInv_rder_smul (hX j) (casInv_rder_mem (hX j) hφ)]

theorem casInv_lap_symm {d : ℕ} {a b : KG ε → ℂ} (ha : a ∈ polyV ε d) (hb : b ∈ polyV ε d) :
    ∫ k, a k * (∑ j, rder ε [X j, X j] b) k ∂(muK ε) =
      ∫ k, (∑ j, rder ε [X j, X j] a) k * b k ∂(muK ε) := by
  simp only [Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finset_sum _ (fun j _ => casInv_integrable (f := fun k => a k * rder ε [X j, X j] b k)
      ((continuous_of_mem ha).mul (continuous_of_mem (casInv_rder2_mem (hX j) hb)))),
    integral_finset_sum _ (fun j _ => casInv_integrable (f := fun k => rder ε [X j, X j] a k * b k)
      ((continuous_of_mem (casInv_rder2_mem (hX j) ha)).mul (continuous_of_mem hb)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [casInv_rder_pair, casInv_rder_pair]
  have h1 := casInv_byParts (hX j) ha (casInv_rder_mem (hX j) hb)
  have h2 := casInv_byParts (hX j) (casInv_rder_mem (hX j) ha) hb
  rw [h2, h1, neg_neg]

theorem casInv_lap_low {i : ℕ} {q : KG ε → ℂ} (hq : q ∈ lowV ε i) :
    (∑ j, rder ε [X j, X j] q) ∈ lowV ε i := by
  cases i with
  | zero =>
    rw [lowV, Submodule.mem_bot] at hq ⊢
    subst hq
    simp only [casInv_rder_zero, Finset.sum_const_zero]
  | succ d => exact casInv_lap_mem X hX hq

theorem casInv_energy {d : ℕ} {p : KG ε → ℂ} (hp : p ∈ polyV ε d) :
    ∫ k, (∑ j, rder ε [X j, X j] p) k * star (p k) ∂(muK ε) =
      -(((∑ j, ∫ k, ‖rder ε [X j] p k‖ ^ 2 ∂(muK ε) : ℝ)) : ℂ) := by
  simp only [Finset.sum_apply, Finset.sum_mul]
  rw [integral_finset_sum _ (fun j _ => casInv_integrable (f := fun k => rder ε [X j, X j] p k * star (p k))
      ((continuous_of_mem (casInv_rder2_mem (hX j) hp)).mul (continuous_star.comp (continuous_of_mem hp))))]
  push_cast
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [casInv_rder_pair]
  have h1 := casInv_byParts (hX j) (casInv_rder_mem (hX j) hp) (star_mem hp)
  simp only [casInv_rder_star (hX j) hp] at h1
  rw [h1, ← integral_complex_ofReal]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  have := Complex.mul_conj' (rder ε [X j] p k)
  simp only [Complex.ofReal_pow]
  exact this

end Lap

end GlobalTheory.KFourier

namespace GlobalTheory.KFourier

open MeasureTheory

variable {n : ℕ}

theorem casInv_eq_zero {ε : Fin n → Bool} {p : KG ε → ℂ} (hp : Continuous p)
    (h : ∫ k, ‖p k‖ ^ 2 ∂(muK ε) = 0) : p = 0 := by
  have hc : Continuous fun k => ‖p k‖ ^ 2 := (continuous_norm.comp hp).pow 2
  have h2 := (integral_eq_zero_iff_of_nonneg (fun k => sq_nonneg ‖p k‖) (casInv_integrable hc)).1 h
  have h3 := (Continuous.ae_eq_iff_eq (muK ε) hc (continuous_const (y := (0 : ℝ)))).1 h2
  funext k
  have : ‖p k‖ ^ 2 = 0 := congrFun h3 k
  simpa using this

def casInvSpace (ε : Fin n → Bool) (i : ℕ) : Submodule ℂ (KG ε → ℂ) where
  carrier := {p | p ∈ polyV ε i ∧ ∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨add_mem ha hb, fun q hq => ?_⟩
    have cq := continuous_of_mem (lowV_le ε i hq)
    simp only [Pi.add_apply, mul_add]
    rw [integral_add (casInv_integrable (f := fun k => q k * a k) (cq.mul (continuous_of_mem ha)))
      (casInv_integrable (f := fun k => q k * b k) (cq.mul (continuous_of_mem hb))), ha' q hq, hb' q hq,
      add_zero]
  zero_mem' := ⟨Submodule.zero_mem _, fun q _ => by simp⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨Submodule.smul_mem _ c ha, fun q hq => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (fun k => q k * (c * a k)) = fun k => c * (q k * a k) from funext fun k => by ring,
      integral_const_mul, ha' q hq, mul_zero]

instance casInvSpace_fd (ε : Fin n → Bool) (i : ℕ) : FiniteDimensional ℂ (casInvSpace ε i) :=
  Submodule.finiteDimensional_of_le (fun _ hp => hp.1 : casInvSpace ε i ≤ polyV ε i)

def casInvOp (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ j, inK ε (X j))
    (i : ℕ) : casInvSpace ε i →ₗ[ℂ] casInvSpace ε i where
  toFun p := ⟨∑ j, rder ε [X j, X j] (p : KG ε → ℂ), casInv_lap_mem X hX p.2.1, fun q hq => by
      rw [casInv_lap_symm X hX (lowV_le ε i hq) p.2.1]
      exact p.2.2 _ (casInv_lap_low X hX hq)⟩
  map_add' a b := Subtype.ext (casInv_lap_add X hX a.2.1 b.2.1)
  map_smul' c a := Subtype.ext (casInv_lap_smul X hX a.2.1 c)

theorem casInv_coercive {ε : Fin n → Bool} {r : ℕ} (X : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ j, inK ε (X j)) {i : ℕ} {l : ℝ} (hl : 0 < l)
    (hyp : ∀ p ∈ polyV ε i, (∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) →
      l * ∫ k, ‖p k‖ ^ 2 ∂(muK ε) ≤ ∑ j, ∫ k, ‖rder ε [X j] p k‖ ^ 2 ∂(muK ε))
    {p : KG ε → ℂ} (hp : p ∈ casInvSpace ε i) :
    l ^ 2 * ∫ k, ‖p k‖ ^ 2 ∂(muK ε) ≤ ∫ k, ‖(∑ j, rder ε [X j, X j] p) k‖ ^ 2 ∂(muK ε) := by
  have hS := hyp p hp.1 hp.2
  have hE := casInv_energy X hX hp.1
  set S := ∑ j, ∫ k, ‖rder ε [X j] p k‖ ^ 2 ∂(muK ε)
  set L := ∑ j, rder ε [X j, X j] p with hL
  have cp := continuous_of_mem hp.1
  have cL : Continuous L := continuous_of_mem (casInv_lap_mem X hX hp.1)
  have h1 : S ≤ ∫ k, ‖L k‖ * ‖p k‖ ∂(muK ε) := by
    calc S ≤ ‖(S : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self S
      _ = ‖∫ k, L k * star (p k) ∂(muK ε)‖ := by rw [hE, norm_neg]
      _ ≤ ∫ k, ‖L k * star (p k)‖ ∂(muK ε) := norm_integral_le_integral_norm _
      _ = ∫ k, ‖L k‖ * ‖p k‖ ∂(muK ε) := by simp only [norm_mul, norm_star]
  have h2 : 2 * l * ∫ k, ‖L k‖ * ‖p k‖ ∂(muK ε) ≤
      ∫ k, ‖L k‖ ^ 2 ∂(muK ε) + l ^ 2 * ∫ k, ‖p k‖ ^ 2 ∂(muK ε) := by
    have cLn := continuous_norm.comp cL
    have cpn := continuous_norm.comp cp
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (casInv_integrable (f := fun k => ‖L k‖ ^ 2) (cLn.pow 2))
        (casInv_integrable (f := fun k => l ^ 2 * ‖p k‖ ^ 2) (continuous_const.mul (cpn.pow 2)))]
    refine integral_mono (casInv_integrable (f := fun k => 2 * l * (‖L k‖ * ‖p k‖)) (continuous_const.mul (cLn.mul cpn)))
      (casInv_integrable (f := fun k => ‖L k‖ ^ 2 + l ^ 2 * ‖p k‖ ^ 2) ((cLn.pow 2).add (continuous_const.mul (cpn.pow 2)))) (fun k => ?_)
    have := sq_nonneg (‖L k‖ - l * ‖p k‖)
    simp only
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left (hS.trans h1) (by positivity : (0 : ℝ) ≤ 2 * l)
  nlinarith

theorem casimir_inverse_bound : ∀ {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n), (∀ j, inK ε (X j)) →
    ∀ (i : ℕ) (l : ℝ), 0 < l →
    (∀ p ∈ polyV ε i, (∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) →
      l * ∫ k, ‖p k‖ ^ 2 ∂(muK ε) ≤ ∑ j, ∫ k, ‖rder ε [X j] p k‖ ^ 2 ∂(muK ε)) →
    ∀ (M : ℕ) (e : KG ε → ℂ), e ∈ polyV ε i → (∀ q ∈ lowV ε i, ∫ k, q k * e k ∂(muK ε) = 0) →
    ∃ s ∈ polyV ε i, (fun φ : KG ε → ℂ => ∑ j, rder ε [X j, X j] φ)^[M] s = e ∧
      ∫ k, ‖s k‖ ^ 2 ∂(muK ε) ≤ (l ^ (2 * M))⁻¹ * ∫ k, ‖e k‖ ^ 2 ∂(muK ε) := by
  intro n ε r X hX i l hl hyp M e he heo
  have hinj : Function.Injective (casInvOp ε X hX i) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    have h0 : (∑ j, rder ε [X j, X j] (p : KG ε → ℂ)) = 0 := congrArg Subtype.val hp
    have h1 := casInv_coercive X hX hl hyp p.2
    have hz : ∫ k, ‖(0 : KG ε → ℂ) k‖ ^ 2 ∂(muK ε) = 0 := by simp
    rw [h0, hz] at h1
    have hA0 : 0 ≤ ∫ k, ‖(p : KG ε → ℂ) k‖ ^ 2 ∂(muK ε) := integral_nonneg fun k => sq_nonneg _
    have hl2 : 0 < l ^ 2 := by positivity
    have hA : ∫ k, ‖(p : KG ε → ℂ) k‖ ^ 2 ∂(muK ε) = 0 := le_antisymm (by nlinarith) hA0
    exact Subtype.ext (casInv_eq_zero (continuous_of_mem p.2.1) hA)
  have hbij : Function.Bijective (casInvOp ε X hX i) :=
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have hcoe : ∀ (m : ℕ) (p : casInvSpace ε i),
      (((casInvOp ε X hX i)^[m] p : casInvSpace ε i) : KG ε → ℂ) =
        (fun φ : KG ε → ℂ => ∑ j, rder ε [X j, X j] φ)^[m] (p : KG ε → ℂ) := by
    intro m
    induction m with
    | zero => intro p; rfl
    | succ m ih =>
      intro p
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih p]
      rfl
  have hbound : ∀ (m : ℕ) (p : casInvSpace ε i),
      l ^ (2 * m) * ∫ k, ‖(p : KG ε → ℂ) k‖ ^ 2 ∂(muK ε) ≤
        ∫ k, ‖(((casInvOp ε X hX i)^[m] p : casInvSpace ε i) : KG ε → ℂ) k‖ ^ 2 ∂(muK ε) := by
    intro m
    induction m with
    | zero => intro p; simp
    | succ m ih =>
      intro p
      rw [Function.iterate_succ_apply']
      have h1 := casInv_coercive X hX hl hyp ((casInvOp ε X hX i)^[m] p).2
      have h2 := ih p
      have hl2 : (0 : ℝ) ≤ l ^ 2 := by positivity
      calc l ^ (2 * (m + 1)) * ∫ k, ‖(p : KG ε → ℂ) k‖ ^ 2 ∂(muK ε)
          = l ^ 2 * (l ^ (2 * m) * ∫ k, ‖(p : KG ε → ℂ) k‖ ^ 2 ∂(muK ε)) := by ring
        _ ≤ l ^ 2 * ∫ k, ‖(((casInvOp ε X hX i)^[m] p : casInvSpace ε i) : KG ε → ℂ) k‖ ^ 2 ∂(muK ε) :=
          mul_le_mul_of_nonneg_left h2 hl2
        _ ≤ _ := h1
  obtain ⟨s, hs⟩ := (hbij.iterate M).2 ⟨e, he, heo⟩
  refine ⟨s, s.2.1, ?_, ?_⟩
  · rw [← hcoe, hs]
  · have h := hbound M s
    rw [hs] at h
    rw [le_inv_mul_iff₀ (by positivity)]
    exact h

end GlobalTheory.KFourier
