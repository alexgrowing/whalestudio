import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalDoublingSectionGraphDiagonalEqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightInvariantEqSumOpenSubgroupCosetsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BiInvariantReplaceSameDoubleCosetSumsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SummableNormCosetOutStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsZonalSphericalFunctionUnramifiedUnitaryStatement
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ZetaSumU

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem cartan_complete : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ g : GU σ n, ∃ (d : Fin n → ℤ) (t : GU σ n),
      t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) ∧ ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g = k₁ * t * k₂ := by
  intro L _ _ _ ϖ σ q n hU g
  obtain ⟨d, hd, a, ha, b, hb, e⟩ := GlobalTheory.LFun.UnitaryDiv.exists_good_div L ϖ σ q n hU g
  obtain ⟨t, ht⟩ := GlobalTheory.InertThetaCompare.exists_diag hU hd
  obtain ⟨k₁, h₁, k₂, h₂, e'⟩ := GlobalTheory.T.unitaryDoubleCoset_of_GLintDoubleCoset L ϖ σ q n hU t g a b ha hb (Units.ext (by rw [e, ← ht]; rfl))
  exact ⟨fun i => d.getD i.1 0, t, ht, k₁, h₁, k₂, h₂, e'⟩

section
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {σ : L →+* L} {q n : ℕ}

theorem kerU_biInv {ϖ : L} (hU : IsUnramInv ϖ σ q) {N : ℕ} {z : ℂˣ} {φ : GU σ n → ℂ} (hφ : KerU ϖ q N z φ)
    (g : GU σ n) {k₁ k₂ : GU σ n} (h₁ : k₁ ∈ KU σ n) (h₂ : k₂ ∈ KU σ n) : φ (k₁ * g * k₂) = φ g := by
  obtain ⟨d, t, ht, a, ha, b, hb, rfl⟩ := cartan_complete L ϖ σ q n hU g
  rw [show k₁ * (a * t * b) * k₂ = (k₁ * a) * t * (b * k₂) by group, hφ d t ht _ (mul_mem h₁ ha) _ (mul_mem hb h₂),
    hφ d t ht a ha b hb]

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem sph_eq (ϖ : Lˣ) (hU : IsUnramInv (ϖ : L) σ q) {χ : Lˣ →* ℂˣ} (hχ : IsUnr χ) {s : ℂ} {Φ : GD σ n → ℂ}
    (hΦ : IsSphSec σ q n χ s Φ) {N : ℕ} {z : ℂˣ} {φ : GU σ n → ℂ} (hφ : KerU (ϖ : L) q N z φ)
    (hX : varX q n (χ ϖ) s = (z : ℂ) * ((q : ℂ) ^ N)⁻¹) (g : GU σ n) : Φ (io1 σ n g) = φ g := by
  obtain ⟨d, t, ht, a, ha, b, hb, rfl⟩ := cartan_complete L (ϖ : L) σ q n hU g
  rw [GlobalTheory.T.sphericalDoublingSection_graph_diagonal_eq L ϖ σ q n hU χ hχ s Φ hΦ d t ht a ha b hb, hφ d t ht a ha b hb, hX]

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem exists_unr_char (ϖ : Lˣ) (hU : IsUnramInv (ϖ : L) σ q) (z : ℂˣ) : ∃ χ : Lˣ →* ℂˣ, IsUnr χ ∧ χ ϖ = z := by
  refine ⟨{ toFun := fun u => z ^ Formalism.UG.ordL (u : L), map_one' := ?_, map_mul' := fun a b => ?_ }, fun u hu => ?_, ?_⟩
  · have : Formalism.UG.ordL (1 : L) = 0 := by simp [Formalism.UG.ordL]; rfl
    simp [this]
  · simp [Formalism.UG.P.fIwasawa_ordL_mul _ _ a.ne_zero b.ne_zero, _root_.zpow_add]
  · have : Formalism.UG.ordL (u : L) = 0 := by
      have h0 : Valued.v (u : L) ≠ 0 := by rw [hu]; exact one_ne_zero
      have h1 : WithZero.unzero h0 = 1 := WithZero.coe_injective (by rw [WithZero.coe_unzero, hu]; rfl)
      simp [Formalism.UG.ordL, h0, h1]
    simp [this]
  · have h := Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1 (1 : ℤ)
    rw [zpow_one] at h
    simp [h]

theorem exists_haar (ϖ : L) (hU : IsUnramInv ϖ σ q) (n : ℕ) [MeasurableSpace (GU σ n)] [BorelSpace (GU σ n)] :
    ∃ μ : Measure (GU σ n), μ.IsHaarMeasure ∧ μ (KU σ n) = 1 := by
  haveI := GlobalTheory.LGrp.locallyCompact_GU_of_unram hU n
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU
  let K₀ : TopologicalSpace.PositiveCompacts (GU σ n) :=
    ⟨⟨_, hc⟩, by rw [ho.interior_eq]; exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self⟩

end

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem closedForm_eq' (q r : ℕ) (X y : ℂ) (α : Fin (r / 2) → ℂˣ) :
    closedForm q r X y α = eulerFac (bcParam r α) y * ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * X) := by
  rw [closedForm, GlobalTheory.LGrp.bcParam, GlobalTheory.LFun.eulerFac_add, GlobalTheory.LFun.eulerFac_add,
    GlobalTheory.LFun.eulerFac_map, GlobalTheory.LFun.eulerFac_map, Finset.prod_mul_distrib]
  simp only [Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm y]
  rcases Nat.even_or_odd r with h | h
  · rw [if_neg (Nat.not_odd_iff_even.2 h), Nat.even_iff.1 h]
    simp only [Multiset.replicate_zero, GlobalTheory.LFun.eulerFac_zero]
    ring
  · rw [if_pos h, Nat.odd_iff.1 h]
    simp only [Multiset.replicate_one, GlobalTheory.LFun.eulerFac_singleton, Units.val_one, one_mul]
    ring

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem varXY_eq (q r t : ℕ) (hq : 2 ≤ q) (z : ℂ) :
    varX q r z ((t : ℂ) / 2) = z * ((q : ℂ) ^ (r + t))⁻¹ ∧ varY q z ((t : ℂ) / 2) = z * ((q : ℂ) ^ (t + 1))⁻¹ := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  constructor
  · rw [varX, show -(2 * ((t : ℂ) / 2) + r) = -(((r + t : ℕ) : ℂ)) by push_cast; ring, Complex.cpow_neg,
      Complex.cpow_natCast]
  · rw [varY, show -(2 * ((t : ℂ) / 2) + 1) = -(((t + 1 : ℕ) : ℂ)) by push_cast; ring, Complex.cpow_neg,
      Complex.cpow_natCast]

theorem tb_triv : ∀ (q r : ℕ), 2 ≤ q → ∀ α : Fin (r / 2) → ℂˣ, (∀ i, (α i : ℂ) = (q : ℂ) ^ ((r : ℤ) - 1 - 2 * (i.val : ℤ))) → GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α := by
  intro q r hq α hα i
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hn : ‖(α i : ℂ)‖ = (q:ℝ) ^ ((((r:ℤ) - 1 - 2 * (i.val:ℤ) : ℤ)) : ℝ) := by
    rw [hα, norm_zpow, Complex.norm_natCast, Real.rpow_intCast]
  have hi : 2 * i.val + 1 ≤ r := by have := i.2; omega
  have hi' : 2 * (i.val : ℝ) + 1 ≤ r := by exact_mod_cast hi
  have hi0 : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
  rw [Real.rpow_neg (by positivity), GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq, hn, ← Real.rpow_neg (by positivity)]
  constructor <;> apply Real.rpow_le_rpow_of_exponent_le hq1 <;> push_cast <;> linarith

theorem dom_of_tb : ∀ (q r t : ℕ), 2 ≤ q → r ≤ t → ∀ (z : ℂ), ‖z‖ = 1 → ∀ α : Fin (r / 2) → ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY q z ((t : ℂ) / 2)) α := by
  intro q r t hq hrt z hz α hα
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hq1' : (1:ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hq0 : (0:ℝ) < q := by linarith
  rw [(varXY_eq q r t hq z).2]
  have hy : ‖z * ((q:ℂ)^(t+1))⁻¹‖ = ((q:ℝ)^(t+1))⁻¹ := by
    rw [norm_mul, hz, one_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have hB : ((q:ℝ)^2)^(((r:ℝ)-1)/2) ≤ (q:ℝ)^t := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by have : (r:ℝ) ≤ t := (by exact_mod_cast hrt); linarith)
  have hBp : 0 < ((q:ℝ)^2)^(((r:ℝ)-1)/2) := by positivity
  have e : ((q:ℝ)^(t+1))⁻¹ * (q:ℝ)^t = (q:ℝ)⁻¹ := by rw [pow_succ]; field_simp
  have key : ∀ a : ℝ, a ≤ (q:ℝ)^t → ((q:ℝ)^(t+1))⁻¹ * a < 1 := fun a ha =>
    calc ((q:ℝ)^(t+1))⁻¹ * a ≤ ((q:ℝ)^(t+1))⁻¹ * (q:ℝ)^t := mul_le_mul_of_nonneg_left ha (by positivity)
      _ = (q:ℝ)⁻¹ := e
      _ < 1 := inv_lt_one_of_one_lt₀ hq1'
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain, hy]
  refine ⟨by simpa using key 1 (one_le_pow₀ hq1), fun i => ⟨key _ ((hα i).2.trans hB), key _ ?_⟩⟩
  have h1 := (hα i).1
  rw [Real.rpow_neg (by positivity)] at h1
  have hαp : 0 < ‖(α i : ℂ)‖ := norm_pos_iff.2 (α i).ne_zero
  exact (inv_le_of_inv_le₀ hBp h1).trans hB

set_option maxHeartbeats 1000000 in
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in

theorem hasSum_zetaSum_inert : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q r t : ℕ), IsUnramInv ϖ σ q → r ≤ t → ∀ (z : ℂˣ) (φ : GU σ r → ℂ), ‖(z : ℂ)‖ = 1 → KerU ϖ q (r + t) z φ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ r) V) (x : V) (α : Fin (r / 2) → ℂˣ), IsSatVecU ϖ q ρ x α → GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → HasSum (fun a : GU σ r ⧸ KU σ r => φ a.out * ℓ (ρ a.out x)) (eulerFac (bcParam r α) ((z : ℂ) * ((q : ℂ) ^ (t + 1))⁻¹) * (∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((z : ℂ) * ((q : ℂ) ^ (r + t))⁻¹))) * ℓ x) := by
  intro L _ _ _ ϖ σ q r t hU hrt z φ hz hφ V _ _ ρ x α hx hα ℓ hℓ
  obtain ⟨C, hC⟩ := hℓ
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq : q ≠ 0 := by omega
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    have h' := hU.2.2.2.1
    rw [h, map_zero] at h'
    exact WithZero.zero_ne_coe h'
  let ϖu : Lˣ := Units.mk0 ϖ hϖ0
  have hUu : IsUnramInv (ϖu : L) σ q := hU
  obtain ⟨χ, hχ, hχϖ⟩ := exists_unr_char ϖu hUu z
  obtain ⟨Φ, hΦ⟩ := exists_isSphSec σ hq r hχ ((t : ℂ) / 2)
  obtain ⟨hXe, hYe⟩ := varXY_eq q r t hq2 (z : ℂ)
  have hX : varX q r (χ ϖu) ((t : ℂ) / 2) = (z : ℂ) * ((q : ℂ) ^ (r + t))⁻¹ := by rw [hχϖ, hXe]
  have hΦφ : ∀ g, Φ (io1 σ r g) = φ g := sph_eq ϖu hUu hχ hΦ hφ hX
  letI : MeasurableSpace (GU σ r) := borel _
  haveI : BorelSpace (GU σ r) := ⟨rfl⟩
  obtain ⟨μ, hμH, hμK⟩ := exists_haar ϖ hU r
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU r
  have hKo := (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q r hU).1
  have hright : ∀ g, ∀ k ∈ KU σ r, φ (g * k) = φ g := fun g k hk => by
    simpa using kerU_biInv hU hφ g (one_mem _) hk
  have hdouble := GlobalTheory.T.unramifiedDoublingIntegral_inert_place L ϖu σ q r hUu μ hμK χ hχ _ Φ hΦ
  have hzχ : ((χ ϖu : ℂˣ) : ℂ) = z := by rw [hχϖ]
  have hdom : ∀ β : Fin (r / 2) → ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r β →
      Domain (varY q (χ ϖu) ((t : ℂ) / 2)) β := fun β hβ => by
    rw [hzχ]; exact dom_of_tb q r t hq2 hrt z hz β hβ

  obtain ⟨α0, hα0, hw0⟩ := isZonal_one hU r
  have hint1 := ((hdouble α0 _ hw0).1 (hdom α0 (tb_triv q r hq2 α0 hα0))).1
  have hintφ : Integrable φ μ := by simpa [hΦφ] using hint1

  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_zonalSphericalFunction_unramifiedUnitary L ϖ σ q r hU α
  obtain ⟨hintw, hval, -⟩ := (hdouble α w hw).1 (hdom α hα)
  simp only [hΦφ] at hintw hval
  have hFw : ∀ g, ∀ k ∈ KU σ r, φ (g * k) * w (g * k) = φ g * w g := fun g k hk => by
    have h1 := hw.1 1 ⟨k, hk⟩ g
    simp only [OneMemClass.coe_one, one_mul] at h1
    rw [hright g k hk, h1]
  have hsw := (GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ r) hKo hμK _ hFw hintw).of_norm
  have hci := (GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets _ μ (KU σ r) hKo hμK (fun g => φ g * w g) _ hFw hsw.hasSum).2
  have hS1 : HasSum (fun a : GU σ r ⧸ KU σ r => φ a.out * w a.out)
      (closedForm q r (varX q r (χ ϖu) ((t : ℂ) / 2)) (varY q (χ ϖu) ((t : ℂ) / 2)) α) := by
    rw [← hval, hci]; exact hsw.hasSum

  have hsφ := GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ r) hKo hμK φ hright hintφ
  have hsψ : Summable (fun a : GU σ r ⧸ KU σ r => φ a.out * ℓ (ρ a.out x)) := by
    refine Summable.of_norm_bounded (hsφ.mul_left C) fun a => ?_
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)

  have hm : ∀ g : GU σ r, dosetInd ℂ (KU σ r) g ∈ Formalism.UG.Hecke ℂ (KU σ r) := fun g => Formalism.UG.Final.DosetIndMem _ _ ℂ g
  have hcond : ∀ g : GU σ r, Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) (fun g => ℓ x * w g) 1 =
      Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) (fun g => ℓ (ρ g x)) 1 := fun g => by
    have h1 := hw.2.2 _ (hm g)
    have h2 := congrArg ℓ (hx.2.2 _ (hm g))
    rw [map_smul, smul_eq_mul] at h2
    have e1 : Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) (fun g => ℓ x * w g) 1 =
        ℓ x * Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) w 1 := by
      unfold Formalism.UG.hAct
      rw [mul_finsum]
      exact finsum_congr fun c => by simp only [smul_eq_mul]; ring
    have e2 : Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) (fun g => ℓ (ρ g x)) 1 =
        ℓ (GlobalTheory.LFun.heckeVec ρ (KU σ r) (dosetInd ℂ (KU σ r) g) x) := by
      refine Eq.trans (finsum_congr fun c => ?_)
        (ℓ.toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec hK (hm g) ρ x)).symm
      simp
    rw [e1, e2, h1, h2, mul_comm]
  have hswap := GlobalTheory.T.biInvariant_replace_same_double_coset_sums _ (KU σ r) hK φ (fun g => ℓ x * w g) (fun g => ℓ (ρ g x)) _
    (fun a b g => kerU_biInv hU hφ g a.2 b.2)
    (fun a b g => by simp only [hw.1 a b g]) hcond hsψ.hasSum
  have h2 : HasSum (fun a : GU σ r ⧸ KU σ r => φ a.out * (ℓ x * w a.out))
      (closedForm q r (varX q r (χ ϖu) ((t : ℂ) / 2)) (varY q (χ ϖu) ((t : ℂ) / 2)) α * ℓ x) := by
    have h3 : (fun a : GU σ r ⧸ KU σ r => φ a.out * (ℓ x * w a.out)) = fun a => φ a.out * w a.out * ℓ x :=
      funext fun a => by ring
    rw [h3]; exact hS1.mul_right (ℓ x)
  have e := hswap.unique h2
  rw [hX, hzχ, hYe, closedForm_eq'] at e
  rw [← e]
  exact hsψ.hasSum

end GlobalTheory.ZetaSumU

end
