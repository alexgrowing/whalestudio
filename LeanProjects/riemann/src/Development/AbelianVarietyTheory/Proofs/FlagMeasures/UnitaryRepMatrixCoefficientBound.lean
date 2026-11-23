import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarBallGrowthUnitaryJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableExpNegMulOfSublevelGrowth
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarSubgroupBiInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalVolumeGrowthStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaWithCutoffSubgroupStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec.ConstTermNorm

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

theorem continuous_integral_translate (ν : Measure G) (D : G → ℝ) (hDc : Continuous D)
    (hDi : ∀ g, D g⁻¹ = D g) (hDm : ∀ g h, D (g * h) ≤ D g + D h) (c C : ℝ) (hc : 0 ≤ c)
    (hν : Integrable (fun m => Real.exp (-(c * D m))) ν) (a : G → ℂ) (ha : Continuous a)
    (hb : ∀ g, ‖a g‖ ≤ C * Real.exp (-(c * D g))) :
    Continuous (fun g => ∫ m, a (m * g) ∂ν) := by
  have hC : 0 ≤ C := by
    have h1 := hb 1
    have h2 := Real.exp_pos (-(c * D 1))
    nlinarith [norm_nonneg (a 1)]
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have hev : ∀ᶠ g in nhds g₀, D g < D g₀ + 1 :=
    hDc.continuousAt.eventually (gt_mem_nhds (lt_add_one (D g₀)))
  refine continuousAt_of_dominated
    (bound := fun m => C * Real.exp (c * (D g₀ + 1)) * Real.exp (-(c * D m))) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun g =>
      (ha.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
  · filter_upwards [hev] with g hg
    refine Filter.Eventually.of_forall fun m => ?_
    have hm : D m ≤ D (m * g) + D g := by
      have h3 := hDm (m * g) g⁻¹
      rwa [mul_inv_cancel_right, hDi] at h3
    have k1 := mul_le_mul_of_nonneg_left hm hc
    have k2 := mul_le_mul_of_nonneg_left hg.le hc
    calc ‖a (m * g)‖ ≤ C * Real.exp (-(c * D (m * g))) := hb _
      _ ≤ C * Real.exp (c * (D g₀ + 1)) * Real.exp (-(c * D m)) := by
        rw [mul_assoc, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC
        nlinarith
  · exact hν.const_mul _
  · exact Filter.Eventually.of_forall fun m =>
      (ha.comp (continuous_const.mul continuous_id)).continuousAt

theorem integrable_translate_mul (ν μ : Measure G) [SFinite ν] [SFinite μ] (D : G → ℝ) (hD0 : ∀ g, 0 ≤ D g)
    (hDi : ∀ g, D g⁻¹ = D g) (hDm : ∀ g h, D (g * h) ≤ D g + D h) (c C C' : ℝ) (hc : 0 ≤ c)
    (hν : Integrable (fun m => Real.exp (-(c / 2 * D m))) ν)
    (hμ : Integrable (fun m => Real.exp (-(c / 2 * D m))) μ) (a b : G → ℂ) (ha : Continuous a) (hb : Continuous b)
    (hab : ∀ g, ‖a g‖ ≤ C * Real.exp (-(c * D g))) (hbb : ∀ g, ‖b g‖ ≤ C' * Real.exp (-(c * D g))) :
    Integrable (fun p : G × G => a (p.1 * p.2) * b p.2) (ν.prod μ) := by
  have hC : 0 ≤ C := by
    have h1 := hab 1
    have h2 := Real.exp_pos (-(c * D 1))
    nlinarith [norm_nonneg (a 1)]
  have hC' : 0 ≤ C' := by
    have h1 := hbb 1
    have h2 := Real.exp_pos (-(c * D 1))
    nlinarith [norm_nonneg (b 1)]
  have hmeas : AEStronglyMeasurable (fun p : G × G => a (p.1 * p.2) * b p.2) (ν.prod μ) :=
    ((ha.comp continuous_mul).mul (hb.comp continuous_snd)).aestronglyMeasurable
  refine Integrable.mono' ((hν.mul_prod hμ).const_mul (C * C')) hmeas
    (Filter.Eventually.of_forall fun p => ?_)
  obtain ⟨m, y⟩ := p
  have hm : D m ≤ D (m * y) + D y := by
    have h3 := hDm (m * y) y⁻¹
    rwa [mul_inv_cancel_right, hDi] at h3
  have k0 := mul_nonneg hc (hD0 (m * y))
  have k1 := mul_le_mul_of_nonneg_left hm hc
  show ‖a (m * y) * b y‖ ≤ C * C' * (Real.exp (-(c / 2 * D m)) * Real.exp (-(c / 2 * D y)))
  rw [norm_mul]
  calc ‖a (m * y)‖ * ‖b y‖ ≤ (C * Real.exp (-(c * D (m * y)))) * (C' * Real.exp (-(c * D y))) :=
        mul_le_mul (hab _) (hbb _) (norm_nonneg _) (mul_nonneg hC (Real.exp_pos _).le)
    _ = C * C' * Real.exp (-(c * D (m * y)) + -(c * D y)) := by rw [Real.exp_add]; ring
    _ ≤ C * C' * (Real.exp (-(c / 2 * D m)) * Real.exp (-(c / 2 * D y))) := by
        rw [← Real.exp_add]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (mul_nonneg hC hC')
        nlinarith

private theorem inner_mul_eq_inner_inv_of_isURepOn {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ)
    (m y : UJ ε) (w u : H) :
    ⟪w, σ (umat (m * y)) u⟫_ℂ = ⟪σ (umat m⁻¹) w, σ (umat y) u⟫_ℂ := by
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hσ
  have e2 : umat m * umat m⁻¹ = 1 := congrArg (fun z : UJ ε => umat z) (mul_inv_cancel m)
  have hv : σ (umat m) (σ (umat m⁻¹) w) = w := by
    have h3 := hmul (umat m) m.2 (umat m⁻¹) m⁻¹.2
    rw [e2, h1] at h3
    have h4 := congrArg (fun T : H →L[ℂ] H => T w) h3
    simpa using h4.symm
  have hmy : σ (umat (m * y)) u = σ (umat m) (σ (umat y) u) := by
    have h3 := hmul (umat m) m.2 (umat y) y.2
    exact congrArg (fun T : H →L[ℂ] H => T u) h3
  let T : H →ₗᵢ[ℂ] H := ⟨(σ (umat m) : H →ₗ[ℂ] H), fun x => hiso (umat m) m.2 x⟩
  rw [hmy]
  conv_lhs => rw [← hv]
  exact T.inner_map_map (σ (umat m⁻¹) w) (σ (umat y) u)

private theorem dOp_nonneg_inv_subadditive_continuous (n : ℕ) (ε : Fin n → Bool) :
    (∀ g : UJ ε, 0 ≤ dOp (umat g)) ∧ (∀ g : UJ ε, dOp (umat g⁻¹) = dOp (umat g)) ∧
      (∀ g h : UJ ε, dOp (umat (g * h)) ≤ dOp (umat g) + dOp (umat h)) ∧
      Continuous (fun g : UJ ε => dOp (umat g)) := by
  obtain ⟨-, -, -, -, h5⟩ := GlobalTheory.Count.Cartan.cartan_distances n ε
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : ∀ g : UJ ε, dOp (umat g) = 0 := fun g => by
      rw [GlobalTheory.Count.Cartan.dOp_eq, Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) ℂ) (umat g) 0]
      letI : NormedRing (Matrix (Fin 0) (Fin 0) ℂ) := Matrix.instL2OpNormedRing
      exact Real.log_eq_zero.2 (Or.inl norm_zero)
    refine ⟨fun g => (h0 g).ge, fun g => by rw [h0, h0], fun g h => by rw [h0, h0, h0, add_zero], h5⟩
  · obtain ⟨-, h2, -⟩ := GlobalTheory.Count.Cartan.cartan_distances n ε
    exact ⟨fun g => (h2 g 1 hn).1, fun g => (h2 g 1 hn).2.1, fun g h => (h2 g h hn).2.2.1, h5⟩

private theorem nw_one_mem_mul_mem_inv_mem_isClosed {n : ℕ} (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) :
    (1 : UJ ε) ∈ NW ε W ∧ (∀ a ∈ NW ε W, ∀ b ∈ NW ε W, a * b ∈ NW ε W) ∧
      (∀ a ∈ NW ε W, a⁻¹ ∈ NW ε W) ∧ IsClosed (NW ε W) := by
  have hadd : ∀ x p q : Fin n → ℂ, herm (Jm ε) x (p + q) = herm (Jm ε) x p + herm (Jm ε) x q := by
    intro x p q
    simp only [herm, star_add, add_dotProduct]
  have hneg : ∀ x p : Fin n → ℂ, herm (Jm ε) x (-p) = -herm (Jm ε) x p := by
    intro x p
    simp only [herm, star_neg, neg_dotProduct]
  have hzero : ∀ x : Fin n → ℂ, herm (Jm ε) x 0 = 0 := by
    intro x
    simp only [herm, star_zero, zero_dotProduct]
  have hmulv : ∀ g h : UJ ε,
      umat (g * h) - 1 = (umat g - 1) * (umat h - 1) + (umat g - 1) + (umat h - 1) := by
    intro g h
    have e : umat (g * h) = umat g * umat h := rfl
    rw [e]
    noncomm_ring
  have hinv : ∀ g : UJ ε, umat g⁻¹ - 1 = -(umat g - 1) - (umat g⁻¹ - 1) * (umat g - 1) ∧
      umat g⁻¹ - 1 = -(umat g - 1) - (umat g - 1) * (umat g⁻¹ - 1) := by
    intro g
    have h1 : umat g⁻¹ * umat g = 1 := congrArg (fun z : UJ ε => umat z) (inv_mul_cancel g)
    have h2 : umat g * umat g⁻¹ = 1 := congrArg (fun z : UJ ε => umat z) (mul_inv_cancel g)
    constructor
    · rw [sub_mul, mul_sub, mul_sub, h1, mul_one, one_mul, one_mul]
      abel
    · rw [mul_sub, sub_mul, sub_mul, h2, mul_one, one_mul, one_mul]
      abel
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e0 : umat (1 : UJ ε) - 1 = 0 := sub_self (1 : Matrix (Fin n) (Fin n) ℂ)
    simp only [NW, Set.mem_setOf_eq, e0, zero_mulVec, hzero]
    exact ⟨fun _ _ => trivial, fun _ _ => W.zero_mem, fun _ _ _ => trivial⟩
  · intro a ha b hb
    simp only [NW, Set.mem_setOf_eq] at ha hb ⊢
    obtain ⟨a1, a2, a3⟩ := ha
    obtain ⟨b1, b2, b3⟩ := hb
    refine ⟨fun x hx => ?_, fun y hy => ?_, fun y x hx => ?_⟩ <;>
      rw [hmulv, add_mulVec, add_mulVec, ← mulVec_mulVec]
    · rw [b1 x hx, a1 x hx, mulVec_zero, add_zero, add_zero]
    · rw [a1 _ (b2 y hy), zero_add]
      exact W.add_mem (a2 y hy) (b2 y hy)
    · rw [hadd, hadd, a3 _ x hx, a3 y x hx, b3 y x hx, add_zero, add_zero]
  · intro g hg
    simp only [NW, Set.mem_setOf_eq] at hg ⊢
    obtain ⟨a1, a2, a3⟩ := hg
    have c1 : ∀ x ∈ W, (umat g⁻¹ - 1) *ᵥ x = 0 := by
      intro x hx
      rw [(hinv g).1, sub_mulVec, neg_mulVec, ← mulVec_mulVec, a1 x hx, mulVec_zero, neg_zero, sub_zero]
    refine ⟨c1, fun y hy => ?_, fun y x hx => ?_⟩
    · rw [(hinv g).1, sub_mulVec, neg_mulVec, ← mulVec_mulVec, c1 _ (a2 y hy), sub_zero]
      exact W.neg_mem (a2 y hy)
    · rw [(hinv g).2, sub_mulVec, neg_mulVec, ← mulVec_mulVec, sub_eq_add_neg, hadd, hneg, hneg,
        a3 y x hx, a3 _ x hx, neg_zero, add_zero]
  · have hcu : Continuous (fun g : UJ ε => umat g - 1) :=
      (Units.continuous_val.comp continuous_subtype_val).sub continuous_const
    have hcv : ∀ y, Continuous (fun g : UJ ε => (umat g - 1) *ᵥ y) := fun y =>
      hcu.matrix_mulVec continuous_const
    simp only [NW, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter (isClosed_iInter fun x => isClosed_iInter fun _ =>
      isClosed_eq (hcv x) continuous_const) (IsClosed.inter (isClosed_iInter fun y =>
      isClosed_iInter fun _ => (W.closed_of_finiteDimensional).preimage (hcv y))
      (isClosed_iInter fun y => isClosed_iInter fun x => isClosed_iInter fun _ =>
      isClosed_eq ?_ continuous_const))
    simp only [herm]
    unfold dotProduct
    exact continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp (hcv y).star).mul continuous_const

end General

theorem constTerm_inner : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → ∀ β : UJ ε → ENNReal, Measurable β → (∀ y, β y ≠ ⊤) → (∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d c : ℝ) (u v v' : H), IsURepOn (UJset ε) σ → IsFdeg (muG ε) σ d → 8 * n * rkR ε < c → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) u⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v', σ (umat g) u⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) v'⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → Continuous (fun g : UJ ε => (∫ m, ⟪v, σ (umat (m * g)) u⟫_ℂ ∂ν)) ∧ Integrable (fun g : UJ ε => ((β g).toReal : ℂ) * ((∫ m, ⟪v, σ (umat (m * g)) u⟫_ℂ ∂ν) * star (∫ m, ⟪v', σ (umat (m * g)) u⟫_ℂ ∂ν))) (muG ε) ∧ ∫ g : UJ ε, ((β g).toReal : ℂ) * ((∫ m, ⟪v, σ (umat (m * g)) u⟫_ℂ ∂ν) * star (∫ m, ⟪v', σ (umat (m * g)) u⟫_ℂ ∂ν)) ∂(muG ε) = (∫ m, ⟪v, σ (umat m) v'⟫_ℂ ∂ν) * ((‖u‖ ^ 2 / d : ℝ) : ℂ) := by
  intro n ε W ν hW hν β hβ hβt hβ1 H _ _ _ σ d c u v v' hσ hd hc hf hf' hvv
  obtain ⟨hD0, hDi, hDm, hDc⟩ := dOp_nonneg_inv_subadditive_continuous n ε
  obtain ⟨n1, nmul, ninv, ncl⟩ := nw_one_mem_mul_mem_inv_mem_isClosed ε W
  have hr := GlobalTheory.T.haar_subgroup_bi_invariant n ε W ν hW hν
  obtain ⟨-, hνi⟩ := GlobalTheory.T.unipotentRadical_volume_growth n ε W ν hW hν
  haveI : IsFiniteMeasureOnCompacts ν := hν.2.1
  have hnr : (0 : ℝ) ≤ (n : ℝ) * (rkR ε : ℝ) := by positivity
  have hc0 : 0 ≤ c := by nlinarith
  have hνc : Integrable (fun m : UJ ε => Real.exp (-(c * dOp (umat m)))) ν := hνi c (by nlinarith)
  have hνc2 : Integrable (fun m : UJ ε => Real.exp (-(c / 2 * dOp (umat m)))) ν :=
    hνi (c / 2) (by nlinarith)
  have hμc2 : Integrable (fun m : UJ ε => Real.exp (-(c / 2 * dOp (umat m)))) (muG ε) := by
    obtain ⟨C0, -, hC0⟩ := GlobalTheory.BallVol.ballVol n ε
    exact GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth (UJ ε) (muG ε) (fun g => dOp (umat g)) _ (c / 2) C0
      hDc.measurable hD0 hC0 (by nlinarith)
  obtain ⟨C1, hC1⟩ := hf
  obtain ⟨C2, hC2⟩ := hf'
  have hcu : Continuous (fun g : UJ ε => umat g) := Units.continuous_val.comp continuous_subtype_val
  have hsc : ∀ x : H, Continuous (fun g : UJ ε => σ (umat g) x) := fun x =>
    (hσ.2.2 x).comp_continuous hcu (fun g => g.2)
  have cf : Continuous (fun g : UJ ε => ⟪v, σ (umat g) u⟫_ℂ) := continuous_const.inner (hsc u)
  have cf' : Continuous (fun g : UJ ε => ⟪v', σ (umat g) u⟫_ℂ) := continuous_const.inner (hsc u)
  have hconj : ∀ F : UJ ε → ℂ, ∫ x, star (F x) ∂ν = star (∫ x, F x ∂ν) := fun F => by
    simpa using integral_conj (μ := ν) (f := F)
  have hP := integrable_translate_mul ν (muG ε) (fun g => dOp (umat g)) hD0 hDi hDm c C2 C1 hc0 hνc2 hμc2
    (fun g => star ⟪v', σ (umat g) u⟫_ℂ) (fun g => ⟪v, σ (umat g) u⟫_ℂ) cf'.star cf
    (fun g => (norm_star _).trans_le (hC2 g)) hC1
  have hνN : ∀ᵐ m ∂ν, m ∈ NW ε W := ae_iff.2 hν.2.2.1
  have hF' : ∀ y : UJ ε, ∀ m₀ ∈ NW ε W, (∫ m, ⟪v', σ (umat (m * (m₀ * y))) u⟫_ℂ ∂ν) =
      ∫ m, ⟪v', σ (umat (m * y)) u⟫_ℂ ∂ν := by
    intro y m₀ hm₀
    have e' : Measure.map (MeasurableEquiv.mulRight m₀) ν = ν := hr.1 m₀ hm₀
    conv_rhs => rw [← e']
    rw [integral_map_equiv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact congrArg (fun z : UJ ε => ⟪v', σ (umat z) u⟫_ℂ) (mul_assoc x m₀ y).symm
  have hin : ∀ y : UJ ε, (∫ m, ⟪v, σ (umat (m * y)) u⟫_ℂ *
      star (∫ k, ⟪v', σ (umat (k * (m * y))) u⟫_ℂ ∂ν) ∂ν) =
      (∫ m, ⟪v, σ (umat (m * y)) u⟫_ℂ ∂ν) * star (∫ k, ⟪v', σ (umat (k * y)) u⟫_ℂ ∂ν) := by
    intro y
    rw [← integral_mul_const]
    refine integral_congr_ae ?_
    filter_upwards [hνN] with m hm
    rw [hF' y m hm]
  have hpt : ∀ y : UJ ε, (∫ m, star ⟪v', σ (umat (m * y)) u⟫_ℂ * ⟪v, σ (umat y) u⟫_ℂ ∂ν) =
      ⟪v, σ (umat y) u⟫_ℂ * star (∫ m, ⟪v', σ (umat (m * y)) u⟫_ℂ ∂ν) := by
    intro y
    rw [integral_mul_const, hconj, mul_comm]
  have hhint : Integrable (fun y : UJ ε => ⟪v, σ (umat y) u⟫_ℂ *
      star (∫ m, ⟪v', σ (umat (m * y)) u⟫_ℂ ∂ν)) (muG ε) :=
    hP.integral_prod_right.congr (Filter.Eventually.of_forall fun y => hpt y)
  let N : Subgroup (UJ ε) :=
    { carrier := NW ε W, mul_mem' := fun {a b} ha hb => nmul a ha b hb, one_mem' := n1,
      inv_mem' := fun {a} ha => ninv a ha }
  obtain ⟨-, hU⟩ := GlobalTheory.T.weil_formula_with_cutoff_subgroup (UJ ε) (muG ε) N ν ncl hν β hβ hβt hβ1
  obtain ⟨hUi, hUe⟩ := hU _ hhint
  have key : ∀ m : UJ ε, ∫ y, star ⟪v', σ (umat (m * y)) u⟫_ℂ * ⟪v, σ (umat y) u⟫_ℂ ∂(muG ε) =
      ⟪u, u⟫_ℂ * ⟪v, σ (umat m⁻¹) v'⟫_ℂ / (d : ℂ) := by
    intro m
    rw [← (hd.2 u v u (σ (umat m⁻¹) v')).2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show star ⟪v', σ (umat (m * y)) u⟫_ℂ * ⟪v, σ (umat y) u⟫_ℂ = _
    rw [inner_mul_eq_inner_inv_of_isURepOn σ hσ m y v' u]
    exact mul_comm _ _
  have hinvI : ∫ m, ⟪v, σ (umat m⁻¹) v'⟫_ℂ ∂ν = ∫ m, ⟪v, σ (umat m) v'⟫_ℂ ∂ν := by
    have e' : Measure.map (MeasurableEquiv.inv (UJ ε)) ν = ν := hr.2
    conv_rhs => rw [← e']
    rw [integral_map_equiv]
    rfl
  refine ⟨continuous_integral_translate ν (fun g => dOp (umat g)) hDc hDi hDm c C1 hc0 hνc
    (fun g => ⟪v, σ (umat g) u⟫_ℂ) cf hC1, ?_, ?_⟩
  · refine hUi.congr (Filter.Eventually.of_forall fun g => ?_)
    dsimp only
    rw [hin g]
  · have s1 : (∫ g : UJ ε, ((β g).toReal : ℂ) * ((∫ m, ⟪v, σ (umat (m * g)) u⟫_ℂ ∂ν) *
        star (∫ m, ⟪v', σ (umat (m * g)) u⟫_ℂ ∂ν)) ∂(muG ε)) =
        ∫ y, ⟪v, σ (umat y) u⟫_ℂ * star (∫ m, ⟪v', σ (umat (m * y)) u⟫_ℂ ∂ν) ∂(muG ε) := by
      rw [hUe]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      dsimp only
      rw [hin g]
    have s2 : (∫ y, ⟪v, σ (umat y) u⟫_ℂ * star (∫ m, ⟪v', σ (umat (m * y)) u⟫_ℂ ∂ν) ∂(muG ε)) =
        ∫ y, ∫ m, star ⟪v', σ (umat (m * y)) u⟫_ℂ * ⟪v, σ (umat y) u⟫_ℂ ∂ν ∂(muG ε) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => (hpt y).symm)
    have s3 := integral_integral_swap (μ := ν) (ν := muG ε)
      (f := fun m y => star ⟪v', σ (umat (m * y)) u⟫_ℂ * ⟪v, σ (umat y) u⟫_ℂ) hP
    rw [s1, s2, ← s3]
    simp_rw [key]
    have hu : ⟪u, u⟫_ℂ = ((‖u‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K u
    rw [integral_div, integral_const_mul, hinvI, hu]
    push_cast
    ring

end GlobalTheory.Dec.ConstTermNorm
