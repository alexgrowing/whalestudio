import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealWeight
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DistribHaarCharTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VectorTupleProductMeasureTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexMulMeasure

open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Formalism.UG Matrix GlobalTheory.BorelUMod
open scoped NNReal Pointwise

noncomputable section
namespace GlobalTheory.LineUMod

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem locCompact_secondCountable [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    LocallyCompactSpace L ∧ SecondCountableTopology L := by
  obtain ⟨-, hv, -, hϖ, -, hq, hcard⟩ := h
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero, by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  have hp := (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (K := L)).2 ⟨inferInstance, (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing,
      Nat.finite_of_card_ne_zero (by
        refine ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩
  constructor
  · open scoped Valued in exact inferInstance
  · open scoped Valued in exact inferInstance

open UpLatIndex in

theorem distribHaarChar_eq [CompleteSpace L] [LocallyCompactSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ}
    (h : IsUnramInv ϖ σ q) (u : Lˣ) : (distribHaarChar L u : ℝ) = (q : ℝ) ^ (-2 * ordL (u : L)) := by
  have hq : q ≠ 0 := by have := h.2.2.2.2.2.1; omega
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  haveI := (locCompact_secondCountable h).2
  borelize L
  let μ : Measure L := Measure.addHaar
  have key : ∀ k K : ℤ, k ≤ K → μ.real (ordBall L k) = (q : ℝ) ^ (2 * (K - k)) * μ.real (ordBall L K) := by
    intro k K hk
    have e := relIndex_ordBall h hk
    haveI : ((ordBall L K).addSubgroupOf (ordBall L k)).FiniteIndex :=
      ⟨ne_of_eq_of_ne e (pow_ne_zero _ (pow_ne_zero _ hq))⟩
    have := GlobalTheory.BaseModule.addRelIndex_mul_measure (ordBall L K) (ordBall L k) (ordBall_mono hk)
      (isOpen_vball h.2.2.2.1 K).measurableSet μ
    rw [Measure.real, ← this, e, ENNReal.toReal_mul, ENNReal.toReal_natCast, ← pow_mul, Nat.cast_pow, ← zpow_natCast,
      Measure.real]
    congr 2
    omega
  have hs : u • (ordBall L 0 : Set L) = ordBall L (ordL (u : L)) := by
    ext x
    obtain ⟨y, rfl⟩ := MulAction.surjective u x
    beta_reduce
    rw [Set.smul_mem_smul_set_iff, SetLike.mem_coe, SetLike.mem_coe, mem_ordBall, mem_ordBall, Units.smul_def,
      smul_eq_mul, map_mul, v_eq_exp u.ne_zero, neg_zero, WithZero.exp_zero]
    exact (mul_le_iff_le_one_right WithZero.exp_pos).symm
  have h1 := congrArg ENNReal.toReal (distribHaarChar_mul μ u (ordBall L 0 : Set L))
  rw [hs, ENNReal.toReal_mul, ENNReal.coe_toReal, ← Measure.real, ← Measure.real,
    key 0 |ordL (u : L)| (abs_nonneg _), key (ordL (u : L)) _ (le_abs_self _), ← mul_assoc] at h1
  have hpos : μ.real (ordBall L |ordL (u : L)|) ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨(isOpen_vball h.2.2.2.1 _).measure_ne_zero μ ⟨0, zero_mem (ordBall L _)⟩,
      (isCompact_vball h _).measure_ne_top⟩
  have h2 := mul_right_cancel₀ hpos h1
  rw [eq_comm, ← mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ hq'), ← _root_.zpow_neg, ← zpow_add₀ hq'] at h2
  rw [← h2]
  congr 1
  ring

abbrev fixK (σ : L →+* L) : Subfield L := σ.eqLocusField (RingHom.id L)

instance (σ : L →+* L) : IsTopologicalRing (fixK σ) := inferInstanceAs (IsTopologicalRing (fixK σ).toSubring)

instance (σ : L →+* L) [SecondCountableTopology L] : SecondCountableTopology (fixK σ) :=
  TopologicalSpace.Subtype.secondCountableTopology (fixK σ : Set L)

def basisEquiv {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ) {θ d : L} (hθ : θ + σ θ = 1) (hd : σ d = -d)
    (hd0 : d ≠ 0) : (Fin 2 → fixK σ) ≃ₜ+ L where
  toFun x := θ * x 0 + d * x 1
  invFun z := ![⟨z + σ z, by show σ _ = _; simp [hσ, add_comm]⟩, ⟨d⁻¹ * (z - θ * (z + σ z)), by
    show σ _ = d⁻¹ * (z - θ * (z + σ z))
    simp only [map_mul, map_inv₀, map_sub, map_add, hσ, hd, inv_neg]
    linear_combination d⁻¹ * (z + σ z) * hθ⟩]
  left_inv x := by
    have h0 : σ (x 0) = x 0 := (x 0).2
    have h1 : σ (x 1) = x 1 := (x 1).2
    have h2 : θ * x 0 + d * x 1 + σ (θ * x 0 + d * x 1) = x 0 := by
      simp only [map_mul, map_add, h0, h1, hd]
      linear_combination (x 0 : L) * hθ
    funext i
    fin_cases i
    · exact Subtype.ext h2
    · refine Subtype.ext ?_
      show d⁻¹ * (θ * x 0 + d * x 1 - θ * (θ * x 0 + d * x 1 + σ (θ * x 0 + d * x 1))) = x 1
      rw [h2]; field_simp; ring
  right_inv z := by
    show θ * (z + σ z) + d * (d⁻¹ * (z - θ * (z + σ z))) = z
    field_simp; ring
  map_add' x y := by simp only [Pi.add_apply, Subfield.coe_add]; ring
  continuous_toFun := by fun_prop
  continuous_invFun := continuous_pi fun i => by
    fin_cases i
    · exact Continuous.subtype_mk (by fun_prop) _
    · exact Continuous.subtype_mk (by fun_prop) _

section Mat
omit [Valued L (WithZero (Multiplicative ℤ))]

def nMat (x y : Fin n → L) (z : L) : Matrix (Fin (n + 2)) (Fin (n + 2)) L :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun j' => Fin.lastCases z x j') j) (fun i' => Fin.cases 0 (fun j' =>
    Fin.lastCases (Fin.lastCases 1 y i')
      (fun j'' => Fin.lastCases 0 (fun i'' => (1 : Matrix (Fin n) (Fin n) L) i'' j'') i') j') j) i

variable (x y : Fin n → L) (z : L)

@[simp] theorem nMat_zero_zero : nMat x y z 0 0 = 1 := rfl
@[simp] theorem nMat_zero_mid (j : Fin n) : nMat x y z 0 (midIdx j) = x j := by simp [nMat, midIdx]
@[simp] theorem nMat_zero_last : nMat x y z 0 (Fin.last (n + 1)) = z := by simp [nMat, ← Fin.succ_last]
@[simp] theorem nMat_mid_zero (i : Fin n) : nMat x y z (midIdx i) 0 = 0 := rfl
@[simp] theorem nMat_mid_mid (i j : Fin n) :
    nMat x y z (midIdx i) (midIdx j) = (1 : Matrix (Fin n) (Fin n) L) i j := by simp [nMat, midIdx]
@[simp] theorem nMat_mid_last (i : Fin n) : nMat x y z (midIdx i) (Fin.last (n + 1)) = y i := by
  simp [nMat, midIdx, ← Fin.succ_last]
@[simp] theorem nMat_last_zero : nMat x y z (Fin.last (n + 1)) 0 = 0 := rfl
@[simp] theorem nMat_last_mid (j : Fin n) : nMat x y z (Fin.last (n + 1)) (midIdx j) = 0 := by
  simp [nMat, midIdx, ← Fin.succ_last]
@[simp] theorem nMat_last_last : nMat x y z (Fin.last (n + 1)) (Fin.last (n + 1)) = 1 := by
  simp [nMat, ← Fin.succ_last]

theorem nMat_mul (x' y' : Fin n → L) (z' : L) :
    nMat x y z * nMat x' y' z' = nMat (x + x') (y + y') (z + x ⬝ᵥ y' + z') := by
  ext i j
  induction i using lineCases <;> induction j using lineCases <;>
    simp [mul_apply, sum_line, Matrix.one_apply, dotProduct] <;> ring

theorem nMat_zero : nMat (0 : Fin n → L) 0 0 = 1 := by
  ext i j
  induction i using lineCases <;> induction j using lineCases <;> simp [Matrix.one_apply]

theorem adjJ_nMat (σ : L →+* L) :
    adjJ σ (nMat x y z) = nMat (fun j => σ (y j.rev)) (fun i => σ (x i.rev)) (σ z) := by
  ext i j
  induction i using lineCases <;> induction j using lineCases <;> simp [adjJ, Matrix.one_apply, eq_comm]

end Mat

variable {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ)

def rowOf (σ : L →+* L) (y : Fin n → L) : Fin n → L := fun j => -σ (y j.rev)

theorem val_eq_nMat (g : (lineParU σ hσ hc n).U) :
    g.1.1.val = nMat (rowOf σ fun i => g.1.1.val (midIdx i) (Fin.last _)) (fun i => g.1.1.val (midIdx i) (Fin.last _))
      (g.1.1.val 0 (Fin.last _)) ∧
    g.1.1.val 0 (Fin.last _) + σ (g.1.1.val 0 (Fin.last _)) =
      (rowOf σ fun i => g.1.1.val (midIdx i) (Fin.last _)) ⬝ᵥ fun i => g.1.1.val (midIdx i) (Fin.last _) := by
  obtain ⟨h1, h2, h3⟩ := (mem_lineParU_U σ hσ hc g.1).1 g.2
  have h4 := row_eq_zero_of_col σ g.1 0 h1
  rw [Fin.rev_zero] at h4
  have h5 : adjJ σ g.1.1.val * g.1.1.val = 1 := by rw [← (mem_GU_iff_adjJ σ _).1 g.1.2, Units.inv_mul]
  generalize g.1.1.val = X at *
  have h6 : X (Fin.last _) (Fin.last _) = 1 := by
    have := congrFun (congrFun h5 (Fin.last _)) (Fin.last _)
    simpa [mul_apply, sum_line, adjJ, h1, h2] using this
  have e : X = nMat (fun j => X 0 (midIdx j)) (fun i => X (midIdx i) (Fin.last _)) (X 0 (Fin.last _)) := by
    ext i j
    induction i using lineCases <;> induction j using lineCases <;> simp [h1, h2, h3, h4, h6]
  rw [e, adjJ_nMat, nMat_mul] at h5
  have h7 : (fun j => X 0 (midIdx j)) = rowOf σ fun i => X (midIdx i) (Fin.last _) := funext fun j => by
    have := congrFun (congrFun h5 0) (midIdx j)
    simp only [nMat_zero_mid, Pi.add_apply, Matrix.one_apply_ne (zero_ne_midIdx j)] at this
    exact eq_neg_of_add_eq_zero_right this
  refine ⟨h7 ▸ e, ?_⟩
  have := congrFun (congrFun h5 0) (Fin.last _)
  simp only [nMat_zero_last, Matrix.one_apply_ne zero_ne_lastIdx] at this
  simp only [dotProduct, rowOf, neg_mul, Finset.sum_neg_distrib] at this ⊢
  linear_combination this

omit [Valued L (WithZero (Multiplicative ℤ))] in
include hσ in
theorem adjJ_mul_nMat (y : Fin n → L) (z : L) (hz : z + σ z = rowOf σ y ⬝ᵥ y) :
    adjJ σ (nMat (rowOf σ y) y z) * nMat (rowOf σ y) y z = 1 := by
  rw [adjJ_nMat, nMat_mul, ← nMat_zero]
  congr 1
  · funext j; simp [rowOf]
  · funext j; simp [rowOf, hσ]
  · simp only [dotProduct, rowOf, neg_mul, Finset.sum_neg_distrib] at hz ⊢
    linear_combination hz

def nElt (y : Fin n → L) (z : L) (hz : z + σ z = rowOf σ y ⬝ᵥ y) : (lineParU σ hσ hc n).U :=
  ⟨⟨⟨nMat (rowOf σ y) y z, adjJ σ (nMat (rowOf σ y) y z), mul_eq_one_comm.1 (adjJ_mul_nMat hσ y z hz),
    adjJ_mul_nMat hσ y z hz⟩, (mem_GU_iff_adjJ σ _).2 rfl⟩, (mem_lineParU_U σ hσ hc _).2 ⟨fun i hi => by
      induction i using lineCases
      · exact absurd rfl hi
      · rfl
      · rfl, rfl, fun i j => nMat_mid_mid _ _ _ i j⟩⟩

omit [Valued L (WithZero (Multiplicative ℤ))] in
include hσ in
theorem map_rowOf_dot (y : Fin n → L) : σ (rowOf σ y ⬝ᵥ y) = rowOf σ y ⬝ᵥ y := by
  simp only [dotProduct, rowOf, map_sum, map_mul, map_neg, hσ]
  rw [← Equiv.sum_comp Fin.revPerm]
  simp [mul_comm]

variable {θ d : L} (hθ : θ + σ θ = 1) (hd : σ d = -d) (hd0 : d ≠ 0)

def skewPart (z : L) : fixK σ := (basisEquiv hσ hc hθ hd hd0).symm z 1

theorem skewPart_coe (z : L) : (skewPart hσ hc hθ hd hd0 z : L) = d⁻¹ * (z - θ * (z + σ z)) := rfl

theorem continuous_skewPart : Continuous (skewPart hσ hc hθ hd hd0) :=
  (continuous_apply 1).comp (basisEquiv hσ hc hθ hd hd0).symm.continuous

omit [Valued L (WithZero (Multiplicative ℤ))] in
include hσ hθ hd in
theorem trace_corner (y : Fin n → L) (c : fixK σ) :
    θ * (rowOf σ y ⬝ᵥ y) + d * c + σ (θ * (rowOf σ y ⬝ᵥ y) + d * c) = rowOf σ y ⬝ᵥ y := by
  have h1 : σ c = c := c.2
  rw [map_add, map_mul, map_mul, map_rowOf_dot hσ, hd, h1]
  linear_combination (rowOf σ y ⬝ᵥ y) * hθ

def coord (n : ℕ) : (lineParU σ hσ hc n).U ≃ₜ (Fin n → L) × fixK σ where
  toFun g := (fun i => g.1.1.val (midIdx i) (Fin.last _), skewPart hσ hc hθ hd hd0 (g.1.1.val 0 (Fin.last _)))
  invFun p := nElt hσ hc p.1 _ (trace_corner hσ hθ hd p.1 p.2)
  left_inv g := by
    obtain ⟨h1, h2⟩ := val_eq_nMat hσ hc g
    refine Subtype.ext (Subtype.ext (Units.ext (Eq.trans ?_ h1.symm)))
    show nMat _ _ _ = _
    congr 1
    rw [← h2, skewPart_coe, mul_inv_cancel_left₀ hd0, add_sub_cancel]
  right_inv p := by
    refine Prod.ext (funext fun i => nMat_mid_last _ _ _ i) (Subtype.ext ?_)
    show (skewPart hσ hc hθ hd hd0 (nMat _ _ _ 0 (Fin.last _)) : L) = _
    rw [nMat_zero_last, skewPart_coe, trace_corner hσ hθ hd, add_sub_cancel_left, inv_mul_cancel_left₀ hd0]
  continuous_toFun := by
    have h : ∀ i j, Continuous fun g : (lineParU σ hσ hc n).U => g.1.1.val i j := fun i j =>
      (continuous_entry i j).comp (continuous_subtype_val.comp continuous_subtype_val)
    exact (continuous_pi fun i => h _ _).prodMk ((continuous_skewPart hσ hc hθ hd hd0).comp (h _ _))
  continuous_invFun := by
    refine Continuous.subtype_mk ((isInducing_GU_val hc _).continuous_iff.2 (continuous_matrix fun i j => ?_)) _
    show Continuous fun p : (Fin n → L) × fixK σ => nMat (rowOf σ p.1) p.1 (θ * (rowOf σ p.1 ⬝ᵥ p.1) + d * p.2) i j
    induction i using lineCases <;> induction j using lineCases <;>
      simp only [nMat_zero_zero, nMat_zero_mid, nMat_zero_last, nMat_mid_zero, nMat_mid_mid, nMat_mid_last,
        nMat_last_zero, nMat_last_mid, nMat_last_last, rowOf, dotProduct] <;> fun_prop

include hσ in

def normUnit (u : Lˣ) : (fixK σ)ˣ :=
  Units.mk0 ⟨u * σ u, by show σ _ = _; simp [hσ, mul_comm]⟩ fun e => by simpa using congrArg Subtype.val e

end GlobalTheory.LineUMod
