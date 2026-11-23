import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.AnnAnti
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLevelInverseCongruence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir ValuativeRel

namespace PositivityTheory.RgUd.Form.LeviSmoothness.stab

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem vmv_sq {m : ℕ} (η : Fin (m + 1) → k) :
    vecMulVec (xi0 k m) η * vecMulVec (xi0 k m) η = η (Fin.last m) • vecMulVec (xi0 k m) η := by
  ext i j
  simp [Matrix.mul_apply, vecMulVec_apply, xi0, Pi.single_apply, mul_comm, mul_left_comm]

theorem inv_pair {m : ℕ} (E : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (a c : k) (hE : E * E = a • E)
    (hc : c * (1 + a) = 1) : (1 + E) * (1 - c • E) = 1 ∧ (1 - c • E) * (1 + E) = 1 := by
  have h : E = c • E + (c * a) • E := by
    rw [← add_smul, ← mul_one_add, hc, one_smul]
  constructor
  · rw [add_mul, one_mul, mul_sub, mul_one, mul_smul_comm, hE, smul_smul]
    have h2 : E - (c * a) • E = c • E := by
      rw [sub_eq_iff_eq_add]
      exact h
    rw [sub_add_eq_add_sub, add_sub_assoc, h2, sub_self, add_zero]
  · rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hE, smul_smul, ← h, add_sub_cancel_right]

def gU {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) : GL (Fin (m + 1)) k :=
  ⟨1 + vecMulVec (xi0 k m) η, 1 - (1 + η (Fin.last m))⁻¹ • vecMulVec (xi0 k m) η,
    (inv_pair _ _ _ (vmv_sq η) (inv_mul_cancel₀ hη)).1, (inv_pair _ _ _ (vmv_sq η) (inv_mul_cancel₀ hη)).2⟩

theorem gU_val {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) :
    ((gU η hη : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = 1 + vecMulVec (xi0 k m) η := rfl

theorem gU_inv_val {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) :
    (((gU η hη)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      1 - (1 + η (Fin.last m))⁻¹ • vecMulVec (xi0 k m) η := rfl

theorem gU_transpose {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) :
    ((gU η hη : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵀ *ᵥ xi0 k m = xi0 k m + η := by
  funext i
  simp [gU_val, Matrix.transpose_add, Matrix.add_mulVec, Matrix.transpose_vecMulVec, Matrix.mulVec,
    dotProduct, vecMulVec_apply, xi0, Pi.single_apply]
  by_cases h : i = Fin.last m
  · subst h
    simp
  · simp [h, Matrix.one_apply_ne (Ne.symm h)]

theorem gU_det {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) :
    ((Matrix.GeneralLinearGroup.det (gU η hη) : kˣ) : k) = 1 + η (Fin.last m) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, gU_val, vecMulVec_eq Unit,
    det_one_add_replicateCol_mul_replicateRow]
  simp [xi0, dotProduct_single]

theorem val_dot_le {n : ℕ} (a x : Fin n → k) (γ : ValueGroupWithZero k) (ha : ∀ i, valuation k (a i) ≤ 1)
    (hx : ∀ i, valuation k (x i) ≤ γ) : valuation k (a ⬝ᵥ x) ≤ γ := by
  simp only [dotProduct]
  refine Valuation.map_sum_le _ (fun i _ => ?_)
  rw [Valuation.map_mul]
  calc _ ≤ 1 * γ := mul_le_mul' (ha i) (hx i)
    _ = γ := one_mul γ

theorem vmv_mulVec_apply {m : ℕ} (u v w : Fin (m + 1) → k) (i : Fin (m + 1)) :
    (vecMulVec u v *ᵥ w) i = u i * (v ⬝ᵥ w) := by
  simp [mulVec, vecMulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem mem_ball_of {m : ℕ} (c : k) (η x : Fin (m + 1) → k) (hc : valuation k c ≤ 1) (hη : ∀ i, valuation k (η i) ≤ 1)
    (s : kˣ) (hx : x ∈ ball (m + 1) s) : (1 + c • vecMulVec (xi0 k m) η) *ᵥ x ∈ ball (m + 1) s := by
  have hx' : ∀ i, valuation k (x i) ≤ valuation k (s : k) := hx
  show ∀ i, valuation k (((1 + c • vecMulVec (xi0 k m) η) *ᵥ x) i) ≤ valuation k (s : k)
  intro i
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Matrix.smul_mulVec, Pi.smul_apply,
    vmv_mulVec_apply, smul_eq_mul]
  refine Valuation.map_add_le _ (hx' i) ?_
  rw [Valuation.map_mul, Valuation.map_mul]
  have hu : valuation k (xi0 k m i) ≤ 1 := by
    unfold xi0
    rw [Pi.single_apply]
    split_ifs <;> simp
  have hd := val_dot_le η x _ hη hx'
  calc _ ≤ 1 * (1 * valuation k (s : k)) := mul_le_mul' hc (mul_le_mul' hu hd)
    _ = _ := by rw [one_mul, one_mul]

theorem good_nbhd_pf {m : ℕ} (K : Subgroup (GL (Fin (m + 1)) k)) (hK : IsOpen (K : Set (GL (Fin (m + 1)) k))) :
    ∃ D ∈ nhds (0 : Fin (m + 1) → k), ∀ η ∈ D, ∃ g ∈ K, nabs k (Matrix.GeneralLinearGroup.det g) = 1 ∧
      (∀ s : kˣ, pre g⁻¹ (ball (m + 1) s) = ball (m + 1) s) ∧
      ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵀ *ᵥ xi0 k m = xi0 k m + η := by
  have hv : {x : k | valuation k x < 1} ∈ nhds (0 : k) :=
    (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun x hx => by simpa using hx⟩
  have hS : {η : Fin (m + 1) → k | ∀ i, valuation k (η i) < 1} ∈ nhds (0 : Fin (m + 1) → k) := by
    simp only [Set.setOf_forall]
    refine Filter.iInter_mem.2 fun i => ?_
    have h1 : (fun η : Fin (m + 1) → k => η i) ⁻¹' {x : k | valuation k x < 1} ∈
        nhds (0 : Fin (m + 1) → k) :=
      ((continuous_apply i).tendsto (0 : Fin (m + 1) → k)) hv
    exact h1
  obtain ⟨U, hU, hUK⟩ := isOpen_induced_iff.1 hK
  let F : (Fin (m + 1) → k) →
      Matrix (Fin (m + 1)) (Fin (m + 1)) k × (Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵐᵒᵖ :=
    fun η => (1 + vecMulVec (xi0 k m) η,
      MulOpposite.op (1 - (1 + η (Fin.last m))⁻¹ • vecMulVec (xi0 k m) η))
  have hF : ContinuousAt F 0 := by
    have hE : Continuous fun η : Fin (m + 1) → k => vecMulVec (xi0 k m) η :=
      Continuous.matrix_vecMulVec continuous_const continuous_id
    have h2 : ContinuousAt (fun η : Fin (m + 1) → k => (1 + η (Fin.last m))⁻¹) 0 :=
      ContinuousAt.inv₀ (continuous_const.add (continuous_apply _)).continuousAt (by simp)
    have h3 : ContinuousAt
        (fun η : Fin (m + 1) → k => 1 - (1 + η (Fin.last m))⁻¹ • vecMulVec (xi0 k m) η) 0 :=
      continuousAt_const.sub (h2.smul hE.continuousAt)
    exact ContinuousAt.prodMk (continuous_const.add hE).continuousAt
      (MulOpposite.continuous_op.continuousAt.comp h3)
  have h0 : F 0 ∈ U := by
    have h1 : (1 : GL (Fin (m + 1)) k) ∈ (K : Set (GL (Fin (m + 1)) k)) := K.one_mem
    rw [← hUK] at h1
    have e : F 0 = Units.embedProduct _ (1 : GL (Fin (m + 1)) k) :=
      Prod.ext (by simp [F]) (MulOpposite.unop_injective (by simp [F]))
    rw [e]
    exact h1
  refine ⟨F ⁻¹' U ∩ {η | ∀ i, valuation k (η i) < 1},
    Filter.inter_mem (hF.preimage_mem_nhds (hU.mem_nhds h0)) hS, ?_⟩
  rintro η ⟨hηU, hηv⟩
  have hl : valuation k (1 + η (Fin.last m)) = 1 := Valuation.map_one_add_of_lt _ (hηv _)
  have hne : 1 + η (Fin.last m) ≠ 0 := by
    intro h
    rw [h, map_zero] at hl
    exact zero_ne_one hl
  have hη1 : ∀ i, valuation k (η i) ≤ 1 := fun i => (hηv i).le
  refine ⟨(gU η hne)⁻¹, ?_, ?_, ?_, ?_⟩
  · apply K.inv_mem
    have e : Units.embedProduct _ (gU η hne) = F η :=
      Prod.ext (gU_val η hne) (MulOpposite.unop_injective (gU_inv_val η hne))
    have h1 : gU η hne ∈ Units.embedProduct _ ⁻¹' U := by
      show Units.embedProduct _ (gU η hne) ∈ U
      rw [e]
      exact hηU
    rw [hUK] at h1
    exact h1
  · rw [GlobalTheory.SplitWeil.nabs_eq_one_iff, map_inv, Units.val_inv_eq_inv_val, gU_det, map_inv₀, hl, inv_one]
  · intro s
    rw [inv_inv]
    ext x
    simp only [pre, AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, gU_val]
    constructor
    · intro hx
      have hc' : valuation k (-(1 + η (Fin.last m))⁻¹) ≤ 1 := by
        rw [Valuation.map_neg, map_inv₀, hl, inv_one]
      have hmul : (1 + (-(1 + η (Fin.last m))⁻¹) • vecMulVec (xi0 k m) η) *
          (1 + vecMulVec (xi0 k m) η) = 1 := by
        rw [neg_smul, ← sub_eq_add_neg]
        exact (inv_pair _ _ _ (vmv_sq η) (inv_mul_cancel₀ hne)).2
      have h1 := mem_ball_of _ η _ hc' hη1 s hx
      rwa [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec] at h1
    · intro hx
      have h1 := mem_ball_of 1 η x (map_one (valuation k)).le hη1 s hx
      rwa [one_smul] at h1
  · rw [inv_inv]
    exact gU_transpose η hne

end PositivityTheory.RgUd.Form.LeviSmoothness.stab
