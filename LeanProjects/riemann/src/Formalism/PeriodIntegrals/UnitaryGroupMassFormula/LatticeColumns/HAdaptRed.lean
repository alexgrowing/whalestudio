import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.OneSubMulOneAdd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.LevelClauseAdaptedBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsMulGL

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

section In

variable (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
  (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

def cV (s : Idx D.R.rS D.R.k) : Idx D.R.rS D.R.k → FpX X p :=
  pr1 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ (idxEquiv X).symm

def aV (s : Idx D.R.rS D.R.k) : Idx D.R.rS D.R.k → FpX X p :=
  (Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ *ᵥ
    (pr2 θ (ratV (F := X.B.I.F) (FpX X p) (vecAt (frameOf X u) s)) ∘ (idxEquiv X).symm)

def yV (i : Fin D.R.k) : Idx D.R.rS D.R.k → FpX X p :=
  pr1 θ (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (PI.MassDataKppVolLemmas.piV X.B.I p.1 (finHA X hb (X.xu u))) :
      GL (Fin X.B.I.n) (TpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) *ᵥ
      PI.FinKW.vecV X.B.I p.1 (X.bw i)) ∘ (idxEquiv X).symm

end In

def AdaptIn (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ P : GL (Idx D.R.rS D.R.k) (FpX X p), LatBasis X p θ (reindex₂ X p P) ∧
    ∃ (l : Idx D.R.rS D.R.k → FpX X p) (o : Idx D.R.rS D.R.k → Fin D.R.k → FpX X p) (uu : FpX X p),
      (∀ s t, ¬ IsW s → ¬ IsW t → aV X u p θ s ⬝ᵥ cV X u p θ t = if t = dlH s then l s else 0) ∧
      (∀ s i, ¬ IsW s → aV X u p θ s ⬝ᵥ yV X hb u p θ i = ((gOf p : ℕ) : FpX X p) * o s i) ∧
      (∀ s, ¬ IsW s → l s ≠ 0) ∧ (∀ s, ¬ IsW s → (l s)⁻¹ ∈ p.1.adicCompletionIntegers X.B.I.F) ∧
      (∀ s i, o s i ∈ p.1.adicCompletionIntegers X.B.I.F) ∧
      IntO (p.1.adicCompletionIntegers X.B.I.F).toSubring
        (((P⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *
          ofCols (colv (cV X u p θ) (yV X hb u p θ))) ∧
      uu ∈ p.1.adicCompletionIntegers X.B.I.F ∧
      (((P⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *
          ofCols (colv (cV X u p θ) (yV X hb u p θ))).det * uu = 1

private theorem mulVec_apply_eq_sum_lattice_columns {ι κ K : Type} [Fintype κ] [Field K] (M : Matrix ι κ K) (v : κ → K)
    (i : ι) : (M *ᵥ v) i = ∑ j, M i j * v j := rfl

private theorem dotProduct_eq_sum_mul {κ K : Type} [Fintype κ] [Field K] (v w : κ → K) :
    v ⬝ᵥ w = ∑ j, v j * w j := rfl

private theorem dotProduct_comm_field {κ K : Type} [Fintype κ] [Field K] (v w : κ → K) :
    v ⬝ᵥ w = w ⬝ᵥ v := by
  rw [dotProduct_eq_sum_mul, dotProduct_eq_sum_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem colv_apply_of_not_isW {r k : ℕ} {K : Type} [Field K] (c : Idx r k → Idx r k → K)
    (y : Fin k → Idx r k → K) (s : Idx r k) (hs : ¬ IsW s) : colv c y s = c s := by
  rcases s with a | ((i | u) | b)
  · rfl
  · exact absurd ⟨i, rfl⟩ hs
  · rfl
  · rfl

private theorem dlH_dlH_lattice_columns {r k : ℕ} (s : Idx r k) : dlH (dlH s) = s := by
  rcases s with a | ((i | u) | b) <;> simp [dlH]

private theorem not_isW_dlH_of_not_isW {r k : ℕ} (s : Idx r k) (hs : ¬ IsW s) : ¬ IsW (dlH s) := by
  rcases s with a | ((i | u) | b)
  · rintro ⟨j, hj⟩
    simp [dlH] at hj
  · exact absurd ⟨i, rfl⟩ hs
  · rintro ⟨j, hj⟩
    simp [dlH] at hj
  · rintro ⟨j, hj⟩
    simp [dlH] at hj

private theorem ofCols_mulVec_single_one {r k : ℕ} {K : Type} [Field K] (v : Idx r k → Idx r k → K)
    (s : Idx r k) : ofCols v *ᵥ Pi.single s 1 = v s := by
  funext i
  rw [mulVec_apply_eq_sum_lattice_columns]
  simp [ofCols, Pi.single_apply]

private theorem ofCols_transpose_mulVec_apply {r k : ℕ} {K : Type} [Field K] (v : Idx r k → Idx r k → K)
    (w : Idx r k → K) (t : Idx r k) : ((ofCols v)ᵀ *ᵥ w) t = v t ⬝ᵥ w := by
  first
  | rfl
  | simp [mulVec_apply_eq_sum_lattice_columns, dotProduct_eq_sum_mul, ofCols, Matrix.transpose_apply]

private theorem ofCols_mulVec_eq_sum_smul {r k : ℕ} {K : Type} [Field K] (v : Idx r k → Idx r k → K)
    (w : Idx r k → K) : ofCols v *ᵥ w = ∑ j, w j • v j := by
  funext i
  rw [mulVec_apply_eq_sum_lattice_columns, Finset.sum_apply]
  simp [ofCols, mul_comm]

private theorem ofCols_colv_zero_mulVec_eq_zero_of_isW {r k : ℕ} {K : Type} [Field K] (z : Fin k → Idx r k → K)
    (w : Idx r k → K) (hw : ∀ j, IsW j → w j = 0) : ofCols (colv (fun _ => 0) z) *ᵥ w = 0 := by
  rw [ofCols_mulVec_eq_sum_smul]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : IsW j
  · rw [hw j hj, zero_smul]
  · simp [colv_apply_of_not_isW _ _ j hj]

private theorem ofCols_colv_zero_mul_self_eq_zero_of_isW {r k : ℕ} {K : Type} [Field K] (z : Fin k → Idx r k → K)
    (hz : ∀ i j, IsW j → z i j = 0) :
    ofCols (colv (fun _ => 0) z) * ofCols (colv (fun _ => 0) z) = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : IsW j
  · by_cases hb : IsW b
    · obtain ⟨i, rfl⟩ := hb
      simp [ofCols, colv, hz i j hj]
    · simp [ofCols, colv_apply_of_not_isW _ _ b hb]
  · simp [ofCols, colv_apply_of_not_isW _ _ j hj]

private theorem mulVec_apply_mem_of_mem {ι κ K : Type} [Fintype κ] [Field K] (S : ValuationSubring K)
    (M : Matrix ι κ K) (hM : ∀ i j, M i j ∈ S) (v : κ → K) (hv : ∀ j, v j ∈ S) (i : ι) :
    (M *ᵥ v) i ∈ S := by
  rw [mulVec_apply_eq_sum_lattice_columns]
  exact sum_mem fun j _ => mul_mem (hM i j) (hv j)

private theorem mulVec_mem_iff_of_mul_eq_one_of_mem {κ K : Type} [Fintype κ] [DecidableEq κ] [Field K] (S : ValuationSubring K)
    (N N' : Matrix κ κ K) (h : N * N' = 1) (hN : ∀ i j, N i j ∈ S) (hN' : ∀ i j, N' i j ∈ S)
    (w : κ → K) : (∀ i, (N' *ᵥ w) i ∈ S) ↔ ∀ i, w i ∈ S := by
  constructor
  · intro hw i
    have hw' : w = N *ᵥ (N' *ᵥ w) := by rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
    rw [hw']
    exact mulVec_apply_mem_of_mem S N hN _ hw i
  · intro hw i
    exact mulVec_apply_mem_of_mem S N' hN' w hw i

private theorem matrix_mul_apply_mem_of_mem {κ K : Type} [Fintype κ] [Field K] (S : ValuationSubring K)
    (M E : Matrix κ κ K) (hM : ∀ i j, M i j ∈ S) (hE : ∀ i j, E i j ∈ S) (i j : κ) :
    (M * E) i j ∈ S := by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hM i l) (hE l j)

private theorem adjugate_apply_mem_of_forall_mem {κ K : Type} [Fintype κ] [DecidableEq κ] [Field K] (S : ValuationSubring K)
    (M : Matrix κ κ K) (hM : ∀ i j, M i j ∈ S) (i j : κ) : M.adjugate i j ∈ S := by
  let M' : Matrix κ κ S.toSubring := fun a b => ⟨M a b, hM a b⟩
  have hMeq : M = (S.toSubring.subtype).mapMatrix M' := by
    ext a b
    rfl
  rw [hMeq, ← RingHom.map_adjugate]
  exact (M'.adjugate i j).2

private theorem latBasis_mul_of_mem_integers_of_inv_mem (X : HidaSetting D) (p : TypX X)
    (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (P R : GL (Fin X.B.I.n) (FpX X p))
    (hR : ∀ i j, (R : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) i j ∈
      p.1.adicCompletionIntegers X.B.I.F)
    (hR' : ∀ i j, ((R⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) i j ∈
      p.1.adicCompletionIntegers X.B.I.F)
    (h : LatBasis X p θ P) : LatBasis X p θ (P * R) := by
  unfold LatBasis at h ⊢
  intro x
  rw [h x]
  have e1 : (((P * R)⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) =
      ((R⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) *
        ((P⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) := by
    rw [mul_inv_rev, Units.val_mul]
  have e2 : ((P * R : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p))ᵀ =
      (R : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p))ᵀ *
        (P : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p))ᵀ := by
    rw [Units.val_mul, Matrix.transpose_mul]
  rw [e1, e2]
  simp only [← Matrix.mulVec_mulVec]
  refine and_congr ?_ ?_
  · refine (mulVec_mem_iff_of_mul_eq_one_of_mem _ (R : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) _ ?_ hR hR' _).symm
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · refine (mulVec_mem_iff_of_mul_eq_one_of_mem _ ((R⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p))ᵀ
      (R : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p))ᵀ ?_ (fun i j => hR' j i) (fun i j => hR j i) _).symm
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]

set_option maxHeartbeats 800000 in

theorem hAdaptQ_of_in (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
    (h : AdaptIn X hb u p) : HAdaptQ X hb u p := by
  classical
  obtain ⟨θ, hθ, P, hP, l, o, uu, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  let cc : Fin D.R.k → Idx D.R.rS D.R.k → FpX X p := fun i t =>
    if IsW t then 0 else -(o (dlH t) i) * (l (dlH t))⁻¹
  let z : Fin D.R.k → Idx D.R.rS D.R.k → FpX X p := fun i t => ((gOf p : ℕ) : FpX X p) * cc i t
  have hccW : ∀ i j, IsW j → cc i j = 0 := fun i j hj => by simp [cc, hj]
  have hz : ∀ i j, IsW j → z i j = 0 := fun i j hj => by simp [z, hccW i j hj]
  have hcc : ∀ i t, cc i t ∈ p.1.adicCompletionIntegers X.B.I.F := by
    intro i t
    by_cases ht : IsW t
    · rw [hccW i t ht]
      exact zero_mem _
    · simp only [cc, if_neg ht]
      exact mul_mem (neg_mem (h5 _ _)) (h4 _ (not_isW_dlH_of_not_isW t ht))
  have hgO : ((gOf p : ℕ) : FpX X p) ∈ p.1.adicCompletionIntegers X.B.I.F := natCast_mem _ _
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p),
      A = ofCols (colv (cV X u p θ) (yV X hb u p θ)) := ⟨_, rfl⟩
  obtain ⟨Nn, hNn⟩ : ∃ Nn : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p),
      Nn = ofCols (colv (fun _ => 0) z) := ⟨_, rfl⟩
  rw [← hA] at h6 h8
  have hsq : Nn * Nn = 0 := by
    rw [hNn]
    exact ofCols_colv_zero_mul_self_eq_zero_of_isW z hz
  have hE1 : (1 + Nn) * (1 - Nn) = 1 := by
    first
    | simp [add_mul, mul_sub, hsq]
    | rw [add_mul, one_mul, mul_sub, mul_one, hsq, sub_zero, sub_add_cancel]
  have hE2 : (1 - Nn) * (1 + Nn) = 1 := by
    first
    | simp [sub_mul, mul_add, hsq]
    | rw [sub_mul, one_mul, mul_add, mul_one, hsq, add_zero, sub_sub_cancel_left, add_neg_cancel]
  have hAdet : IsUnit A.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [Matrix.det_mul, h0, mul_zero, zero_mul] at h8
    exact zero_ne_one h8
  let Eu : GL (Idx D.R.rS D.R.k) (FpX X p) := ⟨1 + Nn, 1 - Nn, hE1, hE2⟩
  let Q : GL (Idx D.R.rS D.R.k) (FpX X p) := Matrix.nonsingInvUnit A hAdet * Eu
  have hQ : (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) = A * (1 + Nn) := rfl
  have hAs : ∀ s, ¬ IsW s → A *ᵥ Pi.single s 1 = cV X u p θ s := fun s hs => by
    rw [hA, ofCols_mulVec_single_one, colv_apply_of_not_isW _ _ s hs]
  have hAw : ∀ i, A *ᵥ Pi.single (wI i) 1 = yV X hb u p θ i := fun i => by
    rw [hA, ofCols_mulVec_single_one]
    rfl
  have hNs : ∀ s, ¬ IsW s → Nn *ᵥ Pi.single s 1 = 0 := fun s hs => by
    rw [hNn, ofCols_mulVec_single_one, colv_apply_of_not_isW _ _ s hs]
  have hNw : ∀ i, Nn *ᵥ Pi.single (wI i) 1 = z i := fun i => by
    rw [hNn, ofCols_mulVec_single_one]
    rfl
  have hQs : ∀ s, ¬ IsW s →
      (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ Pi.single s 1 = cV X u p θ s :=
    fun s hs => by
      rw [hQ, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hNs s hs, add_zero, hAs s hs]
  have hM : ∀ a b, (((P⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) :
      Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) * A) a b ∈
      p.1.adicCompletionIntegers X.B.I.F := h6
  have hNint : ∀ a b, Nn a b ∈ p.1.adicCompletionIntegers X.B.I.F := by
    intro a b
    rw [hNn]
    show colv (fun _ => 0) z b a ∈ _
    by_cases hb' : IsW b
    · obtain ⟨i, rfl⟩ := hb'
      exact mul_mem hgO (hcc i a)
    · rw [colv_apply_of_not_isW _ _ b hb']
      exact zero_mem _
  have hEint : ∀ a b, (1 + Nn : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) a b ∈
      p.1.adicCompletionIntegers X.B.I.F := by
    intro a b
    rw [Matrix.add_apply, Matrix.one_apply]
    refine add_mem ?_ (hNint a b)
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hEint' : ∀ a b, (1 - Nn : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) a b ∈
      p.1.adicCompletionIntegers X.B.I.F := by
    intro a b
    rw [Matrix.sub_apply, Matrix.one_apply]
    refine sub_mem ?_ (hNint a b)
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hR0 : ∀ a b, ((P⁻¹ * Q : GL (Idx D.R.rS D.R.k) (FpX X p)) :
      Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) a b ∈ p.1.adicCompletionIntegers X.B.I.F := by
    intro a b
    rw [Units.val_mul, hQ, ← Matrix.mul_assoc]
    exact matrix_mul_apply_mem_of_mem _ _ _ hM hEint a b
  have hR0' : ∀ a b, (((P⁻¹ * Q)⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) :
      Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) a b ∈ p.1.adicCompletionIntegers X.B.I.F := by
    intro a b
    rw [Matrix.coe_units_inv, Units.val_mul, hQ, ← Matrix.mul_assoc, Matrix.mul_inv_rev,
      Matrix.inv_eq_right_inv hE1]
    refine matrix_mul_apply_mem_of_mem _ _ _ hEint' ?_ a b
    intro c d
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    have hinv : Ring.inverse (((P⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) :
        Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) * A).det = uu := by
      rw [Ring.inverse_eq_inv]
      exact (eq_inv_of_mul_eq_one_right h8).symm
    rw [hinv]
    exact mul_mem h7 (adjugate_apply_mem_of_forall_mem _ _ hM c d)
  unfold HAdaptQ
  refine ⟨θ, hθ, Q, l, h3, fun s hs => ?_, fun s hs => ?_, ?_, ?_⟩
  · change ((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) :
        Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ cV X u p θ s = Pi.single s 1
    rw [← hQs s hs, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · change (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p))ᵀ *ᵥ aV X u p θ s =
        l s • Pi.single (dlH s) 1
    have hw : ∀ t, (Aᵀ *ᵥ aV X u p θ s) t =
        colv (cV X u p θ) (yV X hb u p θ) t ⬝ᵥ aV X u p θ s := fun t => by
      rw [hA]
      exact ofCols_transpose_mulVec_apply _ _ t
    have hwn : ∀ t, ¬ IsW t → (Aᵀ *ᵥ aV X u p θ s) t = if t = dlH s then l s else 0 :=
      fun t ht => by
        rw [hw, colv_apply_of_not_isW _ _ t ht, dotProduct_comm_field]
        exact h1 s t hs ht
    have hww : ∀ i, (Aᵀ *ᵥ aV X u p θ s) (wI i) = ((gOf p : ℕ) : FpX X p) * o s i := fun i => by
      rw [hw, dotProduct_comm_field]
      exact h2 s i hs
    have hNT : ∀ (v : Idx D.R.rS D.R.k → FpX X p) t, (Nnᵀ *ᵥ v) t = colv (fun _ => 0) z t ⬝ᵥ v :=
      fun v t => by
        rw [hNn]
        exact ofCols_transpose_mulVec_apply _ _ t
    have hdn := not_isW_dlH_of_not_isW s hs
    rw [hQ, Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
    funext t
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, hNT]
    by_cases ht : IsW t
    · obtain ⟨i, rfl⟩ := ht
      have hne : (wI i : Idx D.R.rS D.R.k) ≠ dlH s := fun heq => hdn ⟨i, heq.symm⟩
      rw [hww]
      change _ + z i ⬝ᵥ _ = _
      rw [dotProduct_eq_sum_mul, Finset.sum_eq_single (dlH s)]
      · rw [hwn _ hdn, if_pos rfl]
        simp only [z, cc, if_neg hdn, dlH_dlH_lattice_columns, Pi.smul_apply, Pi.single_apply, if_neg hne,
          smul_eq_mul, mul_zero]
        linear_combination (-(((gOf p : ℕ) : FpX X p) * o s i)) * mul_inv_cancel₀ (h3 s hs)
      · intro j _ hj
        by_cases hjW : IsW j
        · rw [hz i j hjW, zero_mul]
        · rw [hwn j hjW, if_neg hj, mul_zero]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    · rw [colv_apply_of_not_isW _ _ t ht, dotProduct_eq_sum_mul, hwn t ht]
      by_cases hts : t = dlH s
      · subst hts
        simp
      · simp [Pi.single_apply, hts]
  · have hQP : Q = P * (P⁻¹ * Q) := (mul_inv_cancel_left P Q).symm
    rw [hQP]
    have hmap : reindex₂ X p (P * (P⁻¹ * Q)) = reindex₂ X p P * reindex₂ X p (P⁻¹ * Q) := by
      unfold reindex₂
      exact map_mul _ _ _
    rw [hmap]
    refine latBasis_mul_of_mem_integers_of_inv_mem X p θ _ _ ?_ ?_ hP
    · intro i j
      first
      | exact hR0 _ _
      | (unfold reindex₂; simp only [Units.coe_map]; exact hR0 _ _)
    · intro i j
      unfold reindex₂
      rw [← map_inv]
      first
      | exact hR0' _ _
      | (simp only [Units.coe_map]; exact hR0' _ _)
  · intro i
    refine ⟨fun t => ⟨cc i t, hcc i t⟩, ?_⟩
    change (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ Pi.single (wI i) 1 -
        yV X hb u p θ i =
      ((gOf p : ℕ) : FpX X p) • ((Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ cc i)
    rw [hQ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hNw,
      hNn, ofCols_colv_zero_mulVec_eq_zero_of_isW z (cc i) (hccW i), add_zero, Matrix.mulVec_add, hAw, add_sub_cancel_left,
      ← Matrix.mulVec_smul]
    try rfl

def AdaptInAll : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ p : TypX X, AdaptIn X hb u p

theorem hAdaptAll_of (h : AdaptInAll) : HAdaptAll := by
  unfold HAdaptAll
  intro D X hb hK u hM hL p
  exact hAdaptQ_of_in X hb u p (h X hb hK u hM hL p)

end PIW.MassDataColumns
