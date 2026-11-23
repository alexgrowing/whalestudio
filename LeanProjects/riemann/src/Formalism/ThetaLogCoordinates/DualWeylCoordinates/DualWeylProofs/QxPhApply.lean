import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StripDataTensorColumnFamilies
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QbIndepField

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
  {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
  {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ}

lemma qx_ps_equiv (hd : IsStripData B be Str ps) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : nu ∈ Str mu)
    (K : TIdx mu) (k : κ) (I : TIdx nu) :
    ∑ y : TIdx mu × κ, TMat mu K y.1 * B k y.2 * (ps mu nu y I : GLCoord ℤ n) =
      ∑ I', (ps mu nu (K, k) I' : GLCoord ℤ n) * TMat nu I' I :=
  congrFun (congrFun (hd.2.2.2.1 mu hmu nu hnu) (K, k)) I

lemma qx_wt (hd : IsStripData B be Str ps) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : nu ∈ Str mu)
    (K : TIdx mu) (k : κ) (I : TIdx nu) (h : ps mu nu (K, k) I ≠ 0) :
    qb_wtT mu K + be k = qb_wtT nu I := by
  have h1 := congrArg (evGL (torusPt n)) (qx_ps_equiv hd hmu hnu K k I)
  simp only [map_sum, map_mul, map_intCast, qb_evGL_torus_TMat, hd.2.1, Fintype.sum_prod_type,
    ite_mul, zero_mul, mul_ite, mul_zero, sum_ite_eq, sum_ite_eq', mem_univ, if_true,
    AddMonoidAlgebra.single_mul_single, one_mul] at h1
  by_contra hne
  have h2 := congrArg (fun x => x.coeff (qb_wtT nu I)) h1
  simp only [← zsmul_eq_mul', ← zsmul_eq_mul, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul, if_neg hne, if_true, mul_zero, mul_one] at h2
  exact h h2.symm

lemma qx_wt_can (hd : IsStripData B be Str ps) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : nu ∈ Str mu)
    (K : TIdx mu) (k : κ) (h : ps mu nu (K, k) (canT nu) ≠ 0) : qb_wtT mu K = nu - be k := by
  have h1 := qx_wt hd hmu hnu K k _ h
  rw [qb_wtT_can (hd.2.2.1 mu hmu nu hnu)] at h1
  rw [← h1, add_sub_cancel_right]

variable {M M' : GLMod n}

abbrev qx_J (Str : (Fin n → ℤ) → Finset (Fin n → ℤ)) (CF : ColFam M) : Type :=
  Σ j : CF.J, ↥(Str (CF.mu j))

def qx_ph (ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ) (e : M'.ι ≃ M.ι × κ) (CF : ColFam M)
    (x : qx_J Str CF) : Matrix M'.ι (TIdx (x.2 : Fin n → ℤ)) ℤ :=
  fun i I => ∑ K : TIdx (CF.mu x.1), CF.ph x.1 (e i).1 K * ps (CF.mu x.1) x.2 (K, (e i).2) I

lemma qx_ph_apply (e : M'.ι ≃ M.ι × κ) (CF : ColFam M) (x : qx_J Str CF) (i : M'.ι)
    (I : TIdx (x.2 : Fin n → ℤ)) :
    qx_ph ps e CF x i I = ∑ K : TIdx (CF.mu x.1), CF.ph x.1 (e i).1 K * ps (CF.mu x.1) x.2 (K, (e i).2) I := rfl

lemma qx_equiv (hd : IsStripData B be Str ps) (e : M'.ι ≃ M.ι × κ) (hT : IsTensor M M' B e) (CF : ColFam M)
    (x : qx_J Str CF) (i : M'.ι) (I : TIdx (x.2 : Fin n → ℤ)) :
    ∑ k, M'.A i k * (qx_ph ps e CF x k I : GLCoord ℤ n) =
      ∑ I', (qx_ph ps e CF x i I' : GLCoord ℤ n) * TMat (x.2 : Fin n → ℤ) I' I := by
  obtain ⟨j, nu, hnu⟩ := x
  have hmu := CF.dom j
  have hT' : ∀ i j, M'.A i j = M.A (e i).1 (e j).1 * B (e i).2 (e j).2 := hT
  simp only [qx_ph_apply, hT', Int.cast_sum, Int.cast_mul]
  rw [← e.symm.sum_comp]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  calc ∑ m, ∑ k, M.A (e i).1 m * B (e i).2 k *
        ∑ K, (CF.ph j m K : GLCoord ℤ n) * (ps (CF.mu j) nu (K, k) I : GLCoord ℤ n)
      = ∑ K, ∑ k, (∑ m, M.A (e i).1 m * (CF.ph j m K : GLCoord ℤ n)) * (B (e i).2 k *
          (ps (CF.mu j) nu (K, k) I : GLCoord ℤ n)) := by
        simp only [mul_sum, sum_mul]
        rw [sum_comm]
        conv_lhs => enter [2, k]; rw [sum_comm]
        rw [sum_comm]
        refine sum_congr rfl fun K _ => sum_congr rfl fun k _ => sum_congr rfl fun m _ => by ring
    _ = ∑ K', (CF.ph j (e i).1 K' : GLCoord ℤ n) * ∑ y : TIdx (CF.mu j) × κ,
          TMat (CF.mu j) K' y.1 * B (e i).2 y.2 * (ps (CF.mu j) nu y I : GLCoord ℤ n) := by
        simp only [qb_equiv_apply, Fintype.sum_prod_type, mul_sum, sum_mul]
        rw [sum_comm]
        conv_lhs => enter [2, k]; rw [sum_comm]
        rw [sum_comm]
        conv_lhs => enter [2, k]; rw [sum_comm]
        refine sum_congr rfl fun K' _ => sum_congr rfl fun K _ => sum_congr rfl fun k _ => by ring
    _ = _ := by
        simp only [qx_ps_equiv hd hmu hnu, mul_sum, sum_mul]
        rw [sum_comm]
        refine sum_congr rfl fun I' _ => sum_congr rfl fun K _ => by ring

lemma qx_rank (hd : IsStripData B be Str ps) (e : M'.ι ≃ M.ι × κ) (CF : ColFam M) :
    Fintype.card M'.ι = ∑ x : qx_J Str CF, dMu (x.2 : Fin n → ℤ) := by
  rw [Fintype.card_congr e, Fintype.card_prod, CF.rank, sum_mul, Fintype.sum_sigma]
  refine sum_congr rfl fun j _ => ?_
  rw [hd.2.2.2.2.2 _ (CF.dom j)]
  exact (Finset.sum_coe_sort (Str (CF.mu j)) dMu).symm

end Formalism.InvariantFactorPaths.ColumnFamilies
