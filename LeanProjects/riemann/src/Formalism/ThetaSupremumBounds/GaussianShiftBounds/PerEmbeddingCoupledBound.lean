import Mathlib
import Formalism.ThetaSupremumBounds.StatementCB
import Formalism.ThetaSupremumBounds.DivIneqRecordTwoConst6
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DescendedNorm

open Finset NumberField
open scoped Real

namespace Formalism.DimensionVariation

open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues (fnorm chainFun chainMat)

namespace CB

theorem card_sigma_le {AA : Type} [Fintype AA] (Cl : AA → Type) [∀ a, Fintype (Cl a)] (h : ℝ)
    (hh : ∀ a, (Fintype.card (Cl a) : ℝ) ≤ h) :
    (Fintype.card (Σ a, Cl a) : ℝ) ≤ (Fintype.card AA : ℝ) * h := by
  rw [Fintype.card_sigma]
  push_cast
  calc (∑ a, (Fintype.card (Cl a) : ℝ)) ≤ ∑ _a : AA, h := Finset.sum_le_sum (fun a _ => hh a)
    _ = (Fintype.card AA : ℝ) * h := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem const_le {AA AA' : Type} [Fintype AA] [Fintype AA'] (Cl : AA → Type) (Cl' : AA' → Type)
    [∀ a, Fintype (Cl a)] [∀ b, Fintype (Cl' b)] (h h' t : ℝ) (ht : 0 ≤ t)
    (hh : ∀ a, (Fintype.card (Cl a) : ℝ) ≤ h) (hh' : ∀ b, (Fintype.card (Cl' b) : ℝ) ≤ h') :
    ((Fintype.card (Σ a, Cl a) : ℝ) * (Fintype.card (Σ b, Cl' b) : ℝ)) * t ≤
      cbSq (Fintype.card AA) (Fintype.card AA') h h' t := by
  have h1 := card_sigma_le Cl h hh
  have h2 := card_sigma_le Cl' h' hh'
  have h3 : ((Fintype.card (Σ a, Cl a) : ℝ) * (Fintype.card (Σ b, Cl' b) : ℝ)) ≤
      ((Fintype.card AA : ℝ) * h) * ((Fintype.card AA' : ℝ) * h') :=
    mul_le_mul h1 h2 (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) h1)
  have h4 := mul_le_mul_of_nonneg_right h3 ht
  unfold cbSq
  calc _ ≤ _ := h4
    _ = _ := by ring

theorem cbSq_nonneg {AA AA' : Type} [Fintype AA] [Fintype AA'] (Cl : AA → Type) (Cl' : AA' → Type)
    [∀ a, Fintype (Cl a)] [∀ b, Fintype (Cl' b)] (h h' t : ℝ) (ht : 0 ≤ t)
    (hh : ∀ a, (Fintype.card (Cl a) : ℝ) ≤ h) (hh' : ∀ b, (Fintype.card (Cl' b) : ℝ) ≤ h') :
    0 ≤ cbSq (Fintype.card AA) (Fintype.card AA') h h' t :=
  le_trans (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ht)
    (const_le Cl Cl' h h' t ht hh hh')

theorem pos_pair {a b : ℝ} (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a ∧ 0 < b := by
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with h' | h'
  · exact h'
  · exact absurd hb (not_le.mpr h'.2)

open Formalism.DivisionValues.OperatorNormFrames in
theorem nrm_le_sqrt {a b : ℕ} (X : Matrix (Fin a) (Fin a) ℂ) (X' : Matrix (Fin b) (Fin b) ℂ)
    (hX : IsUnit X.det) (M : Matrix (Fin b) (Fin a) ℂ) (Bd : ℝ) (hB : 0 ≤ Bd)
    (h : ∀ y, fnorm X' (M.mulVec y) ^ 2 ≤ Bd * fnorm X y ^ 2) :
    nrm (X'⁻¹ * M * X) ≤ Real.sqrt Bd := by
  unfold nrm
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun z => ?_)
  have key : ∀ (A' : Matrix (Fin b) (Fin a) ℂ),
      ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A')) z‖ =
        Formalism.HermitianLatticesTheory.cnorm (A'.mulVec (fun i => z i)) := by
    intro A'
    rw [EuclideanSpace.norm_eq]
    rfl
  have hz : ‖z‖ = Formalism.HermitianLatticesTheory.cnorm (fun i => z i) := by
    rw [EuclideanSpace.norm_eq]
    rfl
  rw [key, hz]
  have e1 : (X'⁻¹ * M * X).mulVec (fun i => z i) = X'⁻¹.mulVec (M.mulVec (X.mulVec (fun i => z i))) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have e2 : X⁻¹.mulVec (X.mulVec (fun i => z i)) = (fun i => z i) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul X hX, Matrix.one_mulVec]
  have hy := h (X.mulVec (fun i => z i))
  unfold Formalism.DivisionValues.fnorm at hy
  rw [e2, ← e1] at hy
  have c0 : 0 ≤ Formalism.HermitianLatticesTheory.cnorm ((X'⁻¹ * M * X).mulVec (fun i => z i)) := Real.sqrt_nonneg _
  have c1 : 0 ≤ Formalism.HermitianLatticesTheory.cnorm (fun i => z i) := Real.sqrt_nonneg _
  rw [← Real.sqrt_sq c0, ← Real.sqrt_sq c1, ← Real.sqrt_mul hB]
  exact Real.sqrt_le_sqrt hy

end CB

open CB

theorem sharp_norm : SharpNorm := by
  intro AA AA' _ _ Cl Cl' _ _ A B _ _ _ _ γ γ' ε T h h' tmax hγ hγ' hε hT ht hh hh'
  have hPQ : (Fintype.card (Σ a, Cl a) : ℝ) * (Fintype.card (Σ b, Cl' b) : ℝ) * tmax ≤
      cbSq (Fintype.card AA) (Fintype.card AA') h h' tmax :=
    const_le Cl Cl' h h' tmax ht hh hh'
  have hcb0 : 0 ≤ cbSq (Fintype.card AA) (Fintype.card AA') h h' tmax :=
    cbSq_nonneg Cl Cl' h h' tmax ht hh hh'
  have hsumγ : ∑ p, γ p ≤ (Fintype.card (Σ a, Cl a) : ℝ) := by
    calc ∑ p, γ p ≤ ∑ _p : (Σ a, Cl a), (1 : ℝ) := Finset.sum_le_sum (fun p _ => (hγ p).2)
      _ = (Fintype.card (Σ a, Cl a) : ℝ) := by simp
  have key : ∀ G : (Σ a, Cl a) → A, ∀ q, ‖liftOp γ ε T G q‖ ^ 2 ≤
      tmax * ((Fintype.card (Σ a, Cl a) : ℝ) * ∑ p, γ p * ‖G p‖ ^ 2) := by
    intro G q
    have h1 : ‖liftOp γ ε T G q‖ ≤ ∑ p, γ p * (Real.sqrt tmax * ‖G p‖) := by
      unfold liftOp
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun p _ => ?_))
      rw [norm_smul, norm_mul, hε p q, mul_one, Complex.norm_real, Real.norm_of_nonneg (hγ p).1.le]
      refine mul_le_mul_of_nonneg_left ?_ (hγ p).1.le
      refine le_trans (ContinuousLinearMap.le_opNorm _ _) (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact le_of_eq_of_le (abs_of_nonneg (norm_nonneg _)).symm (Real.abs_le_sqrt (hT p q))
    have h2 : (∑ p, γ p * (Real.sqrt tmax * ‖G p‖)) = Real.sqrt tmax * ∑ p, γ p * ‖G p‖ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    have h3 : (∑ p, γ p * ‖G p‖) ^ 2 ≤ (∑ p, γ p) * ∑ p, γ p * ‖G p‖ ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul _ (fun p _ => (hγ p).1.le)
        (fun p _ => mul_nonneg (hγ p).1.le (sq_nonneg _)) (fun p _ => by ring)
    have hS : 0 ≤ ∑ p, γ p * ‖G p‖ ^ 2 :=
      Finset.sum_nonneg (fun p _ => mul_nonneg (hγ p).1.le (sq_nonneg _))
    rw [h2] at h1
    calc ‖liftOp γ ε T G q‖ ^ 2 ≤ (Real.sqrt tmax * ∑ p, γ p * ‖G p‖) ^ 2 :=
          sq_le_sq' (by linarith [norm_nonneg (liftOp γ ε T G q)]) h1
      _ = tmax * (∑ p, γ p * ‖G p‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt ht]
      _ ≤ tmax * ((∑ p, γ p) * ∑ p, γ p * ‖G p‖ ^ 2) := mul_le_mul_of_nonneg_left h3 ht
      _ ≤ tmax * ((Fintype.card (Σ a, Cl a) : ℝ) * ∑ p, γ p * ‖G p‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsumγ hS) ht
  have bound : ∀ G : (Σ a, Cl a) → A, (∑ q, γ' q * ‖liftOp γ ε T G q‖ ^ 2) ≤
      cbSq (Fintype.card AA) (Fintype.card AA') h h' tmax * ∑ p, γ p * ‖G p‖ ^ 2 := by
    intro G
    have hS : 0 ≤ ∑ p, γ p * ‖G p‖ ^ 2 :=
      Finset.sum_nonneg (fun p _ => mul_nonneg (hγ p).1.le (sq_nonneg _))
    calc (∑ q, γ' q * ‖liftOp γ ε T G q‖ ^ 2)
        ≤ ∑ _q : (Σ b, Cl' b), tmax * ((Fintype.card (Σ a, Cl a) : ℝ) * ∑ p, γ p * ‖G p‖ ^ 2) :=
          Finset.sum_le_sum (fun q _ =>
            le_trans (mul_le_of_le_one_left (sq_nonneg _) (hγ' q).2) (key G q))
      _ = (Fintype.card (Σ a, Cl a) : ℝ) * (Fintype.card (Σ b, Cl' b) : ℝ) * tmax *
            ∑ p, γ p * ‖G p‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hPQ hS
  refine ⟨bound, ?_⟩
  unfold liftNormSq
  exact csInf_le ⟨0, fun X hX => hX.1⟩ ⟨hcb0, bound⟩

theorem lift_sharp_bound : LiftSharpBound := by
  intro Pl ι AA AA' _ _ _ _ Cl Cl' _ _ A B _ _ _ _ _ r ν n s Th c Rc lam Om S γ γ' ε h h'
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hγ hγ' hε hh hh'
  refine (liftOperatorBound Pl ι (Σ a, Cl a) (Σ b, Cl' b) A B r ν n s Th c Rc lam Om S γ γ' ε
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hγ hγ' hε).trans (const_le Cl Cl' h h' _ ?_ hh hh')
  have : ∀ τ, 0 < (Om τ)⁻¹ ^ n τ *
      (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * Fintype.card ι) * Real.exp (∑ i, ph (ν τ i))) := by
    intro τ
    have := h10 τ
    positivity
  have hP := Finset.prod_pos (fun τ (_ : τ ∈ Finset.univ) => this τ)
  positivity

open Formalism.DivisionValues.OperatorNormFrames in
theorem chain_coupled_bound : ChainCB := by
  intro K _ _ _ m c Xc Kj AA Cl _ _ W _ _ γ Φ ε T hcl tmax hyp kU hkU
  obtain ⟨hX, hγ, hΦ, hint, hε, hT, ht0, hh⟩ := hyp
  have hnn : ∀ j v, 0 ≤ cbSq (Fintype.card (AA j.castSucc)) (Fintype.card (AA j.succ))
      (hcl j.castSucc) (hcl j.succ) (tmax j v) := fun j v =>
    cbSq_nonneg (Cl j.castSucc) (Cl j.succ) _ _ _ (ht0 j v) (hh _) (hh _)
  have hop : ∀ j v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ≤ kU j v := by
    intro j v
    rw [hkU, opNormAt_mulVecLin]
    refine nrm_le_sqrt _ _ (hX _ v) _ _ (hnn j v) fun y => ?_
    rw [← hΦ, ← hΦ, hint]
    exact (sharp_norm (AA j.castSucc) (AA j.succ) (Cl j.castSucc) (Cl j.succ) (W j.castSucc v)
      (W j.succ v) (γ j.castSucc) (γ j.succ) (ε j v) (T j v) (hcl j.castSucc) (hcl j.succ) (tmax j v)
      (hγ _) (hγ _) (hε j v) (hT j v) (ht0 j v) (hh _) (hh _)).1 _
  have hk2 : ∀ j v, kU j v ^ 2 = cbSq (Fintype.card (AA j.castSucc)) (Fintype.card (AA j.succ))
      (hcl j.castSucc) (hcl j.succ) (tmax j v) := fun j v => by
    rw [hkU, Real.sq_sqrt (hnn j v)]
  refine ⟨hop, hk2, fun hne => ?_⟩
  have key := (Formalism.DivisionValues.composition_norm_at_place K m c Xc hX Kj).1
  have hpos : ∀ v, 0 < Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
      (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m)) v
        (Matrix.mulVecLin (chainMat Kj (Fin.last m))) := fun v =>
    Formalism.HN.PlaceOperatorNorms.opNormAt_pos _ _ _ _ (hX _) (hX _) v _ (mulVecLin_ne_zero _ hne)
  have hjpos : ∀ j v, 0 < Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) := by
    intro j v
    have hprod := (hpos v).trans_le (key v)
    exact lt_of_le_of_ne (opNormAt_nonneg _ _ _ _ _ _)
      (Finset.prod_ne_zero_iff.1 hprod.ne' j (Finset.mem_univ j)).symm
  have hfac : ∀ j v, 0 < (Fintype.card (AA j.castSucc) : ℝ) ∧ 0 < (Fintype.card (AA j.succ) : ℝ) ∧
      0 < hcl j.castSucc ∧ 0 < hcl j.succ ∧ 0 < tmax j v := by
    intro j v
    have h0 : 0 < cbSq (Fintype.card (AA j.castSucc)) (Fintype.card (AA j.succ))
        (hcl j.castSucc) (hcl j.succ) (tmax j v) := by
      rw [← hk2]; exact pow_pos ((hjpos j v).trans_le (hop j v)) 2
    rw [cbSq] at h0
    obtain ⟨h1, h2⟩ := pos_pair h0 (ht0 j v)
    rw [mul_comm] at h1
    obtain ⟨h3, h4⟩ := pos_pair h1 (by positivity)
    obtain ⟨h5, h6⟩ := pos_pair h4 (Nat.cast_nonneg _)
    obtain ⟨a⟩ := Fintype.card_pos_iff.1 (Nat.cast_pos.1 h6)
    obtain ⟨h7, h8⟩ := pos_pair h3 ((Nat.cast_nonneg _).trans (hh j.succ a))
    exact ⟨h5, h6, h7, h8, h2⟩
  refine ⟨hfac, fun j v => ?_, fun v => ?_, fun v => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hfac j v
    rw [hk2, cbSq, Real.log_mul (by positivity) h5.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_mul h1.ne' h2.ne', Real.log_mul h3.ne' h4.ne']
    ring
  · rw [← Real.log_prod (fun j _ => pow_ne_zero 2 (hjpos j v).ne'), Finset.prod_pow]
    exact Real.log_le_log (pow_pos (hpos v) 2) (pow_le_pow_left₀ (hpos v).le (key v) 2)
  · exact Finset.sum_le_sum fun j _ =>
      Real.log_le_log (pow_pos (hjpos j v) 2) (pow_le_pow_left₀ (hjpos j v).le (hop j v) 2)
  · rw [Formalism.HN.htMap]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => ?_) (by positivity)
    refine le_trans ?_ (Finset.sum_le_sum fun j _ =>
      Real.log_le_log (pow_pos (hjpos j v) 2) (pow_le_pow_left₀ (hjpos j v).le (hop j v) 2))
    rw [← Real.log_prod (fun j _ => pow_ne_zero 2 (hjpos j v).ne'), Finset.prod_pow]
    exact Real.log_le_log (pow_pos (hpos v) 2) (pow_le_pow_left₀ (hpos v).le (key v) 2)

namespace CB

theorem extra_le (a b f m N L La logg C8 : ℝ) (ha : a ≤ f * N ^ 2 * logg) (hb : b ≤ f * N ^ 2 * logg)
    (hf : 0 ≤ f) (hm : 1 ≤ m) (hL : 0 ≤ L) (hLLa : L ≤ La) (hg : logg ≤ C8 * L) (p8 : 0 ≤ C8) :
    a + b ≤ 2 * C8 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L) := by
  have hN : 0 ≤ f * N ^ 2 := mul_nonneg hf (sq_nonneg N)
  have h1 : f * N ^ 2 * logg ≤ f * N ^ 2 * (C8 * La) :=
    mul_le_mul_of_nonneg_left (le_trans hg (mul_le_mul_of_nonneg_left hLLa p8)) hN
  have hm3 : 0 ≤ m ^ 3 := pow_nonneg (le_trans zero_le_one hm) 3
  have h2 : 0 ≤ C8 * (f * m ^ 3 * N ^ 2 * L) :=
    mul_nonneg p8 (mul_nonneg (mul_nonneg (mul_nonneg hf hm3) (sq_nonneg N)) hL)
  nlinarith [h1, h2, ha, hb]

end CB

private theorem perEmbCore_lemma : PerEmbeddingCB := by
  intro J Pl Emb _ _ _ _ r ν g0 logK MainNotions logOmτ logth0 logh logh' logn logn' logOm v f m N L La logT
    logg C2 C3 C4 c5 c6 C7 C8 C0 hK hn hn' hOm hSK hth hh hh' hPl hg0 hm hN hL hLLa hLa hc5 hc6 hT hg
    p2 p3 p4 p5 p6 p7 p8 hC0
  have hEpos : (0 : ℝ) < (Fintype.card Emb : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hE : (Fintype.card Emb : ℝ) ≠ 0 := hEpos.ne'
  have hf : 0 ≤ f := le_trans (Nat.cast_nonneg _) hPl
  have hF2 : 0 ≤ f * N ^ 2 := mul_nonneg hf (sq_nonneg N)
  have hm0 : 0 ≤ m := le_trans zero_le_one hm
  have hm2 : 1 ≤ m ^ 2 := by nlinarith
  have hm3 : 1 ≤ m ^ 3 := by nlinarith
  have hm23 : m ^ 2 ≤ m ^ 3 := by nlinarith [mul_nonneg (sq_nonneg m) (sub_nonneg.mpr hm)]
  have hm13 : m ≤ m ^ 3 := by nlinarith [mul_nonneg hm0 (sub_nonneg.mpr hm2)]
  have hmL1 : L ≤ m ^ 3 * L := by nlinarith [mul_nonneg (sub_nonneg.mpr hm3) hL]
  have hmL2 : m * L ≤ m ^ 3 * L := by nlinarith [mul_nonneg (sub_nonneg.mpr hm13) hL]
  have hLa0 : 0 ≤ La := le_trans zero_le_one hLa
  have hN2 : 1 ≤ N ^ 2 := by nlinarith
  have hNL : 1 ≤ N ^ 2 * La := by nlinarith
  have hX : 0 ≤ f * N ^ 2 * La := mul_nonneg hF2 hLa0
  have hY : 0 ≤ f * m ^ 3 * N ^ 2 * L :=
    mul_nonneg (mul_nonneg (mul_nonneg hf (pow_nonneg hm0 3)) (sq_nonneg N)) hL
  have v1 : C7 * (m * L) ≤ C7 * (m ^ 3 * L) := mul_le_mul_of_nonneg_left hmL2 p7
  have v2 : C8 * L ≤ C8 * (m ^ 3 * L) := mul_le_mul_of_nonneg_left hmL1 p8
  have q1 : 0 ≤ C2 * (C7 + C8) := mul_nonneg p2 (add_nonneg p7 p8)
  have q2 : 0 ≤ C4 * (1 + C7 + C8) := mul_nonneg p4 (add_nonneg (add_nonneg zero_le_one p7) p8)
  have k1 : (C3 + c5 + 2 * c6 + 1) * (f * N ^ 2 * La) ≤ C0 * (f * N ^ 2 * La) :=
    mul_le_mul_of_nonneg_right (by linarith) hX
  have k2 : (2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8) + 2 * C8) * (f * m ^ 3 * N ^ 2 * L) ≤
      C0 * (f * m ^ 3 * N ^ 2 * L) :=
    mul_le_mul_of_nonneg_right (by linarith) hY
  have main : ∀ j, (∑ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + (logn j + logn' j))) ≤
      (Fintype.card Emb : ℝ) * sizeB ν logOm f m N L La C0 j := by
    intro j
    have hc1 : 0 ≤ (Fintype.card Pl : ℝ) * g0 j := mul_nonneg (Nat.cast_nonneg _) (hg0 j).1
    have hc1' : (Fintype.card Pl : ℝ) * g0 j ≤ f * N ^ 2 := mul_le_mul hPl (hg0 j).2 (hg0 j).1 hf
    have hterm : ∀ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + (logn j + logn' j)) ≤
        (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) + (Fintype.card Pl : ℝ) * g0 j * logth0 s + ((Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
            2 * (C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) +
            (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) + (logh j + logh' j) +
            (logn j + logn' j)) := by
      intro s
      have := hSK j s
      unfold liftedMapLogSize
      linarith
    have hsum : (∑ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + (logn j + logn' j))) ≤
        (∑ s, (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s))) + (Fintype.card Pl : ℝ) * g0 j * (∑ s, logth0 s) +
          (Fintype.card Emb : ℝ) * ((Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
            2 * (C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) +
            (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) + (logh j + logh' j) +
            (logn j + logn' j)) := by
      refine le_trans (Finset.sum_le_sum (fun s _ => hterm s)) (le_of_eq ?_)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    have hA : (∑ s, (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s))) =
        (Fintype.card Emb : ℝ) * ∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOm) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, (div_eq_iff hE).mp (hOm τ), Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring
    have hth' : (∑ s, logth0 s) ≤ C3 * L * (Fintype.card Emb : ℝ) := (div_le_iff₀ hEpos).mp hth
    have hth'' : (Fintype.card Pl : ℝ) * g0 j * (∑ s, logth0 s) ≤
        (Fintype.card Pl : ℝ) * g0 j * (C3 * L * (Fintype.card Emb : ℝ)) :=
      mul_le_mul_of_nonneg_left hth' hc1
    have t1 : (Fintype.card Pl : ℝ) * g0 j * (C3 * L) ≤ f * N ^ 2 * (C3 * La) :=
      mul_le_mul hc1' (mul_le_mul_of_nonneg_left hLLa p3) (mul_nonneg p3 hL) hF2
    have t2a : (Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) ≤
        (Fintype.card Pl : ℝ) * g0 j * (c5 * La) := mul_le_mul_of_nonneg_left (hc5 j) hc1
    have t2b : (Fintype.card Pl : ℝ) * g0 j * (c5 * La) ≤ f * N ^ 2 * (c5 * La) :=
      mul_le_mul_of_nonneg_right hc1' (mul_nonneg p5 hLa0)
    have hq : 0 ≤ 1 + 2 * (N ^ 2 * (c6 * La)) := by
      have := mul_nonneg (sq_nonneg N) (mul_nonneg p6 hLa0)
      linarith
    have t3 : (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) ≤
        f * (1 + 2 * (N ^ 2 * (c6 * La))) := by
      calc (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2)))
          ≤ ∑ _τ : Pl, (1 + 2 * (N ^ 2 * (c6 * La))) := Finset.sum_le_sum (fun τ _ => by
            have h1 : g0 j * Real.log (2 * (∑ i, ν j τ i) + 2) ≤ g0 j * (c6 * La) :=
              mul_le_mul_of_nonneg_left (hc6 j τ) (hg0 j).1
            have h2 : g0 j * (c6 * La) ≤ N ^ 2 * (c6 * La) :=
              mul_le_mul_of_nonneg_right (hg0 j).2 (mul_nonneg p6 hLa0)
            linarith)
        _ = (Fintype.card Pl : ℝ) * (1 + 2 * (N ^ 2 * (c6 * La))) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ f * (1 + 2 * (N ^ 2 * (c6 * La))) := mul_le_mul_of_nonneg_right hPl hq
    have t4 : f * 1 ≤ f * (N ^ 2 * La) := mul_le_mul_of_nonneg_left hNL hf
    have t5 : C2 * f * m ^ 2 * N ^ 2 * (logg + logT) ≤ C2 * f * m ^ 2 * N ^ 2 * (C8 * L + C7 * m * L) :=
      mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (mul_nonneg (mul_nonneg p2 hf) (sq_nonneg m)) (sq_nonneg N))
    have t5b : C2 * f * N ^ 2 * (C8 * L) * m ^ 2 ≤ C2 * f * N ^ 2 * (C8 * L) * m ^ 3 :=
      mul_le_mul_of_nonneg_left hm23
        (mul_nonneg (mul_nonneg (mul_nonneg p2 hf) (sq_nonneg N)) (mul_nonneg p8 hL))
    have u : L + logT + logg ≤ m ^ 3 * L + C7 * (m ^ 3 * L) + C8 * (m ^ 3 * L) := by linarith
    have t6 : C4 * f * N ^ 2 * (L + logT + logg) ≤
        C4 * f * N ^ 2 * (m ^ 3 * L + C7 * (m ^ 3 * L) + C8 * (m ^ 3 * L)) :=
      mul_le_mul_of_nonneg_left u (mul_nonneg (mul_nonneg p4 hf) (sq_nonneg N))
    have t7 : f * N ^ 2 * logg ≤ f * N ^ 2 * (C8 * (m ^ 3 * L)) :=
      mul_le_mul_of_nonneg_left (le_trans hg v2) hF2
    have hZ : (Fintype.card Pl : ℝ) * g0 j * (C3 * L) + ((Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
            2 * (C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) +
            (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) + (logh j + logh' j) +
            (logn j + logn' j)) ≤
        C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L) := by
      linarith [hh j, hh' j, hn j, hn' j]
    have hZE := mul_le_mul_of_nonneg_left hZ hEpos.le
    rw [hA] at hsum
    unfold sizeB
    linarith
  have cnn : ∀ j, 0 ≤ sizeB ν logOm f m N L La C0 j -
      (∑ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + (logn j + logn' j))) / (Fintype.card Emb : ℝ) :=
    fun j => sub_nonneg.mpr ((div_le_iff₀ hEpos).mpr (by linarith [main j]))
  refine ⟨fun j => sizeB ν logOm f m N L La C0 j -
      (∑ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + (logn j + logn' j))) / (Fintype.card Emb : ℝ), cnn, ?_, ?_⟩
  · intro j s
    have := hK j s
    have := cnn j
    linarith
  · intro j
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring

theorem first_descent_coupled_bound : StepDiCB := by
  intro J Pl Emb _ _ _ _ r ν g0 logK MainNotions logOmτ logth0 logh logh' logn logn' hK logOm v f m N L La logT
    logg C2 C3 C4 c5 c6 C7 C8 C0 hK0 hn hn' hKd hOm hSK hth hh hh' hPl hg0 hm hN hL hLLa hLa hc5 hc6
    hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  obtain ⟨cst, -, hc1, hc2⟩ := perEmbCore_lemma J Pl Emb r ν g0 logK MainNotions logOmτ logth0 logh logh'
    logn logn' logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 hK0 hn hn' hOm hSK hth hh hh' hPl
    hg0 hm hN hL hLLa hLa hc5 hc6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  have hEpos : (0 : ℝ) < (Fintype.card Emb : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hB : ∀ j, hK j ≤ sizeB ν logOm f m N L La C0 j := by
    intro j
    rw [hKd j, ← hc2 j]
    gcongr
    exact hc1 j _
  refine ⟨fun j s => ?_, fun j s => ?_, fun j s => ?_, hB,
    fun j => C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L), ?_⟩
  · have := hK0 j s
    unfold liftedMapLogSize at this ⊢
    linarith
  · have := hSK j s
    have := hn j
    have := hn' j
    linarith
  · have := hK0 j s
    unfold liftedMapLogSize at this ⊢
    linarith
  · unfold DiHyp6
    refine ⟨fun j => ?_, fun j => le_refl _⟩
    have := hB j
    unfold sizeB at this
    exact this

theorem per_embedding_coupled_bound : PerEmbeddingCB := perEmbCore_lemma

theorem sharp_three_halves_bound : LiftedMapEmbeddingLogBound := by
  intro J Pl Emb _ r ν n g0 Ksq kc Om th0sq nn nn' hcl hcl' v hν hK0 hkc hOm hth hnn hnn' hcl0 hcl0' hv
    hK j s
  have hterm : ∀ τ, Real.log ((Om τ s)⁻¹ ^ n j τ *
          (Real.exp 1 * (2 * (n j τ : ℝ) + 2) ^ (2 * g0 j) * Real.exp (∑ i, ph (ν j τ i)))) =
      (∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * Real.log (Om τ s) +
        (1 + 2 * (g0 j : ℝ) * Real.log (2 * (∑ i, ν j τ i) + 2)) := by
    intro τ
    have hO := hOm τ s
    have hB : (0 : ℝ) < 2 * (n j τ : ℝ) + 2 := by positivity
    rw [Real.log_mul (pow_ne_zero _ (inv_ne_zero hO.ne')) (by positivity),
      Real.log_mul (by positivity) (Real.exp_ne_zero _),
      Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ hB.ne'), Real.log_pow, Real.log_inv,
      Real.log_exp, Real.log_pow, Real.log_exp, hν j τ]
    push_cast
    ring
  have hPpos : ∀ τ, 0 < ((Om τ s)⁻¹ ^ n j τ *
          (Real.exp 1 * (2 * (n j τ : ℝ) + 2) ^ (2 * g0 j) * Real.exp (∑ i, ph (ν j τ i)))) := fun τ =>
    mul_pos (pow_pos (inv_pos.mpr (hOm τ s)) _) (by positivity)
  have hlogP : Real.log (∏ τ, ((Om τ s)⁻¹ ^ n j τ *
          (Real.exp 1 * (2 * (n j τ : ℝ) + 2) ^ (2 * g0 j) * Real.exp (∑ i, ph (ν j τ i))))) =
      ∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * Real.log (Om τ s) +
        (1 + 2 * (g0 j : ℝ) * Real.log (2 * (∑ i, ν j τ i) + 2))) := by
    rw [Real.log_prod (fun τ _ => (hPpos τ).ne')]
    exact Finset.sum_congr rfl (fun τ _ => hterm τ)
  have h8 : (0 : ℝ) < 8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v := by
    have := mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card Pl * g0 j)) hv.le
    linarith
  have hXpos : 0 < (kc j s ^ 2 * (8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v) ^ (Fintype.card Pl * g0 j) *
          th0sq s ^ (Fintype.card Pl * g0 j)) :=
    mul_pos (mul_pos (pow_pos (hkc j s) 2) (pow_pos h8 _)) (pow_pos (hth s) _)
  have hlogX : Real.log (kc j s ^ 2 * (8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v) ^ (Fintype.card Pl * g0 j) *
          th0sq s ^ (Fintype.card Pl * g0 j)) =
      2 * Real.log (kc j s) +
        (Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
        (Fintype.card Pl : ℝ) * g0 j * Real.log (th0sq s) := by
    rw [Real.log_mul (mul_pos (pow_pos (hkc j s) 2) (pow_pos h8 _)).ne' (pow_pos (hth s) _).ne',
      Real.log_mul (pow_pos (hkc j s) 2).ne' (pow_pos h8 _).ne', Real.log_pow, Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  have hPP : 0 < ∏ τ, ((Om τ s)⁻¹ ^ n j τ *
          (Real.exp 1 * (2 * (n j τ : ℝ) + 2) ^ (2 * g0 j) * Real.exp (∑ i, ph (ν j τ i)))) := Finset.prod_pos (fun τ _ => hPpos τ)
  have hK1 := hK j s
  unfold cbSq at hK1
  have hl := Real.log_le_log (hK0 j s) hK1
  rw [Real.log_mul (mul_pos (mul_pos (hnn j) (hnn' j)) (mul_pos (hcl0 j) (hcl0' j))).ne'
      (mul_pos hXpos hPP).ne',
    Real.log_mul (mul_pos (hnn j) (hnn' j)).ne' (mul_pos (hcl0 j) (hcl0' j)).ne',
    Real.log_mul (hnn j).ne' (hnn' j).ne', Real.log_mul (hcl0 j).ne' (hcl0' j).ne',
    Real.log_mul hXpos.ne' hPP.ne', hlogX, hlogP, Finset.sum_add_distrib] at hl
  simp only [liftedMapLogSize]
  linarith

theorem sharp_entries : SharpEntries := by
  intro AA AA' _ Cl Cl' _ A B _ _ _ _ γ ε T G
  refine ⟨fun b L' => ?_, Fintype.sum_sigma (fun p => γ p * ‖G p‖ ^ 2)⟩
  show (∑ p, ((γ p : ℂ) * ε p ⟨b, L'⟩) • T p ⟨b, L'⟩ (G p)) =
    (∑ a, entryHom γ ε T a b (fun L => G ⟨a, L⟩)) L'
  rw [Finset.sum_apply, Fintype.sum_sigma]
  rfl

theorem coupled_product : CoupledProduct := by
  intro AA Rep Y Cl2 _ Cl _ _ _ A B C _ _ _ _ _ _ γ0 γ1 ε1 T1 ε2 T2 G g'
  simp only [liftOp, coupledOp, map_sum, map_smul, Finset.smul_sum, smul_smul, Fintype.sum_sigma,
    mul_assoc]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]

theorem coupled_norm : CoupledNorm := by
  intro AA Rep Y Cl2 Cl _ _ _ _ A B C _ _ _ _ _ _ γ0 γ1 γ2 ε1 T1 ε2 T2 t1 t2 a φ hγ0 hγ1 hγ2 hε1 hε2
    hT1 hT2 ht1 ht2
  have hs0 : 0 ≤ ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖ :=
    Finset.sum_nonneg (fun L _ => mul_nonneg (hγ0 _).1.le (norm_nonneg _))
  have hS0 : 0 ≤ ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖ ^ 2 :=
    Finset.sum_nonneg (fun L _ => mul_nonneg (hγ0 _).1.le (sq_nonneg _))
  have hin : ∀ (y : Y) (x : Rep), ‖liftOp (fun L => γ0 ⟨a, L⟩) (fun L x' => ε1 ⟨a, L⟩ ⟨y, x'⟩)
      (fun L x' => T1 ⟨a, L⟩ ⟨y, x'⟩) φ x‖ ≤ Real.sqrt t1 * ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖ := by
    intro y x
    simp only [liftOp]
    rw [Finset.mul_sum]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun L _ => ?_))
    rw [norm_smul, norm_mul, hε1, mul_one, Complex.norm_real, Real.norm_of_nonneg (hγ0 _).1.le]
    calc γ0 ⟨a, L⟩ * ‖T1 ⟨a, L⟩ ⟨y, x⟩ (φ L)‖ ≤ γ0 ⟨a, L⟩ * (Real.sqrt t1 * ‖φ L‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (hγ0 _).1.le
          refine le_trans (ContinuousLinearMap.le_opNorm _ _)
            (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
          exact le_of_eq_of_le (abs_of_nonneg (norm_nonneg _)).symm (Real.abs_le_sqrt (hT1 _ _))
      _ = Real.sqrt t1 * (γ0 ⟨a, L⟩ * ‖φ L‖) := by ring
  have hco : ∀ g', ‖coupledOp γ0 γ1 ε1 T1 ε2 T2 a φ g'‖ ≤
      (Fintype.card Rep : ℝ) * ((Fintype.card Y : ℝ) *
        (Real.sqrt t2 * (Real.sqrt t1 * ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖))) := by
    intro g'
    simp only [coupledOp]
    calc _ ≤ ∑ _x : Rep, ∑ _y : Y, Real.sqrt t2 * (Real.sqrt t1 * ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖) := by
          refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun x _ => ?_))
          rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (hγ1 x).1.le]
          refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (hγ1 x).2) ?_
          refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun y _ => ?_))
          rw [norm_smul, hε2, one_mul]
          refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
          exact mul_le_mul
            (le_of_eq_of_le (abs_of_nonneg (norm_nonneg _)).symm (Real.abs_le_sqrt (hT2 _ _)))
            (hin y x) (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsγ : ∑ L, γ0 ⟨a, L⟩ ≤ (Fintype.card (Cl a) : ℝ) := by
    calc ∑ L, γ0 ⟨a, L⟩ ≤ ∑ _L : Cl a, (1 : ℝ) := Finset.sum_le_sum (fun L _ => (hγ0 _).2)
      _ = _ := by simp
  have hcs : (∑ L, γ0 ⟨a, L⟩ * ‖φ L‖) ^ 2 ≤
      (Fintype.card (Cl a) : ℝ) * ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖ ^ 2 :=
    le_trans (Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul _ (fun L _ => (hγ0 _).1.le)
        (fun L _ => mul_nonneg (hγ0 _).1.le (sq_nonneg _)) (fun L _ => by ring))
      (mul_le_mul_of_nonneg_right hsγ hS0)
  have key : ∀ g', ‖coupledOp γ0 γ1 ε1 T1 ε2 T2 a φ g'‖ ^ 2 ≤
      (Fintype.card Rep : ℝ) ^ 2 * (Fintype.card Y : ℝ) ^ 2 * t2 * t1 *
        ((Fintype.card (Cl a) : ℝ) * ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖ ^ 2) := by
    intro g'
    have h1 := hco g'
    calc ‖coupledOp γ0 γ1 ε1 T1 ε2 T2 a φ g'‖ ^ 2
        ≤ ((Fintype.card Rep : ℝ) * ((Fintype.card Y : ℝ) *
            (Real.sqrt t2 * (Real.sqrt t1 * ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖)))) ^ 2 :=
          sq_le_sq' (by linarith [norm_nonneg (coupledOp γ0 γ1 ε1 T1 ε2 T2 a φ g')]) h1
      _ = (Fintype.card Rep : ℝ) ^ 2 * (Fintype.card Y : ℝ) ^ 2 * t2 * t1 *
            (∑ L, γ0 ⟨a, L⟩ * ‖φ L‖) ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt ht2, Real.sq_sqrt ht1]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcs
          (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) ht2) ht1)
  calc (∑ g', γ2 g' * ‖coupledOp γ0 γ1 ε1 T1 ε2 T2 a φ g'‖ ^ 2)
      ≤ ∑ _g' : Cl2, (Fintype.card Rep : ℝ) ^ 2 * (Fintype.card Y : ℝ) ^ 2 * t2 * t1 *
        ((Fintype.card (Cl a) : ℝ) * ∑ L, γ0 ⟨a, L⟩ * ‖φ L‖ ^ 2) :=
        Finset.sum_le_sum (fun g' _ =>
          le_trans (mul_le_of_le_one_left (sq_nonneg _) (hγ2 g').2) (key g'))
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

theorem sharp_cost : SharpCost := by
  intro n n' g f N hn hn' hg hf hN h1 h2
  have hg0 : 0 < g := lt_of_lt_of_le one_pos hg
  have hlg : 0 ≤ Real.log g := Real.log_nonneg hg
  have hNN : f * N * Real.log g ≤ f * N ^ 2 * Real.log g := by
    have : N ≤ N ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hf) hlg
  have one : ∀ k : ℕ, 1 ≤ k → ((k : ℝ) ≤ g ^ (f * N ^ 2) ∨ (k : ℝ) ≤ g ^ (f * N)) →
      Real.log k ≤ f * N ^ 2 * Real.log g := by
    intro k hk hk'
    have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
    rcases hk' with hk' | hk'
    · calc Real.log k ≤ Real.log (g ^ (f * N ^ 2)) := Real.log_le_log hk0 hk'
        _ = f * N ^ 2 * Real.log g := Real.log_rpow hg0 _
    · calc Real.log k ≤ Real.log (g ^ (f * N)) := Real.log_le_log hk0 hk'
        _ = f * N * Real.log g := Real.log_rpow hg0 _
        _ ≤ f * N ^ 2 * Real.log g := hNN
  have a1 := one n hn h1
  have a2 := one n' hn' h2
  refine ⟨a1, a2, ?_⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn0' : (0 : ℝ) < n' := Nat.cast_pos.mpr (by omega)
  rw [Real.log_mul hn0.ne' hn0'.ne']
  linarith

theorem lift_first_descent_coupled : LiftStepDiCB := by
  intro J Pl Emb _ _ _ _ ι AA AA' Cl Cl' _ _ _ _ _ _ _ _ _ A B _ _ _ _ _ r ν n s Th c Rc lam Om S kc th0sq
    γ γ' ε hK hcl hcl' logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 hν0 hν hs0 hs hTh hHas hThb
    hsupp hRc hOm hlam hγ hγ' hε hS hLpos hkc hth0 hv hKd hOmd hkcb hthb hCl hCl' hhcl hhcl' hAA hAA'
    hT0 hPl hι hm hN hL hLLa hLa hc5 hc6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0 j
  have hLS := fun j σ => lift_sharp_bound Pl (ι j) (AA j) (AA' j) (Cl j) (Cl' j) (A j σ) (B j σ) r
    (ν j) (n j) (s j σ) (Th j σ) (c j σ) (Rc j σ) (fun τ => lam τ σ) (fun τ => Om τ σ) (S j σ) (γ j)
    (γ' j) (ε j σ) (hcl j) (hcl' j) (hν0 j) (hν j) (hs0 j σ) (hs j σ) (hTh j σ) (hHas j σ) (hThb j σ)
    (hsupp j σ) (hRc j σ) (fun τ => hOm τ σ) (fun τ => hlam τ σ) (hγ j) (hγ' j) (hε j σ) (hCl j)
    (hCl' j)
  have hnn : ∀ j, (0 : ℝ) < (Fintype.card (AA j) : ℝ) := fun j => Nat.cast_pos.mpr Fintype.card_pos
  have hnn' : ∀ j, (0 : ℝ) < (Fintype.card (AA' j) : ℝ) := fun j => Nat.cast_pos.mpr Fintype.card_pos
  have hclp : ∀ j, 0 < hcl j := fun j =>
    lt_of_lt_of_le (Nat.cast_pos.mpr Fintype.card_pos) (hCl j (Classical.arbitrary (AA j)))
  have hclp' : ∀ j, 0 < hcl' j := fun j =>
    lt_of_lt_of_le (Nat.cast_pos.mpr Fintype.card_pos) (hCl' j (Classical.arbitrary (AA' j)))
  have h32 := sharp_three_halves_bound J Pl Emb r ν n (fun j => Fintype.card (ι j))
    (fun j σ => liftNormSq (γ j) (γ' j) (ε j σ) (fun L L' => liftBlock (c j σ L L') (Rc j σ) (fun τ => lam τ σ))) kc Om th0sq
    (fun j => (Fintype.card (AA j) : ℝ)) (fun j => (Fintype.card (AA' j) : ℝ)) hcl hcl' v hν hLpos hkc hOm
    hth0 hnn hnn' hclp hclp' hv (fun j σ => by
      have := hLS j σ
      rw [hS j σ] at this
      exact this)
  have hg0' : ∀ j, 0 ≤ (Fintype.card (ι j) : ℝ) ∧ (Fintype.card (ι j) : ℝ) ≤ N ^ 2 :=
    fun j => ⟨Nat.cast_nonneg _, hι j⟩
  have hc5' : ∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * (Fintype.card (ι j) : ℝ)) * v) ≤ c5 * La :=
    fun j => by
      have := hc5 j
      push_cast at this
      exact this
  have hc6' : ∀ j τ, Real.log (2 * (∑ i, ν j τ i) + 2) ≤ c6 * La := fun j τ => by
    rw [hν j τ]
    exact hc6 j τ
  have hC0' : C3 + c5 + 2 * c6 + 1 + 2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8) + 2 * C8 ≤ C0 := by
    nlinarith
  have hstep := first_descent_coupled_bound J Pl Emb r ν (fun j => (Fintype.card (ι j) : ℝ))
    (fun j σ => Real.log (liftNormSq (γ j) (γ' j) (ε j σ) (fun L L' => liftBlock (c j σ L L') (Rc j σ) (fun τ => lam τ σ)))) (fun j σ => Real.log (kc j σ)) (fun τ σ => Real.log (Om τ σ))
    (fun σ => Real.log (th0sq σ)) (fun j => Real.log (hcl j)) (fun j => Real.log (hcl' j))
    (fun j => Real.log (Fintype.card (AA j) : ℝ)) (fun j => Real.log (Fintype.card (AA' j) : ℝ)) hK logOm v
    f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 h32 hAA hAA' hKd hOmd hkcb hthb hhcl hhcl' hPl hg0' hm hN
    hL hLLa hLa hc5' hc6' hT hg p2 p3 p4 p5 p6 p7 p8 hC0'
  exact hstep.2.2.2.1 j

namespace CB

theorem chainFun_succ {m : ℕ} {C : Fin (m + 2) → Type} (Kj : ∀ j : Fin (m + 1), C j.castSucc → C j.succ)
    (φ : C 0) (i : Fin (m + 1)) :
    chainFun Kj i.succ φ = chainFun (C := fun i => C i.succ) (fun j : Fin m => Kj j.succ) i (Kj 0 φ) := by
  induction i using Fin.induction with
  | zero => rfl
  | succ j ih => exact congrArg (Kj j.succ) ih

theorem chainFun_sum {m : ℕ} {C : Fin (m + 1) → Type} [∀ i, AddCommMonoid (C i)]
    (Kj : ∀ j : Fin m, C j.castSucc →+ C j.succ) {X : Type} (s : Finset X) (x : X → C 0) (i : Fin (m + 1)) :
    chainFun (fun j => ⇑(Kj j)) i (∑ a ∈ s, x a) = ∑ a ∈ s, chainFun (fun j => ⇑(Kj j)) i (x a) := by
  induction i using Fin.induction with
  | zero => rfl
  | succ j ih =>
    show Kj j (chainFun (fun j => ⇑(Kj j)) j.castSucc (∑ a ∈ s, x a)) =
      ∑ a ∈ s, Kj j (chainFun (fun j => ⇑(Kj j)) j.castSucc (x a))
    rw [ih, map_sum]

theorem single_sum {I X : Type} [DecidableEq I] {H : I → Type} [∀ i, AddCommMonoid (H i)] (i : I)
    (s : Finset X) (x : X → H i) :
    (Pi.single i (∑ a ∈ s, x a) : ∀ i, H i) = ∑ a ∈ s, Pi.single i (x a) :=
  map_sum (AddMonoidHom.single H i) x s

end CB

theorem path_sum_alt : PathSum := by
  intro m
  induction m with
  | zero =>
    intro AA _ _ H _ E G
    have key : ∀ F : (∀ i : Fin 1, AA i) → (∀ a, H 0 a),
        (∀ al, F al = Pi.single (al 0) (G (al 0))) → ∑ al, F al = G := by
      intro F hF
      rw [Fintype.sum_equiv (Equiv.piUnique (α := Fin 1) AA) F (fun a => Pi.single a (G a)) hF]
      exact Finset.univ_sum_single G
    exact Eq.symm (key _ (fun al => rfl))
  | succ m ih =>
    intro AA _ _ H _ E G
    have h1 := chainFun_succ (C := fun i => ∀ a, H i a) (fun j => blockMap (E j)) G (Fin.last m)
    have h2 := ih (fun i => AA i.succ) (fun i => H i.succ) (fun j => E j.succ) (blockMap (E 0) G)
    refine h1.trans (h2.trans ?_)
    have hL : ∀ al' : (∀ i : Fin (m + 1), AA i.succ),
        Pi.single (M := fun b => H (Fin.last m).succ b) (al' (Fin.last m))
          (chainFun (C := fun i => H i.succ (al' i))
          (fun j => E j.succ (al' j.castSucc) (al' j.succ)) (Fin.last m) (blockMap (E 0) G (al' 0))) =
        ∑ a : AA 0, Pi.single (M := fun b => H (Fin.last m).succ b) (al' (Fin.last m))
          (chainFun (C := fun i => H i.succ (al' i))
          (fun j => E j.succ (al' j.castSucc) (al' j.succ)) (Fin.last m) (E 0 a (al' 0) (G a))) := by
      intro al'
      rw [← single_sum (H := fun b => H (Fin.last m).succ b)]
      exact congrArg (Pi.single (M := fun b => H (Fin.last m).succ b) (al' (Fin.last m)))
        (chainFun_sum (C := fun i => H i.succ (al' i))
          (fun j => E j.succ (al' j.castSucc) (al' j.succ)) Finset.univ
          (fun a => E 0 a (al' 0) (G a)) (Fin.last m))
    have hR : ∀ (a : AA 0) (al' : ∀ i : Fin (m + 1), AA i.succ),
        Pi.single (M := fun b => H (Fin.last m).succ b) (al' (Fin.last m))
          (chainFun (C := fun i => H i.succ (al' i))
          (fun j => E j.succ (al' j.castSucc) (al' j.succ)) (Fin.last m) (E 0 a (al' 0) (G a))) =
        (fun al : (∀ i, AA i) => Pi.single (al (Fin.last (m + 1))) (chainFun (C := fun i => H i (al i))
          (fun j => E j (al j.castSucc) (al j.succ)) (Fin.last (m + 1)) (G (al 0)))) (Fin.cons a al') := by
      intro a al'
      exact congrArg (Pi.single (M := fun b => H (Fin.last m).succ b) (al' (Fin.last m)))
        (chainFun_succ (C := fun i => H i ((Fin.cons a al' : ∀ i, AA i) i))
          (fun j => E j ((Fin.cons a al' : ∀ i, AA i) j.castSucc) ((Fin.cons a al' : ∀ i, AA i) j.succ))
          (G a) (Fin.last m)).symm
    rw [Finset.sum_congr rfl (fun al' _ => hL al'), Finset.sum_comm]
    rw [← Fintype.sum_equiv (Fin.consEquiv AA) (fun p => (fun al : (∀ i, AA i) => Pi.single (al (Fin.last (m + 1))) (chainFun (C := fun i => H i (al i))
          (fun j => E j (al j.castSucc) (al j.succ)) (Fin.last (m + 1)) (G (al 0)))) (Fin.cons p.1 p.2)) (fun al : (∀ i, AA i) => Pi.single (al (Fin.last (m + 1))) (chainFun (C := fun i => H i (al i))
          (fun j => E j (al j.castSucc) (al j.succ)) (Fin.last (m + 1)) (G (al 0))))
      (fun p => rfl), ← Finset.univ_product_univ, Finset.sum_product]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun al' _ => hR a al'))

theorem column_paths : ColPaths := by
  intro m AA _ _ Cl _ W _ _ γ ε T G
  have hA : ∀ i : Fin (m + 1), (fun (a : AA i) (L : Cl i a) =>
      chainFun (C := fun i => (Σ a, Cl i a) → W i) (fun j => liftOp (γ j.castSucc) (ε j) (T j)) i G ⟨a, L⟩) =
      chainFun (C := fun i => ∀ a, Cl i a → W i)
        (fun j => blockMap (entryHom (γ j.castSucc) (ε j) (T j))) i (fun a L => G ⟨a, L⟩) := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ j ih =>
      funext b L'
      change liftOp (γ j.castSucc) (ε j) (T j) (chainFun (C := fun i => (Σ a, Cl i a) → W i)
        (fun j => liftOp (γ j.castSucc) (ε j) (T j)) j.castSucc G) ⟨b, L'⟩ =
        blockMap (entryHom (γ j.castSucc) (ε j) (T j)) (chainFun (C := fun i => ∀ a, Cl i a → W i)
        (fun j => blockMap (entryHom (γ j.castSucc) (ε j) (T j))) j.castSucc (fun a L => G ⟨a, L⟩)) b L'
      rw [← ih]
      exact (sharp_entries _ _ _ _ _ _ _ _ _ _).1 b L'
  rw [hA]
  exact path_sum_alt m AA (fun i a => Cl i a → W i)
    (fun j a b => entryHom (γ j.castSucc) (ε j) (T j) a b) (fun a L => G ⟨a, L⟩)

theorem coupled_bound_lemma : LemmaCB :=
  ⟨sharp_entries, coupled_product, path_sum_alt, column_paths, sharp_norm,
    coupled_norm, sharp_cost⟩

theorem cbHyp_matrix (K : Type) [Field K] [NumberField K] (m : ℕ) (c : Fin (m + 1) → ℕ)
    (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
    (tmax : Fin m → InfinitePlace K → ℝ) (h0 : ∀ j v, 0 ≤ tmax j v)
    (ht : ∀ j v q p, ‖v.embedding (Kj j q p)‖ ^ 2 ≤ tmax j v) :
    CBHyp (fun i _ => (1 : Matrix (Fin (c i)) (Fin (c i)) ℂ)) Kj (AA := fun i => Fin (c i))
      (fun _ _ => Unit) (fun _ _ => ℂ) (fun _ _ => 1) (fun _ _ x p => x p.1) (fun _ _ _ _ => 1)
      (fun j v p q => (v.embedding (Kj j q.1 p.1)) • ContinuousLinearMap.id ℂ ℂ) (fun _ => 1) tmax := by
  unfold CBHyp
  refine ⟨fun i v => by simp, fun i p => ⟨one_pos, le_rfl⟩, ?_, ?_, fun _ _ _ _ => norm_one, ?_, h0,
    fun _ _ => by simp⟩
  · intro i v x
    simp only [Formalism.DivisionValues.fnorm, Formalism.HermitianLatticesTheory.cnorm]
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), Fintype.sum_sigma]
    simp
  · intro j v x
    funext q
    simp [liftOp, Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  · intro j v p q
    rw [norm_smul, ContinuousLinearMap.norm_id, mul_one]
    exact ht j v q.1 p.1

theorem cb_nonvacuous :
    CBHyp (K := ℚ) (m := 2) (c := fun _ => 2) (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) (fun _ => 1)
      (AA := fun _ => Fin 2) (fun _ _ => Unit) (fun _ _ => ℂ) (fun _ _ => 1) (fun _ _ x p => x p.1)
      (fun _ _ _ _ => 1)
      (fun _ v p q => (v.embedding ((1 : Matrix (Fin 2) (Fin 2) ℚ) q.1 p.1)) • ContinuousLinearMap.id ℂ ℂ)
      (fun _ => 1) (fun _ _ => 1) ∧
    chainMat (R := ℚ) (m := 2) (c := fun _ => 2) (fun _ => 1) (Fin.last 2) ≠ 0 := by
  refine ⟨cbHyp_matrix ℚ 2 (fun _ => 2) (fun _ => 1) (fun _ _ => 1) (fun _ _ => zero_le_one) ?_, ?_⟩
  · intro j v q p
    by_cases h : q = p <;> simp [Matrix.one_apply, h]
  · show (1 : Matrix (Fin 2) (Fin 2) ℚ) * ((1 : Matrix (Fin 2) (Fin 2) ℚ) * 1) ≠ 0
    simp

end Formalism.DimensionVariation
