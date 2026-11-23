import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps
import Formalism.DoubleCosetMeasures.LatticeCoset
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CharacterOrthogonalityDual
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelQuotientFinite
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelPropertiesOfHypotheses
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AddedBlockKernelSupport

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.A5x8

section GlobalTheory
variable {K : Type} [CommRing K] {m N : ℕ}

def eN (hN : N = m + 1) : Fin m ⊕ Unit ≃ Fin N :=
  ((Equiv.sumCongr (Equiv.refl (Fin m)) finOneEquiv.symm).trans finSumFinEquiv).trans
    (finCongr hN.symm)

theorem eN_inl (hN : N = m + 1) (a : Fin m) : ((eN hN (Sum.inl a) : Fin N) : ℕ) = a := by
  simp [eN]

theorem eN_inr (hN : N = m + 1) (u : Unit) : ((eN hN (Sum.inr u) : Fin N) : ℕ) = m := by
  simp [eN]

def blkM (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K) (b a : Fin m → K) (d : K) :
    Matrix (Fin N) (Fin N) K :=
  (fromBlocks A (replicateCol Unit b) (replicateRow Unit a) (Matrix.of fun _ _ => d)).submatrix
    (eN hN).symm (eN hN).symm

theorem blkM_ll (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K) (b a : Fin m → K) (d : K)
    (i j : Fin m) : blkM hN A b a d (eN hN (Sum.inl i)) (eN hN (Sum.inl j)) = A i j := by
  simp [blkM]

theorem blkM_lr (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K) (b a : Fin m → K) (d : K)
    (i : Fin m) (u : Unit) : blkM hN A b a d (eN hN (Sum.inl i)) (eN hN (Sum.inr u)) = b i := by
  simp [blkM]

theorem blkM_rl (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K) (b a : Fin m → K) (d : K)
    (j : Fin m) (u : Unit) : blkM hN A b a d (eN hN (Sum.inr u)) (eN hN (Sum.inl j)) = a j := by
  simp [blkM]

theorem blkM_rr (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K) (b a : Fin m → K) (d : K)
    (u u' : Unit) : blkM hN A b a d (eN hN (Sum.inr u)) (eN hN (Sum.inr u')) = d := by
  simp [blkM]

theorem eq_blkM (hN : N = m + 1) (M : Matrix (Fin N) (Fin N) K) :
    M = blkM hN (Matrix.of fun i j => M (eN hN (Sum.inl i)) (eN hN (Sum.inl j)))
      (fun i => M (eN hN (Sum.inl i)) (eN hN (Sum.inr ())))
      (fun j => M (eN hN (Sum.inr ())) (eN hN (Sum.inl j)))
      (M (eN hN (Sum.inr ())) (eN hN (Sum.inr ()))) := by
  ext i j
  obtain ⟨x, rfl⟩ := (eN hN).surjective i
  obtain ⟨y, rfl⟩ := (eN hN).surjective j
  rcases x with x | ⟨⟩ <;> rcases y with y | ⟨⟩ <;> simp [blkM_ll, blkM_lr, blkM_rl, blkM_rr]

theorem blkM_inj (hN : N = m + 1) {A A' : Matrix (Fin m) (Fin m) K} {b a b' a' : Fin m → K}
    {d d' : K} (h : blkM hN A b a d = blkM hN A' b' a' d') :
    A = A' ∧ b = b' ∧ a = a' ∧ d = d' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    have := congrFun (congrFun h (eN hN (Sum.inl i))) (eN hN (Sum.inl j))
    simpa [blkM_ll] using this
  · funext i
    have := congrFun (congrFun h (eN hN (Sum.inl i))) (eN hN (Sum.inr ()))
    simpa [blkM_lr] using this
  · funext j
    have := congrFun (congrFun h (eN hN (Sum.inr ()))) (eN hN (Sum.inl j))
    simpa [blkM_rl] using this
  · have := congrFun (congrFun h (eN hN (Sum.inr ()))) (eN hN (Sum.inr ()))
    simpa [blkM_rr] using this

theorem blkM_mul (hN : N = m + 1) (A A' : Matrix (Fin m) (Fin m) K) (b a b' a' : Fin m → K)
    (d d' : K) : blkM hN A b a d * blkM hN A' b' a' d' =
      blkM hN (A * A' + vecMulVec b a') (A *ᵥ b' + d' • b) (a ᵥ* A' + d • a') (a ⬝ᵥ b' + d * d') := by
  unfold blkM
  rw [Matrix.submatrix_mul_equiv, fromBlocks_multiply]
  congr 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.mul_apply, mulVec, vecMul, dotProduct, vecMulVec, mul_comm]

theorem blkM_one (hN : N = m + 1) : blkM hN (1 : Matrix (Fin m) (Fin m) K) 0 0 1 = 1 := by
  ext i j
  obtain ⟨x, rfl⟩ := (eN hN).surjective i
  obtain ⟨y, rfl⟩ := (eN hN).surjective j
  rcases x with x | ⟨⟩ <;> rcases y with y | ⟨⟩ <;> simp [blkM_ll, blkM_lr, blkM_rl, blkM_rr, Matrix.one_apply]

theorem blkM_isInt (R : Subring K) (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K)
    (b a : Fin m → K) (d : K) : IsInt R (blkM hN A b a d) ↔
      IsInt R A ∧ (∀ i, b i ∈ R) ∧ (∀ j, a j ∈ R) ∧ d ∈ R := by
  constructor
  · intro h
    refine ⟨fun i j => by simpa [blkM_ll] using h (eN hN (Sum.inl i)) (eN hN (Sum.inl j)),
      fun i => by simpa [blkM_lr] using h (eN hN (Sum.inl i)) (eN hN (Sum.inr ())),
      fun j => by simpa [blkM_rl] using h (eN hN (Sum.inr ())) (eN hN (Sum.inl j)),
      by simpa [blkM_rr] using h (eN hN (Sum.inr ())) (eN hN (Sum.inr ()))⟩
  · rintro ⟨hA, hb, ha, hd⟩ i j
    obtain ⟨x, rfl⟩ := (eN hN).surjective i
    obtain ⟨y, rfl⟩ := (eN hN).surjective j
    rcases x with x | ⟨⟩ <;> rcases y with y | ⟨⟩ <;> simp [hA _ _, blkM_ll, blkM_lr, blkM_rl, blkM_rr, hb, ha, hd]

theorem eN_lt_iff (hN : N = m + 1) (i j : Fin m) :
    eN hN (Sum.inl i) < eN hN (Sum.inl j) ↔ i < j := by
  rw [Fin.lt_iff_val_lt_val, eN_inl, eN_inl, Fin.lt_iff_val_lt_val]

theorem eN_inl_lt_inr (hN : N = m + 1) (i : Fin m) (u : Unit) :
    eN hN (Sum.inl i) < eN hN (Sum.inr u) := by
  rw [Fin.lt_iff_val_lt_val, eN_inl, eN_inr]
  exact i.isLt

theorem blkM_isLowUni (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K)
    (b a : Fin m → K) (d : K) : IsLowUni (blkM hN A b a d) ↔ IsLowUni A ∧ b = 0 ∧ d = 1 := by
  constructor
  · rintro ⟨hl, hd⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ?_, ?_⟩
    · have hh : blkM hN A b a d (eN hN (Sum.inl i)) (eN hN (Sum.inl j)) = 0 :=
        hl ((eN_lt_iff hN i j).2 hij)
      rwa [blkM_ll] at hh
    · have hh : blkM hN A b a d (eN hN (Sum.inl i)) (eN hN (Sum.inl i)) = 1 := hd _
      rwa [blkM_ll] at hh
    · funext i
      have hh : blkM hN A b a d (eN hN (Sum.inl i)) (eN hN (Sum.inr ())) = 0 :=
        hl (eN_inl_lt_inr hN i ())
      rwa [blkM_lr] at hh
    · have hh : blkM hN A b a d (eN hN (Sum.inr ())) (eN hN (Sum.inr ())) = 1 := hd _
      rwa [blkM_rr] at hh
  · rintro ⟨⟨hl, hd⟩, rfl, rfl⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hij' : i < j := hij
      obtain ⟨x, rfl⟩ := (eN hN).surjective i
      obtain ⟨y, rfl⟩ := (eN hN).surjective j
      rcases x with x | ⟨⟩ <;> rcases y with y | ⟨⟩
      · rw [blkM_ll]
        exact hl ((eN_lt_iff hN x y).1 hij')
      · rw [blkM_lr]; rfl
      · exact absurd hij' (lt_asymm (eN_inl_lt_inr hN y ()))
      · exact absurd hij' (lt_irrefl _)
    · obtain ⟨x, rfl⟩ := (eN hN).surjective i
      rcases x with x | ⟨⟩
      · rw [blkM_ll]
        exact hd x
      · rw [blkM_rr]

theorem blkM_isUpUni (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K)
    (b a : Fin m → K) (d : K) : IsUpUni (blkM hN A b a d) ↔ IsUpUni A ∧ a = 0 ∧ d = 1 := by
  constructor
  · rintro ⟨hl, hd⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ?_, ?_⟩
    · have hh : blkM hN A b a d (eN hN (Sum.inl i)) (eN hN (Sum.inl j)) = 0 :=
        hl ((eN_lt_iff hN j i).2 hij)
      rwa [blkM_ll] at hh
    · have hh : blkM hN A b a d (eN hN (Sum.inl i)) (eN hN (Sum.inl i)) = 1 := hd _
      rwa [blkM_ll] at hh
    · funext i
      have hh : blkM hN A b a d (eN hN (Sum.inr ())) (eN hN (Sum.inl i)) = 0 :=
        hl (eN_inl_lt_inr hN i ())
      rwa [blkM_rl] at hh
    · have hh : blkM hN A b a d (eN hN (Sum.inr ())) (eN hN (Sum.inr ())) = 1 := hd _
      rwa [blkM_rr] at hh
  · rintro ⟨⟨hl, hd⟩, rfl, rfl⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hij' : j < i := hij
      obtain ⟨x, rfl⟩ := (eN hN).surjective i
      obtain ⟨y, rfl⟩ := (eN hN).surjective j
      rcases x with x | ⟨⟩ <;> rcases y with y | ⟨⟩
      · rw [blkM_ll]
        exact hl ((eN_lt_iff hN y x).1 hij')
      · exact absurd hij' (lt_asymm (eN_inl_lt_inr hN x ()))
      · rw [blkM_rl]; rfl
      · exact absurd hij' (lt_irrefl _)
    · obtain ⟨x, rfl⟩ := (eN hN).surjective i
      rcases x with x | ⟨⟩
      · rw [blkM_ll]
        exact hd x
      · rw [blkM_rr]

def lastE (x : Fin m → K) : K := ∑ j : Fin m, if j.val + 1 = m then x j else 0

def bigZ (hN : N = m + 1) (Z : Matrix (Fin m) (Fin m) K) (ξ η : Fin m → K) (c : K) :
    Matrix (Fin N) (Fin N) K :=
  blkM hN Z (Z *ᵥ η) (ξ ᵥ* Z) (ξ ⬝ᵥ (Z *ᵥ η) + c)

end GlobalTheory

section Par
variable {K : Type} [CommRing K] (R : Subring K)

abbrev Par (h : Point K) : Type := Cos R h × (Fin h.1.sum → KR R) × (Fin h.1.sum → KR R)

def outV {m : ℕ} (x : Fin m → KR R) : Fin m → K := fun j => Quotient.out (x j)

theorem addBlock_sum (h : Point K) (c : Kˣ) : (addBlock h 1 c).1.sum = h.1.sum + 1 := by
  simp [addBlock]

def toCos {w : Point K} (p : lowW K w.1 w.2 × upUniG K w.1.sum) : Cos R w :=
  (Quotient.mk _ p.1, QuotientGroup.mk p.2)

open Classical in

def Gterm (ψ : AddChar K ℂ) (w w' : Point K) (p : lowW K w.1 w.2 × upUniG K w.1.sum)
    (p' : lowW K w'.1 w'.2 × upUniG K w'.1.sum) : ℂ :=
  (if IsInt R (orbZ w p) ∧ IsInt R (orbZ w' p') then
    (Nat.card (isoZZ R (orbZ w p) (orbZ w' p')) : ℂ) else 0) * phase ψ p * conj (phase ψ p')

end Par

section SecPart

section SecBlk
variable {K : Type} [CommRing K] {m N : ℕ}

theorem sec_pt (h : Point K) (c : Kˣ) :
    pt (addBlock h 1 c).1 (addBlock h 1 c).2 =
      blkM (addBlock_sum h c) (pt h.1 h.2) 0 0 (c : K) := by
  ext x y
  obtain ⟨x, rfl⟩ := (eN (addBlock_sum h c)).surjective x
  obtain ⟨y, rfl⟩ := (eN (addBlock_sum h c)).surjective y
  rcases x with x | x <;> rcases y with y | y
  · rw [blkM_ll]
    simp only [pt, eN_inl]
    change (if (y : ℕ) = revIn (h.1 ++ [1]) x then
      ((Function.update h.2 h.1.length c (blk (h.1 ++ [1]) x) : Kˣ) : K) else 0) = _
    rw [A5x7.revIn_app_lt 1 _ _ x.2, A5x7.blk_app_lt 1 _ _ x.2,
      Function.update_of_ne (ne_of_lt (A5x7.blk_lt_length _ _ x.2))]
  · rw [blkM_lr]
    simp only [pt, eN_inl, eN_inr]
    change (if h.1.sum = revIn (h.1 ++ [1]) x then
      ((Function.update h.2 h.1.length c (blk (h.1 ++ [1]) x) : Kˣ) : K) else 0) = _
    rw [A5x7.revIn_app_lt 1 _ _ x.2, if_neg (ne_of_gt (Formalism.DoubleCosetMeasures.P.Phase.revIn_lt _ _ x.2))]
    rfl
  · rw [blkM_rl]
    simp only [pt, eN_inl, eN_inr]
    change (if (y : ℕ) = revIn (h.1 ++ [1]) h.1.sum then
      ((Function.update h.2 h.1.length c (blk (h.1 ++ [1]) h.1.sum) : Kˣ) : K) else 0) = _
    rw [A5x7.revIn_app _ 1 le_rfl, if_neg (by have := y.2; omega)]
    rfl
  · rw [blkM_rr]
    simp only [pt, eN_inr]
    change (if h.1.sum = revIn (h.1 ++ [1]) h.1.sum then
      ((Function.update h.2 h.1.length c (blk (h.1 ++ [1]) h.1.sum) : Kˣ) : K) else 0) = _
    rw [A5x7.revIn_app _ 1 le_rfl, A5x7.blk_app _ 1 le_rfl, if_pos (by omega), Function.update_self]

theorem sec_sLow (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K) (b a : Fin m → K) (d : K) :
    sLow (blkM hN A b a d) = sLow A + lastE a := by
  unfold sLow lastE
  rw [← (eN hN).sum_comp, Fintype.sum_sum_type]
  have hinr : ¬ (((eN hN (Sum.inr ())) : Fin N) : ℕ) + 1 < N := by
    rw [eN_inr]
    omega
  simp only [Fintype.univ_unit, Finset.sum_singleton]
  rw [dif_neg hinr, add_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := i.isLt
  have hlt : ((eN hN (Sum.inl i) : Fin N) : ℕ) + 1 < N := by
    rw [eN_inl]
    omega
  rw [dif_pos hlt]
  by_cases h : i.val + 1 < m
  · have e : (⟨((eN hN (Sum.inl i) : Fin N) : ℕ) + 1, hlt⟩ : Fin N) = eN hN (Sum.inl ⟨i.val + 1, h⟩) := by
      ext
      simp [eN_inl]
    rw [e, blkM_ll, dif_pos h, if_neg (by omega), add_zero]
  · have e : (⟨((eN hN (Sum.inl i) : Fin N) : ℕ) + 1, hlt⟩ : Fin N) = eN hN (Sum.inr ()) := by
      ext
      simp only [eN_inl, eN_inr]
      omega
    rw [e, blkM_rl, dif_neg h, if_pos (by omega), zero_add]

theorem sec_sUp (hN : N = m + 1) (A : Matrix (Fin m) (Fin m) K) (b a : Fin m → K) (d : K) :
    sUp (blkM hN A b a d) = sUp A + lastE b := by
  unfold sUp lastE
  rw [← (eN hN).sum_comp, Fintype.sum_sum_type]
  have hinr : ¬ (((eN hN (Sum.inr ())) : Fin N) : ℕ) + 1 < N := by
    rw [eN_inr]
    omega
  simp only [Fintype.univ_unit, Finset.sum_singleton]
  rw [dif_neg hinr, add_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := i.isLt
  have hlt : ((eN hN (Sum.inl i) : Fin N) : ℕ) + 1 < N := by
    rw [eN_inl]
    omega
  rw [dif_pos hlt]
  by_cases h : i.val + 1 < m
  · have e : (⟨((eN hN (Sum.inl i) : Fin N) : ℕ) + 1, hlt⟩ : Fin N) = eN hN (Sum.inl ⟨i.val + 1, h⟩) := by
      ext
      simp [eN_inl]
    rw [e, blkM_ll, dif_pos h, if_neg (by omega), add_zero]
  · have e : (⟨((eN hN (Sum.inl i) : Fin N) : ℕ) + 1, hlt⟩ : Fin N) = eN hN (Sum.inr ()) := by
      ext
      simp only [eN_inl, eN_inr]
      omega
    rw [e, blkM_lr, dif_neg h, if_pos (by omega), zero_add]

theorem sec_lastE_vecMul {v : Matrix (Fin m) (Fin m) K} (hv : IsLowUni v) (ξ : Fin m → K) :
    lastE (ξ ᵥ* v) = lastE ξ := by
  unfold lastE
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hj
  · rw [vecMul, dotProduct, Finset.sum_eq_single j]
    · rw [hv.2 j, mul_one]
    · intro k _ hk
      have hkj : k < j := by
        rw [Fin.lt_iff_val_lt_val]
        have := k.isLt
        have : k.val ≠ j.val := fun h => hk (Fin.ext h)
        omega
      have h0 : v k j = 0 := hv.1 hkj
      rw [h0, mul_zero]
    · simp
  · rfl

theorem sec_lastE_mulVec {u : Matrix (Fin m) (Fin m) K} (hu : IsUpUni u) (η : Fin m → K) :
    lastE (u *ᵥ η) = lastE η := by
  unfold lastE
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hj
  · rw [mulVec, dotProduct, Finset.sum_eq_single j]
    · rw [hu.2 j, one_mul]
    · intro k _ hk
      have hkj : k < j := by
        rw [Fin.lt_iff_val_lt_val]
        have := k.isLt
        have : k.val ≠ j.val := fun h => hk (Fin.ext h)
        omega
      have h0 : u j k = 0 := hu.1 hkj
      rw [h0, zero_mul]
    · simp
  · rfl

end SecBlk

section SecGrp
variable {K : Type} [CommRing K]

abbrev sec_m {n : ℕ} {H : Subgroup (GL (Fin n) K)} (g : H) : Matrix (Fin n) (Fin n) K :=
  ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

theorem sec_m_ext {n : ℕ} {H : Subgroup (GL (Fin n) K)} {g g' : H} (h : sec_m g = sec_m g') :
    g = g' := by
  exact Subtype.ext (Units.ext h)

def sec_gl {n : ℕ} (x : Matrix (Fin n) (Fin n) K) (hx : x.det = 1) : GL (Fin n) K :=
  Matrix.nonsingInvUnit x (by rw [hx]; exact isUnit_one)

theorem sec_gl_coe {n : ℕ} (x : Matrix (Fin n) (Fin n) K) (hx : x.det = 1) :
    ((sec_gl x hx : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = x := rfl

variable {m N : ℕ}

theorem sec_mul_low (hN : N = m + 1) (A A' : Matrix (Fin m) (Fin m) K) (a a' : Fin m → K) :
    blkM hN A 0 a 1 * blkM hN A' 0 a' 1 = blkM hN (A * A') 0 (a ᵥ* A' + a') 1 := by
  rw [blkM_mul]
  congr 1 <;> simp

theorem sec_mul_up (hN : N = m + 1) (A A' : Matrix (Fin m) (Fin m) K) (b b' : Fin m → K) :
    blkM hN A b 0 1 * blkM hN A' b' 0 1 = blkM hN (A * A') (A *ᵥ b' + b) 0 1 := by
  rw [blkM_mul]
  congr 1 <;> simp

theorem sec_low_mem (h : Point K) (c : Kˣ) (A : Matrix (Fin h.1.sum) (Fin h.1.sum) K)
    (a : Fin h.1.sum → K) :
    (IsLowUni (blkM (addBlock_sum h c) A 0 a 1) ∧
      ∃ H : Matrix (Fin (addBlock h 1 c).1.sum) (Fin (addBlock h 1 c).1.sum) K, IsLowUni H ∧
        blkM (addBlock_sum h c) A 0 a 1 * pt (addBlock h 1 c).1 (addBlock h 1 c).2 =
          pt (addBlock h 1 c).1 (addBlock h 1 c).2 * H) ↔
    (IsLowUni A ∧ ∃ H : Matrix (Fin h.1.sum) (Fin h.1.sum) K, IsLowUni H ∧
      A * pt h.1 h.2 = pt h.1 h.2 * H) := by
  rw [sec_pt]
  constructor
  · rintro ⟨h1, H, hH, e⟩
    refine ⟨((blkM_isLowUni _ _ _ _ _).1 h1).1, ?_⟩
    rw [eq_blkM (addBlock_sum h c) H] at hH e
    refine ⟨_, ((blkM_isLowUni _ _ _ _ _).1 hH).1, ?_⟩
    rw [blkM_mul, blkM_mul] at e
    have := (blkM_inj _ e).1
    simpa using this
  · rintro ⟨h1, H, hH, e⟩
    refine ⟨(blkM_isLowUni _ _ _ _ _).2 ⟨h1, rfl, rfl⟩,
      blkM (addBlock_sum h c) H 0 (((c⁻¹ : Kˣ) : K) • (a ᵥ* pt h.1 h.2)) 1,
      (blkM_isLowUni _ _ _ _ _).2 ⟨hH, rfl, rfl⟩, ?_⟩
    rw [blkM_mul, blkM_mul]
    congr 1
    · simp [e]
    · simp
    · simp [smul_smul]
    · simp

def sec_lowJ (h : Point K) (c : Kˣ) (v : lowW K h.1 h.2) (ξ : Fin h.1.sum → K) :
    lowW K (addBlock h 1 c).1 (addBlock h 1 c).2 :=
  ⟨sec_gl (blkM (addBlock_sum h c) (sec_m v) 0 (ξ ᵥ* sec_m v) 1)
    (isLowUni_det K ((blkM_isLowUni _ _ _ _ _).2 ⟨v.2.1, rfl, rfl⟩)),
    (sec_low_mem h c (sec_m v) (ξ ᵥ* sec_m v)).2 v.2⟩

theorem sec_lowJ_m (h : Point K) (c : Kˣ) (v : lowW K h.1 h.2) (ξ : Fin h.1.sum → K) :
    sec_m (sec_lowJ h c v ξ) = blkM (addBlock_sum h c) (sec_m v) 0 (ξ ᵥ* sec_m v) 1 := rfl

def sec_upJ (h : Point K) (c : Kˣ) (u : upUniG K h.1.sum) (η : Fin h.1.sum → K) :
    upUniG K (addBlock h 1 c).1.sum :=
  ⟨sec_gl (blkM (addBlock_sum h c) (sec_m u) (sec_m u *ᵥ η) 0 1)
    (isUpUni_det K ((blkM_isUpUni _ _ _ _ _).2 ⟨u.2, rfl, rfl⟩)),
    (blkM_isUpUni _ _ _ _ _).2 ⟨u.2, rfl, rfl⟩⟩

theorem sec_upJ_m (h : Point K) (c : Kˣ) (u : upUniG K h.1.sum) (η : Fin h.1.sum → K) :
    sec_m (sec_upJ h c u η) = blkM (addBlock_sum h c) (sec_m u) (sec_m u *ᵥ η) 0 1 := rfl

theorem sec_orbZ (h : Point K) (c : Kˣ) (p : lowW K h.1 h.2 × upUniG K h.1.sum)
    (ξ η : Fin h.1.sum → K) :
    orbZ (addBlock h 1 c) (sec_lowJ h c p.1 ξ, sec_upJ h c p.2 η) =
      bigZ (addBlock_sum h c) (orbZ h p) ξ η (c : K) := by
  unfold orbZ bigZ
  change sec_m (sec_lowJ h c p.1 ξ) * _ * sec_m (sec_upJ h c p.2 η) = _
  rw [sec_lowJ_m, sec_upJ_m, sec_pt, blkM_mul, blkM_mul]
  congr 1
  · simp
  · simp [Matrix.mulVec_mulVec]
  · simp [Matrix.vecMul_vecMul, Matrix.mul_assoc]
  · simp [Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec, Matrix.mul_assoc]

theorem sec_phase (h : Point K) (c : Kˣ) (p : lowW K h.1 h.2 × upUniG K h.1.sum)
    (ξ η : Fin h.1.sum → K) (ψ : AddChar K ℂ) :
    phase ψ ((sec_lowJ h c p.1 ξ, sec_upJ h c p.2 η) :
      lowW K (addBlock h 1 c).1 (addBlock h 1 c).2 × upUniG K (addBlock h 1 c).1.sum) =
      phase ψ p * ψ (lastE ξ + lastE η) := by
  show ψ (sLow (sec_m (sec_lowJ h c p.1 ξ)) + sUp (sec_m (sec_upJ h c p.2 η))) =
    ψ (sLow (sec_m p.1) + sUp (sec_m p.2)) * ψ (lastE ξ + lastE η)
  rw [sec_lowJ_m, sec_upJ_m, sec_sLow, sec_sUp, sec_lastE_vecMul p.1.2.1, sec_lastE_mulVec p.2.2,
    ← AddChar.map_add_eq_mul]
  congr 1
  ring

end SecGrp

section SecFib

theorem sec_fib {A X G QA QX QG : Type} (cA : A → QA) (oA : QA → A) (hA : ∀ q, cA (oA q) = q)
    (cX : X → QX) (oX : QX → X) (hX : ∀ q, cX (oX q) = q) (cG : G → QG)
    (hG : Function.Surjective cG) (J : A → X → G) (S : ∀ g, ∃ a x, g = J a x)
    (E1 : ∀ a x a' x', cG (J a x) = cG (J a' x') → cA a = cA a')
    (E2 : ∀ a x x', cG (J a x) = cG (J a x') ↔ cX x = cX x')
    (E3 : ∀ a a', cA a = cA a' → ∀ x, ∃ x', cG (J a x) = cG (J a' x')) :
    Function.Bijective (fun p : QA × QX => cG (J (oA p.1) (oX p.2))) := by
  constructor
  · rintro ⟨p, q⟩ ⟨p', q'⟩ h
    simp only at h
    have h1 := E1 _ _ _ _ h
    rw [hA, hA] at h1
    subst h1
    have h2 := (E2 _ _ _).1 h
    rw [hX, hX] at h2
    rw [h2]
  · intro g'
    obtain ⟨g, rfl⟩ := hG g'
    obtain ⟨a, x, rfl⟩ := S g
    obtain ⟨x', hx'⟩ := E3 a (oA (cA a)) (hA _).symm x
    refine ⟨(cA a, cX x'), ?_⟩
    simp only
    rw [hx']
    exact (E2 _ _ _).2 (hX _)

variable {K : Type} [CommRing K] (R : Subring K)

theorem sec_right_eq {G : Type} [Group G] (S : Subgroup G) (x y : G) :
    (Quotient.mk (QuotientGroup.rightRel S) x = Quotient.mk (QuotientGroup.rightRel S) y) ↔
      ∃ g ∈ S, y = g * x := by
  rw [Quotient.eq, QuotientGroup.rightRel_apply]
  constructor
  · intro h
    exact ⟨_, h, by group⟩
  · rintro ⟨g, hg, rfl⟩
    simpa using hg

theorem sec_left_eq {G : Type} [Group G] (S : Subgroup G) (x y : G) :
    ((x : G ⧸ S) = (y : G ⧸ S)) ↔ ∃ g ∈ S, y = x * g := by
  rw [QuotientGroup.eq]
  constructor
  · intro h
    exact ⟨_, h, by group⟩
  · rintro ⟨g, hg, rfl⟩
    simpa using hg

def sec_cX {m : ℕ} (x : Fin m → K) : Fin m → KR R := fun j => Submodule.Quotient.mk (x j)

theorem sec_cX_outV {m : ℕ} (q : Fin m → KR R) : sec_cX R (outV R q) = q := by
  funext j
  exact Quotient.out_eq (q j)

theorem sec_cX_eq {m : ℕ} (x x' : Fin m → K) :
    sec_cX R x = sec_cX R x' ↔ ∀ j, (x' - x) j ∈ R := by
  simp only [funext_iff, sec_cX, Submodule.Quotient.eq', Pi.sub_apply]
  refine forall_congr' fun j => ?_
  rw [neg_add_eq_sub, LinearMap.mem_range]
  constructor
  · rintro ⟨r, hr⟩
    rw [← hr]
    exact r.2
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩

theorem sec_mem_int {n : ℕ} {H : Subgroup (GL (Fin n) K)} (g : H) (hd : (sec_m g).det = 1) :
    g ∈ intSub R H ↔ IsInt R (sec_m g) := by
  constructor
  · intro hg
    exact hg.1
  · intro h
    refine ⟨h, ?_⟩
    let B : Matrix (Fin n) (Fin n) R := fun a b => ⟨sec_m g a b, h a b⟩
    have hB : R.subtype.mapMatrix B = sec_m g := by
      ext a b
      rfl
    have hinv : (((g : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (sec_m g).adjugate := by
      rw [Matrix.coe_units_inv, Matrix.inv_def]
      simp [sec_m] at hd ⊢
      simp [hd]
    intro a b
    rw [hinv, ← hB, ← RingHom.map_adjugate]
    exact (B.adjugate a b).2

theorem sec_vecMul_int {m : ℕ} {A : Matrix (Fin m) (Fin m) K} (hA : IsInt R A) {x : Fin m → K}
    (hx : ∀ j, x j ∈ R) (j : Fin m) : (x ᵥ* A) j ∈ R := by
  simp only [vecMul, dotProduct]
  exact R.sum_mem fun k _ => R.mul_mem (hx k) (hA k j)

theorem sec_mulVec_int {m : ℕ} {A : Matrix (Fin m) (Fin m) K} (hA : IsInt R A) {x : Fin m → K}
    (hx : ∀ j, x j ∈ R) (j : Fin m) : (A *ᵥ x) j ∈ R := by
  simp only [mulVec, dotProduct]
  exact R.sum_mem fun k _ => R.mul_mem (hA j k) (hx k)

theorem sec_lowJ_mul (h : Point K) (c : Kˣ) (a v : lowW K h.1 h.2) (ρ ξ : Fin h.1.sum → K) :
    sec_lowJ h c a ρ * sec_lowJ h c v ξ = sec_lowJ h c (a * v) (ρ + ξ ᵥ* (sec_m a)⁻¹) := by
  have hinv : (sec_m a)⁻¹ * sec_m a = 1 := by
    rw [sec_m, ← Matrix.coe_units_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hav : sec_m (a * v) = sec_m a * sec_m v := rfl
  apply sec_m_ext
  rw [show sec_m (sec_lowJ h c a ρ * sec_lowJ h c v ξ) =
      sec_m (sec_lowJ h c a ρ) * sec_m (sec_lowJ h c v ξ) from rfl, sec_lowJ_m, sec_lowJ_m, sec_lowJ_m,
    sec_mul_low, hav]
  congr 2
  simp only [Matrix.add_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hinv, Matrix.one_mul]

theorem sec_lowJ_surj (h : Point K) (c : Kˣ) (V : lowW K (addBlock h 1 c).1 (addBlock h 1 c).2) :
    ∃ v ξ, V = sec_lowJ h c v ξ := by
  obtain ⟨A, b, a, d, hM⟩ : ∃ A b a d, sec_m V = blkM (addBlock_sum h c) A b a d :=
    ⟨_, _, _, _, eq_blkM (addBlock_sum h c) (sec_m V)⟩
  have hV := V.2
  change IsLowUni (sec_m V) ∧ ∃ H, IsLowUni H ∧ sec_m V * _ = _ * H at hV
  obtain ⟨hA, hb, hd⟩ := (blkM_isLowUni _ _ _ _ _).1 (hM ▸ hV.1)
  subst hb hd
  rw [hM] at hV
  have hv := (sec_low_mem h c _ _).1 hV
  refine ⟨⟨sec_gl A (isLowUni_det K hA), hv⟩, a ᵥ* A⁻¹, ?_⟩
  apply sec_m_ext
  rw [sec_lowJ_m, hM]
  congr 1
  change _ = (a ᵥ* A⁻¹) ᵥ* A
  rw [Matrix.vecMul_vecMul, Formalism.DoubleCosetMeasures.P.Phase.inv_mul_one_low hA, Matrix.vecMul_one]

theorem sec_lowJ_inj (h : Point K) (c : Kˣ) {v v' : lowW K h.1 h.2} {ξ ξ' : Fin h.1.sum → K}
    (e : sec_lowJ h c v ξ = sec_lowJ h c v' ξ') : v = v' ∧ ξ = ξ' := by
  have e1 := congrArg sec_m e
  rw [sec_lowJ_m, sec_lowJ_m] at e1
  obtain ⟨hA, -, ha, -⟩ := blkM_inj _ e1
  have hv : v = v' := sec_m_ext hA
  subst hv
  refine ⟨rfl, ?_⟩
  have hinv : sec_m v * (sec_m v)⁻¹ = 1 := by
    rw [sec_m, ← Matrix.coe_units_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ξ ᵥ* sec_m v ᵥ* (sec_m v)⁻¹ = ξ' ᵥ* sec_m v ᵥ* (sec_m v)⁻¹ := by rw [ha]
  simpa [Matrix.vecMul_vecMul, hinv] using h2

theorem sec_lowJ_int (h : Point K) (c : Kˣ) (a : lowW K h.1 h.2) (ρ : Fin h.1.sum → K) :
    sec_lowJ h c a ρ ∈ intSub R (lowW K (addBlock h 1 c).1 (addBlock h 1 c).2) ↔
      a ∈ intSub R (lowW K h.1 h.2) ∧ ∀ j, ρ j ∈ R := by
  have hd1 : (sec_m (sec_lowJ h c a ρ)).det = 1 := isLowUni_det K (sec_lowJ h c a ρ).2.1
  have hd2 : (sec_m a).det = 1 := isLowUni_det K a.2.1
  rw [sec_mem_int R _ hd1, sec_mem_int R _ hd2, sec_lowJ_m, blkM_isInt]
  constructor
  · rintro ⟨hA, -, ha, -⟩
    refine ⟨hA, fun j => ?_⟩
    have hmem := (sec_mem_int R a hd2).2 hA
    have hinvI : IsInt R (sec_m a)⁻¹ := by
      have h2 := hmem.2
      rwa [Matrix.coe_units_inv] at h2
    have hinv : sec_m a * (sec_m a)⁻¹ = 1 := by
      rw [sec_m, ← Matrix.coe_units_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e : ρ = (ρ ᵥ* sec_m a) ᵥ* (sec_m a)⁻¹ := by
      rw [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
    rw [e]
    exact sec_vecMul_int R hinvI ha j
  · rintro ⟨hA, hρ⟩
    exact ⟨hA, fun i => R.zero_mem, fun j => sec_vecMul_int R hA hρ j, R.one_mem⟩

theorem sec_low_bij (h : Point K) (c : Kˣ) :
    Function.Bijective (fun p : Quotient (QuotientGroup.rightRel (intSub R (lowW K h.1 h.2))) ×
        (Fin h.1.sum → KR R) =>
      (Quotient.mk (QuotientGroup.rightRel
        (intSub R (lowW K (addBlock h 1 c).1 (addBlock h 1 c).2)))
        (sec_lowJ h c p.1.out (outV R p.2)))) := by
  refine sec_fib (Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K h.1 h.2)))) Quotient.out
    Quotient.out_eq (sec_cX R) (outV R) (sec_cX_outV R) _ Quotient.mk_surjective (sec_lowJ h c)
    (sec_lowJ_surj h c) ?_ ?_ ?_
  · intro a x a' x' e
    obtain ⟨g, hg, e1⟩ := (sec_right_eq _ _ _).1 e
    obtain ⟨a0, ρ, rfl⟩ := sec_lowJ_surj h c g
    rw [sec_lowJ_mul] at e1
    exact (sec_right_eq _ _ _).2 ⟨a0, ((sec_lowJ_int R h c a0 ρ).1 hg).1, (sec_lowJ_inj h c e1).1⟩
  · intro a x x'
    rw [sec_cX_eq]
    constructor
    · intro e
      obtain ⟨g, hg, e1⟩ := (sec_right_eq _ _ _).1 e
      obtain ⟨a0, ρ, rfl⟩ := sec_lowJ_surj h c g
      rw [sec_lowJ_mul] at e1
      obtain ⟨e2, e3⟩ := sec_lowJ_inj h c e1
      have ha0 : a0 = 1 := by simpa using e2.symm
      subst ha0
      have e4 : x' = ρ + x := by
        rw [e3]
        change ρ + x ᵥ* (1 : Matrix (Fin h.1.sum) (Fin h.1.sum) K)⁻¹ = _
        simp
      intro j
      rw [e4]
      simpa using ((sec_lowJ_int R h c 1 ρ).1 hg).2 j
    · intro hx
      refine (sec_right_eq _ _ _).2 ⟨sec_lowJ h c 1 (x' - x),
        (sec_lowJ_int R h c 1 _).2 ⟨Subgroup.one_mem _, hx⟩, ?_⟩
      rw [sec_lowJ_mul, one_mul]
      congr 1
      change x' = x' - x + x ᵥ* (1 : Matrix (Fin h.1.sum) (Fin h.1.sum) K)⁻¹
      simp
  · intro a a' e x
    obtain ⟨a0, ha0, rfl⟩ := (sec_right_eq _ _ _).1 e
    refine ⟨0 + x ᵥ* (sec_m a0)⁻¹, (sec_right_eq _ _ _).2 ⟨sec_lowJ h c a0 0,
      (sec_lowJ_int R h c a0 0).2 ⟨ha0, fun _ => R.zero_mem⟩, ?_⟩⟩
    rw [sec_lowJ_mul]

end SecFib

section SecUp
variable {K : Type} [CommRing K] (R : Subring K)

theorem sec_upJ_mul (h : Point K) (c : Kˣ) (u b : upUniG K h.1.sum) (η ρ : Fin h.1.sum → K) :
    sec_upJ h c u η * sec_upJ h c b ρ = sec_upJ h c (u * b) (ρ + (sec_m b)⁻¹ *ᵥ η) := by
  have hinv : sec_m b * (sec_m b)⁻¹ = 1 := by
    rw [sec_m, ← Matrix.coe_units_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hub : sec_m (u * b) = sec_m u * sec_m b := rfl
  apply sec_m_ext
  rw [show sec_m (sec_upJ h c u η * sec_upJ h c b ρ) =
      sec_m (sec_upJ h c u η) * sec_m (sec_upJ h c b ρ) from rfl, sec_upJ_m, sec_upJ_m, sec_upJ_m,
    sec_mul_up, hub]
  congr 2
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_assoc, hinv, Matrix.mul_one]

theorem sec_upJ_surj (h : Point K) (c : Kˣ) (V : upUniG K (addBlock h 1 c).1.sum) :
    ∃ u η, V = sec_upJ h c u η := by
  have hE := eq_blkM (addBlock_sum h c) (sec_m V)
  set A := Matrix.of fun i j => sec_m V (eN (addBlock_sum h c) (Sum.inl i)) (eN (addBlock_sum h c) (Sum.inl j))
    with hA
  set b := fun i => sec_m V (eN (addBlock_sum h c) (Sum.inl i)) (eN (addBlock_sum h c) (Sum.inr ())) with hb
  set a := fun j => sec_m V (eN (addBlock_sum h c) (Sum.inr ())) (eN (addBlock_sum h c) (Sum.inl j)) with ha
  set d := sec_m V (eN (addBlock_sum h c) (Sum.inr ())) (eN (addBlock_sum h c) (Sum.inr ())) with hd
  have hU : IsUpUni (blkM (addBlock_sum h c) A b a d) := by
    rw [← hE]
    exact V.2
  obtain ⟨hAu, ha0, hd1⟩ := (blkM_isUpUni _ _ _ _ _).1 hU
  have hdet : A.det = 1 := isUpUni_det K hAu
  refine ⟨⟨sec_gl A hdet, hAu⟩, A⁻¹ *ᵥ b, ?_⟩
  apply sec_m_ext
  rw [sec_upJ_m]
  show sec_m V = blkM (addBlock_sum h c) A (A *ᵥ (A⁻¹ *ᵥ b)) 0 1
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (by rw [hdet]; exact isUnit_one), Matrix.one_mulVec,
    ← ha0, ← hd1]
  exact hE

theorem sec_upJ_inj (h : Point K) (c : Kˣ) {u u' : upUniG K h.1.sum} {η η' : Fin h.1.sum → K}
    (e : sec_upJ h c u η = sec_upJ h c u' η') : u = u' ∧ η = η' := by
  have e1 := congrArg sec_m e
  rw [sec_upJ_m, sec_upJ_m] at e1
  obtain ⟨hA, hb, -, -⟩ := blkM_inj _ e1
  have hu : u = u' := sec_m_ext hA
  subst hu
  refine ⟨rfl, ?_⟩
  have hinv : (sec_m u)⁻¹ * sec_m u = 1 := by
    rw [sec_m, ← Matrix.coe_units_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (sec_m u)⁻¹ *ᵥ (sec_m u *ᵥ η) = (sec_m u)⁻¹ *ᵥ (sec_m u *ᵥ η') := by rw [hb]
  simpa [Matrix.mulVec_mulVec, hinv] using h2

theorem sec_upJ_int (h : Point K) (c : Kˣ) (b : upUniG K h.1.sum) (ρ : Fin h.1.sum → K) :
    sec_upJ h c b ρ ∈ intSub R (upUniG K (addBlock h 1 c).1.sum) ↔
      b ∈ intSub R (upUniG K h.1.sum) ∧ ∀ j, ρ j ∈ R := by
  have hd1 : (sec_m (sec_upJ h c b ρ)).det = 1 := isUpUni_det K (sec_upJ h c b ρ).2
  have hd2 : (sec_m b).det = 1 := isUpUni_det K b.2
  rw [sec_mem_int R _ hd1, sec_mem_int R _ hd2, sec_upJ_m, blkM_isInt]
  constructor
  · rintro ⟨hA, hb, -, -⟩
    refine ⟨hA, fun j => ?_⟩
    have hmem := (sec_mem_int R b hd2).2 hA
    have hinvI : IsInt R (sec_m b)⁻¹ := by
      have h2 := hmem.2
      rwa [Matrix.coe_units_inv] at h2
    have hinv : (sec_m b)⁻¹ * sec_m b = 1 := by
      rw [sec_m, ← Matrix.coe_units_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e : ρ = (sec_m b)⁻¹ *ᵥ (sec_m b *ᵥ ρ) := by
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    rw [e]
    exact sec_mulVec_int R hinvI hb j
  · rintro ⟨hA, hρ⟩
    exact ⟨hA, fun i => sec_mulVec_int R hA hρ i, fun j => R.zero_mem, R.one_mem⟩

theorem sec_up_bij (h : Point K) (c : Kˣ) :
    Function.Bijective (fun p : (upUniG K h.1.sum ⧸ intSub R (upUniG K h.1.sum)) ×
        (Fin h.1.sum → KR R) =>
      ((sec_upJ h c p.1.out (outV R p.2) : upUniG K (addBlock h 1 c).1.sum) :
        upUniG K (addBlock h 1 c).1.sum ⧸ intSub R (upUniG K (addBlock h 1 c).1.sum))) := by
  have hJint : ∀ (b : upUniG K h.1.sum) (ρ : Fin h.1.sum → K), b ∈ intSub R (upUniG K h.1.sum) →
      (∀ j, ρ j ∈ R) → sec_upJ h c b ρ ∈ intSub R (upUniG K (addBlock h 1 c).1.sum) :=
    fun b ρ hb hρ => (sec_upJ_int R h c b ρ).2 ⟨hb, hρ⟩
  have hone : ∀ x : Fin h.1.sum → K, (sec_m (1 : upUniG K h.1.sum))⁻¹ *ᵥ x = x := by
    intro x
    simp [sec_m]
  refine sec_fib (A := upUniG K h.1.sum) (X := Fin h.1.sum → K)
    (G := upUniG K (addBlock h 1 c).1.sum) (cA := fun a => (a : upUniG K h.1.sum ⧸ intSub R (upUniG K h.1.sum))) (oA := Quotient.out)
    (fun q => QuotientGroup.out_eq' q) (cX := sec_cX R) (oX := outV R) (sec_cX_outV R)
    (cG := fun g => (g : upUniG K (addBlock h 1 c).1.sum ⧸ intSub R (upUniG K (addBlock h 1 c).1.sum)))
    QuotientGroup.mk_surjective (fun (u : upUniG K h.1.sum) (η : Fin h.1.sum → K) => sec_upJ h c u η) (fun g => sec_upJ_surj h c g) ?_ ?_ ?_
  · intro a x a' x' hq
    obtain ⟨g, hg, e⟩ := (sec_left_eq _ _ _).1 hq
    obtain ⟨b, ρ, rfl⟩ := sec_upJ_surj h c g
    have hbρ := (sec_upJ_int R h c b ρ).1 hg
    rw [sec_upJ_mul] at e
    obtain ⟨e1, -⟩ := sec_upJ_inj h c e
    exact (sec_left_eq _ _ _).2 ⟨b, hbρ.1, e1⟩
  · intro a x x'
    constructor
    · intro hq
      obtain ⟨g, hg, e⟩ := (sec_left_eq _ _ _).1 hq
      obtain ⟨b, ρ, rfl⟩ := sec_upJ_surj h c g
      have hbρ := (sec_upJ_int R h c b ρ).1 hg
      rw [sec_upJ_mul] at e
      obtain ⟨e1, e2⟩ := sec_upJ_inj h c e
      have hb1 : b = 1 := by
        have h3 := congrArg (a⁻¹ * ·) e1
        simpa using h3.symm
      subst hb1
      rw [hone] at e2
      rw [sec_cX_eq]
      intro j
      rw [e2]
      simpa using hbρ.2 j
    · intro hx
      rw [sec_cX_eq] at hx
      apply (sec_left_eq _ _ _).2
      refine ⟨sec_upJ h c 1 (x' - x), hJint 1 _ (one_mem _) hx, ?_⟩
      show sec_upJ h c a x' = sec_upJ h c a x * sec_upJ h c 1 (x' - x)
      rw [sec_upJ_mul, mul_one, hone, sub_add_cancel]
  · intro a a' hq x
    obtain ⟨b, hb, e⟩ := (sec_left_eq _ _ _).1 hq
    refine ⟨(sec_m b)⁻¹ *ᵥ x, ?_⟩
    subst e
    apply (sec_left_eq _ _ _).2
    refine ⟨sec_upJ h c b 0, hJint b 0 hb (fun j => R.zero_mem), ?_⟩
    show sec_upJ h c (a * b) ((sec_m b)⁻¹ *ᵥ x) = sec_upJ h c a x * sec_upJ h c b 0
    rw [sec_upJ_mul, zero_add]

def sec_sigma (h : Point K) (c : Kˣ) (t : Par R h) :
    lowW K (addBlock h 1 c).1 (addBlock h 1 c).2 × upUniG K (addBlock h 1 c).1.sum :=
  (sec_lowJ h c (rep R t.1).1 (outV R t.2.1), sec_upJ h c (rep R t.1).2 (outV R t.2.2))

theorem sec_sigma_bij (h : Point K) (c : Kˣ) :
    Function.Bijective (fun t => toCos R (sec_sigma R h c t)) := by
  have h1 := ((sec_low_bij R h c).prodMap (sec_up_bij R h c)).comp
    (Equiv.prodProdProdComm (Quotient (QuotientGroup.rightRel (intSub R (lowW K h.1 h.2))))
      (upUniG K h.1.sum ⧸ intSub R (upUniG K h.1.sum)) (Fin h.1.sum → KR R)
      (Fin h.1.sum → KR R)).bijective
  exact h1

theorem section_exists (h : Point K) (c : Kˣ) :
    ∃ σ : Par R h → lowW K (addBlock h 1 c).1 (addBlock h 1 c).2 × upUniG K (addBlock h 1 c).1.sum,
      Function.Bijective (fun t => toCos R (σ t)) ∧
      ∀ t, orbZ (addBlock h 1 c) (σ t) =
          bigZ (addBlock_sum h c) (orbZ h (rep R t.1)) (outV R t.2.1) (outV R t.2.2) (c : K) ∧
        ∀ ψ : AddChar K ℂ, phase ψ (σ t) =
          phase ψ (rep R t.1) * ψ (lastE (outV R t.2.1) + lastE (outV R t.2.2)) :=
  ⟨sec_sigma R h c, sec_sigma_bij R h c, fun t => ⟨sec_orbZ h c (rep R t.1) _ _, fun ψ =>
      sec_phase h c (rep R t.1) _ _ ψ⟩⟩

end SecUp

end SecPart

section InvPart

variable {K : Type} [CommRing K] (R : Subring K)

theorem inv_exists {w : Point K} (p p₁ : lowW K w.1 w.2 × upUniG K w.1.sum)
    (h : toCos R p = toCos R p₁) :
    ∃ a ∈ intSub R (lowW K w.1 w.2), ∃ b ∈ intSub R (upUniG K w.1.sum),
      p₁ = (a * p.1, p.2 * b) := by
  unfold toCos at h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
  obtain ⟨a, ha, e1⟩ := (sec_right_eq _ _ _).1 h1
  obtain ⟨b, hb, e2⟩ := (sec_left_eq _ _ _).1 h2
  exact ⟨a, ha, b, hb, Prod.ext e1 e2⟩

theorem inv_orbZ (w : Point K) (a x : lowW K w.1 w.2) (y b : upUniG K w.1.sum) :
    orbZ w (a * x, y * b) =
      ((a : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) * orbZ w (x, y) *
        ((b : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := by
  simp only [orbZ, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]

theorem inv_iso (w : Point K) (a : lowW K w.1 w.2) (ha : a ∈ intSub R (lowW K w.1 w.2))
    (b : upUniG K w.1.sum) (hb : b ∈ intSub R (upUniG K w.1.sum))
    (x : lowW K w.1 w.2) (y : upUniG K w.1.sum) :
    ∃ φ : coker R (orbZ w (x, y)) ≃ₗ[R] coker R (orbZ w (a * x, y * b)),
      φ ∈ isoZZ R (orbZ w (x, y)) (orbZ w (a * x, y * b)) := by
  rw [inv_orbZ]
  have haL : IsLowUni ((a : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := a.2.1
  have hbU : IsUpUni ((b : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := b.2
  have haI : IsInt R ((a : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := ha.1
  have hbI : IsInt R ((b : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := hb.1
  generalize ((a : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) = a0 at *
  generalize ((b : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) = b0 at *
  generalize orbZ w (x, y) = Z
  obtain ⟨A, rfl⟩ : ∃ A : Matrix (Fin w.1.sum) (Fin w.1.sum) R, A.map R.subtype = a0 :=
    ⟨Formalism.DoubleCosetMeasures.P.liftR R a0 haI, Formalism.DoubleCosetMeasures.P.liftR_map R a0 haI⟩
  obtain ⟨B, rfl⟩ : ∃ B : Matrix (Fin w.1.sum) (Fin w.1.sum) R, B.map R.subtype = b0 :=
    ⟨Formalism.DoubleCosetMeasures.P.liftR R b0 hbI, Formalism.DoubleCosetMeasures.P.liftR_map R b0 hbI⟩
  have hA := isLowUni_det K haL
  have hB := isUpUni_det K hbU
  refine ⟨Formalism.DoubleCosetMeasures.P.cokEquiv R A B Z hA hB, Formalism.DoubleCosetMeasures.P.cokEquiv_eZ R A B Z hA hB haL,
    fun v v' hv => ?_⟩
  rw [Formalism.DoubleCosetMeasures.P.cokEquiv_mk] at hv
  rw [← Formalism.FourierDecayAlt.P.A5x4.lamLin_mk_eq R _ hv, Formalism.DoubleCosetMeasures.P.lamLin_mul R A B Z hA hbU]

theorem inv_phase (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (w : Point K)
    (a : lowW K w.1 w.2) (ha : a ∈ intSub R (lowW K w.1 w.2))
    (b : upUniG K w.1.sum) (hb : b ∈ intSub R (upUniG K w.1.sum))
    (x : lowW K w.1 w.2) (y : upUniG K w.1.sum) :
    phase ψ ((a * x, y * b) : lowW K w.1 w.2 × upUniG K w.1.sum) = phase ψ (x, y) := by
  have hSA := Formalism.DoubleCosetMeasures.Final.simpleAdd
  unfold phase
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [(hSA K _ _ _).1 a.2.1 x.2.1, (hSA K _ _ _).2 y.2 b.2]
  have hLa : sLow ((a : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) ∈ R := by
    unfold sLow
    refine R.sum_mem fun j _ => ?_
    split_ifs
    · exact ha.1 _ _
    · exact R.zero_mem
  have hUb : sUp ((b : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) ∈ R := by
    unfold sUp
    refine R.sum_mem fun j _ => ?_
    split_ifs
    · exact hb.1 _ _
    · exact R.zero_mem
  have key : ∀ p q r s : K, p + q + (r + s) = (q + r) + (p + s) := by
    intro p q r s
    ring
  rw [key, AddChar.map_add_eq_mul, hψ _ (R.add_mem hLa hUb), mul_one]

theorem Gterm_inv (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (w w' : Point K)
    (p p₁ : lowW K w.1 w.2 × upUniG K w.1.sum) (p' p₁' : lowW K w'.1 w'.2 × upUniG K w'.1.sum)
    (h : toCos R p = toCos R p₁) (h' : toCos R p' = toCos R p₁') :
    Gterm R ψ w w' p p' = Gterm R ψ w w' p₁ p₁' := by
  obtain ⟨a, ha, b, hb, rfl⟩ := inv_exists R p p₁ h
  obtain ⟨a', ha', b', hb', rfl⟩ := inv_exists R p' p₁' h'
  obtain ⟨x, y⟩ := p
  obtain ⟨x', y'⟩ := p'
  obtain ⟨φ, hφ⟩ := inv_iso R w a ha b hb x y
  obtain ⟨φ', hφ'⟩ := inv_iso R w' a' ha' b' hb' x' y'
  simp only [Gterm]
  rw [inv_phase R ψ hψ w a ha b hb x y, inv_phase R ψ hψ w' a' ha' b' hb' x' y',
    Formalism.FourierDecayAlt.P.A5x4.card_isoZZ_congr R hφ hφ']
  have e1 := Formalism.FourierDecayAlt.P.A5x4.isInt_orbZ_inv R w a ha b hb x y
  have e2 := Formalism.FourierDecayAlt.P.A5x4.isInt_orbZ_inv R w' a' ha' b' hb' x' y'
  by_cases hc : IsInt R (orbZ w (x, y)) ∧ IsInt R (orbZ w' (x', y'))
  · rw [if_pos hc, if_pos ⟨e1.2 hc.1, e2.2 hc.2⟩]
  · rw [if_neg hc, if_neg (fun h => hc ⟨e1.1 h.1, e2.1 h.2⟩)]

theorem inv_toCos_rep {w : Point K} (q : Cos R w) : toCos R (rep R q) = q := by
  unfold toCos rep
  exact Prod.ext (Quotient.out_eq _) (QuotientGroup.out_eq' _)

theorem Kp_eq_section (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (w w' : Point K) (T T' : Type)
    (σ : T → lowW K w.1 w.2 × upUniG K w.1.sum) (σ' : T' → lowW K w'.1 w'.2 × upUniG K w'.1.sum)
    (hσ : Function.Bijective (fun t => toCos R (σ t)))
    (hσ' : Function.Bijective (fun t => toCos R (σ' t))) :
    Kp R ψ w w' = ∑ᶠ x : T × T', Gterm R ψ w w' (σ x.1) (σ' x.2) := by
  unfold Kp
  symm
  refine finsum_eq_of_bijective
    (fun x : T × T' => ((toCos R (σ x.1), toCos R (σ' x.2)) : Cos R w × Cos R w'))
    (hσ.prodMap hσ') fun x => ?_
  show _ = Gterm R ψ w w' (rep R (toCos R (σ x.1))) (rep R (toCos R (σ' x.2)))
  exact Gterm_inv R ψ hψ w w' _ _ _ _ (inv_toCos_rep R _).symm (inv_toCos_rep R _).symm

end InvPart

section IsoPart

section IsoAbs
variable {K : Type} [CommRing K] (R : Subring K)

structure iso_Dat (M C : Type) [AddCommGroup M] [Module R M] [AddCommGroup C] [Module R C]
    (γ : Kˣ) (Φ : M →ₗ[R] K) (π : M →ₗ[R] C) (g : M) (lam : C →ₗ[R] KR R) : Prop where
  surj : Function.Surjective π
  ker : ∀ x, π x = 0 → ∃ r : R, x = r • g
  pg : π g = 0
  Pg : Φ g = (γ : K)
  lam_pi : ∀ x, lam (π x) = Submodule.Quotient.mk (((γ⁻¹ : Kˣ) : K) * Φ x)

variable {R}
variable {M₁ M₂ C₁ C₂ : Type} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂] {γ : Kˣ}
  {Φ₁ : M₁ →ₗ[R] K} {π₁ : M₁ →ₗ[R] C₁} {g₁ : M₁} {lam₁ : C₁ →ₗ[R] KR R}
  {Φ₂ : M₂ →ₗ[R] K} {π₂ : M₂ →ₗ[R] C₂} {g₂ : M₂} {lam₂ : C₂ →ₗ[R] KR R}

theorem iso_uniq (D : iso_Dat R M₁ C₁ γ Φ₁ π₁ g₁ lam₁) {x y : M₁} (h1 : π₁ x = π₁ y)
    (h2 : Φ₁ x = Φ₁ y) : x = y := by
  obtain ⟨r, hr⟩ := D.ker (x - y) (by rw [map_sub, h1, sub_self])
  have h0 : Φ₁ (x - y) = 0 := by rw [map_sub, h2, sub_self]
  rw [hr, map_smul, D.Pg] at h0
  have hr0 : (r : K) = 0 := by
    have h3 : (r : K) * (γ : K) = 0 := h0
    exact (Units.mul_left_eq_zero γ).mp h3
  have hr1 : r = 0 := Subtype.ext hr0
  rw [hr1, zero_smul, sub_eq_zero] at hr
  exact hr

theorem iso_ex (D : iso_Dat R M₂ C₂ γ Φ₂ π₂ g₂ lam₂) (y : C₂) (k : K)
    (h : lam₂ y = Submodule.Quotient.mk (((γ⁻¹ : Kˣ) : K) * k)) : ∃ x, π₂ x = y ∧ Φ₂ x = k := by
  obtain ⟨x0, hx0⟩ := D.surj y
  have h1 := D.lam_pi x0
  rw [hx0, h, Submodule.Quotient.eq, LinearMap.mem_range] at h1
  obtain ⟨s, hs⟩ := h1
  have hs' : (s : K) = ((γ⁻¹ : Kˣ) : K) * k - ((γ⁻¹ : Kˣ) : K) * Φ₂ x0 := hs
  refine ⟨x0 + s • g₂, by rw [map_add, map_smul, D.pg, smul_zero, add_zero, hx0], ?_⟩
  rw [map_add, map_smul, D.Pg]
  show Φ₂ x0 + (s : K) * (γ : K) = k
  rw [hs']
  have hγ : ((γ⁻¹ : Kˣ) : K) * (γ : K) = 1 := by simp
  linear_combination (k - Φ₂ x0) * hγ

def iso_liftFun (D₂ : iso_Dat R M₂ C₂ γ Φ₂ π₂ g₂ lam₂) (D₁ : iso_Dat R M₁ C₁ γ Φ₁ π₁ g₁ lam₁)
    (φ : C₁ →ₗ[R] C₂) (hφ : ∀ y, lam₂ (φ y) = lam₁ y) (x : M₁) : M₂ :=
  Classical.choose (iso_ex D₂ (φ (π₁ x)) (Φ₁ x) (by rw [hφ, D₁.lam_pi]))

theorem iso_liftFun_spec (D₂ : iso_Dat R M₂ C₂ γ Φ₂ π₂ g₂ lam₂)
    (D₁ : iso_Dat R M₁ C₁ γ Φ₁ π₁ g₁ lam₁)
    (φ : C₁ →ₗ[R] C₂) (hφ : ∀ y, lam₂ (φ y) = lam₁ y) (x : M₁) :
    π₂ (iso_liftFun D₂ D₁ φ hφ x) = φ (π₁ x) ∧ Φ₂ (iso_liftFun D₂ D₁ φ hφ x) = Φ₁ x := by
  unfold iso_liftFun
  exact Classical.choose_spec (iso_ex D₂ (φ (π₁ x)) (Φ₁ x) (by rw [hφ, D₁.lam_pi]))

def iso_lift (D₂ : iso_Dat R M₂ C₂ γ Φ₂ π₂ g₂ lam₂) (D₁ : iso_Dat R M₁ C₁ γ Φ₁ π₁ g₁ lam₁)
    (φ : C₁ →ₗ[R] C₂) (hφ : ∀ y, lam₂ (φ y) = lam₁ y) : M₁ →ₗ[R] M₂ where
  toFun := iso_liftFun D₂ D₁ φ hφ
  map_add' x y := by
    apply iso_uniq D₂
    · rw [map_add, (iso_liftFun_spec D₂ D₁ φ hφ _).1, (iso_liftFun_spec D₂ D₁ φ hφ _).1,
        (iso_liftFun_spec D₂ D₁ φ hφ _).1, map_add, map_add]
    · rw [map_add, (iso_liftFun_spec D₂ D₁ φ hφ _).2, (iso_liftFun_spec D₂ D₁ φ hφ _).2,
        (iso_liftFun_spec D₂ D₁ φ hφ _).2, map_add]
  map_smul' r x := by
    apply iso_uniq D₂
    · rw [RingHom.id_apply, map_smul, (iso_liftFun_spec D₂ D₁ φ hφ _).1,
        (iso_liftFun_spec D₂ D₁ φ hφ _).1, map_smul, map_smul]
    · rw [RingHom.id_apply, map_smul, (iso_liftFun_spec D₂ D₁ φ hφ _).2,
        (iso_liftFun_spec D₂ D₁ φ hφ _).2, map_smul]

theorem iso_lift_spec (D₂ : iso_Dat R M₂ C₂ γ Φ₂ π₂ g₂ lam₂)
    (D₁ : iso_Dat R M₁ C₁ γ Φ₁ π₁ g₁ lam₁)
    (φ : C₁ →ₗ[R] C₂) (hφ : ∀ y, lam₂ (φ y) = lam₁ y) (x : M₁) :
    π₂ (iso_lift D₂ D₁ φ hφ x) = φ (π₁ x) ∧ Φ₂ (iso_lift D₂ D₁ φ hφ x) = Φ₁ x := by
  exact iso_liftFun_spec D₂ D₁ φ hφ x

theorem iso_symm_lam (φ : C₁ ≃ₗ[R] C₂) (hφ : ∀ y, lam₂ (φ y) = lam₁ y) (y : C₂) :
    lam₁ ((φ.symm : C₂ →ₗ[R] C₁) y) = lam₂ y := by
  rw [← hφ]
  simp

def iso_liftE (D₂ : iso_Dat R M₂ C₂ γ Φ₂ π₂ g₂ lam₂) (D₁ : iso_Dat R M₁ C₁ γ Φ₁ π₁ g₁ lam₁)
    (φ : C₁ ≃ₗ[R] C₂) (hφ : ∀ y, lam₂ (φ y) = lam₁ y) : M₁ ≃ₗ[R] M₂ :=
  LinearEquiv.ofLinearMap (iso_lift D₂ D₁ (φ : C₁ →ₗ[R] C₂) hφ)
    (iso_lift D₁ D₂ (φ.symm : C₂ →ₗ[R] C₁) (iso_symm_lam φ hφ))
    (by
      ext x
      apply iso_uniq D₂
      · simp only [LinearMap.comp_apply, LinearMap.id_apply]
        rw [(iso_lift_spec D₂ D₁ _ _ _).1, (iso_lift_spec D₁ D₂ _ _ _).1]
        simp
      · simp only [LinearMap.comp_apply, LinearMap.id_apply]
        rw [(iso_lift_spec D₂ D₁ _ _ _).2, (iso_lift_spec D₁ D₂ _ _ _).2])
    (by
      ext x
      apply iso_uniq D₁
      · simp only [LinearMap.comp_apply, LinearMap.id_apply]
        rw [(iso_lift_spec D₁ D₂ _ _ _).1, (iso_lift_spec D₂ D₁ _ _ _).1]
        simp
      · simp only [LinearMap.comp_apply, LinearMap.id_apply]
        rw [(iso_lift_spec D₁ D₂ _ _ _).2, (iso_lift_spec D₂ D₁ _ _ _).2])

theorem iso_liftE_spec (D₂ : iso_Dat R M₂ C₂ γ Φ₂ π₂ g₂ lam₂)
    (D₁ : iso_Dat R M₁ C₁ γ Φ₁ π₁ g₁ lam₁)
    (φ : C₁ ≃ₗ[R] C₂) (hφ : ∀ y, lam₂ (φ y) = lam₁ y) (x : M₁) :
    π₂ (iso_liftE D₂ D₁ φ hφ x) = φ (π₁ x) ∧ Φ₂ (iso_liftE D₂ D₁ φ hφ x) = Φ₁ x := by
  exact iso_lift_spec D₂ D₁ (φ : C₁ →ₗ[R] C₂) hφ x

theorem iso_down (D₂ : iso_Dat R M₂ C₂ γ Φ₂ π₂ g₂ lam₂) (D₁ : iso_Dat R M₁ C₁ γ Φ₁ π₁ g₁ lam₁)
    (Ψ : M₁ ≃ₗ[R] M₂) (hg : Ψ g₁ = g₂) : ∃ φ : C₁ ≃ₗ[R] C₂, ∀ x, φ (π₁ x) = π₂ (Ψ x) := by
  have hker1 : ∀ x, π₁ x = 0 → π₂ (Ψ x) = 0 := by
    intro x hx
    obtain ⟨r, rfl⟩ := D₁.ker x hx
    rw [map_smul, hg, map_smul, D₂.pg, smul_zero]
  have hker2 : ∀ y, π₂ y = 0 → π₁ (Ψ.symm y) = 0 := by
    intro y hy
    obtain ⟨r, rfl⟩ := D₂.ker y hy
    rw [map_smul, ← hg, LinearEquiv.symm_apply_apply, map_smul, D₁.pg, smul_zero]
  let e₁ := π₁.quotKerEquivOfSurjective D₁.surj
  let e₂ := π₂.quotKerEquivOfSurjective D₂.surj
  let f : (M₁ ⧸ LinearMap.ker π₁) →ₗ[R] (M₂ ⧸ LinearMap.ker π₂) :=
    (LinearMap.ker π₁).mapQ (LinearMap.ker π₂) Ψ.toLinearMap (fun x hx => by
      simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢
      exact hker1 x hx)
  let g : (M₂ ⧸ LinearMap.ker π₂) →ₗ[R] (M₁ ⧸ LinearMap.ker π₁) :=
    (LinearMap.ker π₂).mapQ (LinearMap.ker π₁) Ψ.symm.toLinearMap (fun y hy => by
      simp only [Submodule.mem_comap, LinearMap.mem_ker] at hy ⊢
      exact hker2 y hy)
  let F : (M₁ ⧸ LinearMap.ker π₁) ≃ₗ[R] (M₂ ⧸ LinearMap.ker π₂) :=
    LinearEquiv.ofLinear f g (by ext y; simp [f, g]) (by ext x; simp [f, g])
  refine ⟨(e₁.symm.trans F).trans e₂, fun x => ?_⟩
  have h1 : e₁.symm (π₁ x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]
    simp [e₁]
  simp only [LinearEquiv.trans_apply]
  rw [h1]
  simp [F, f, e₂]

theorem iso_card (D₂ : iso_Dat R M₂ C₂ γ Φ₂ π₂ g₂ lam₂) (D₁ : iso_Dat R M₁ C₁ γ Φ₁ π₁ g₁ lam₁)
    (f₁ : M₁) (f₂ : M₂) (hf : Φ₁ f₁ = Φ₂ f₂) :
    Nat.card {φ : C₁ ≃ₗ[R] C₂ // (∀ y, lam₂ (φ y) = lam₁ y) ∧ φ (π₁ f₁) = π₂ f₂} =
      Nat.card {Ψ : M₁ ≃ₗ[R] M₂ // (∀ x, Φ₂ (Ψ x) = Φ₁ x) ∧ Ψ g₁ = g₂ ∧ Ψ f₁ = f₂} := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun φ => ⟨iso_liftE D₂ D₁ φ.1 φ.2.1, fun x => (iso_liftE_spec D₂ D₁ φ.1 φ.2.1 x).2, ?_, ?_⟩)
    ⟨?_, ?_⟩)
  · apply iso_uniq D₂
    · rw [(iso_liftE_spec D₂ D₁ φ.1 φ.2.1 _).1, D₁.pg, D₂.pg, map_zero]
    · rw [(iso_liftE_spec D₂ D₁ φ.1 φ.2.1 _).2, D₁.Pg, D₂.Pg]
  · apply iso_uniq D₂
    · rw [(iso_liftE_spec D₂ D₁ φ.1 φ.2.1 _).1, φ.2.2]
    · rw [(iso_liftE_spec D₂ D₁ φ.1 φ.2.1 _).2, hf]
  · intro φ φ' h
    apply Subtype.ext
    ext y
    obtain ⟨x, rfl⟩ := D₁.surj y
    have h1 : iso_liftE D₂ D₁ φ.1 φ.2.1 = iso_liftE D₂ D₁ φ'.1 φ'.2.1 := congrArg Subtype.val h
    rw [← (iso_liftE_spec D₂ D₁ φ.1 φ.2.1 x).1, ← (iso_liftE_spec D₂ D₁ φ'.1 φ'.2.1 x).1, h1]
  · rintro ⟨Ψ, hΨ, hg, hff⟩
    obtain ⟨φ, hφ⟩ := iso_down D₂ D₁ Ψ hg
    have hl : ∀ y, lam₂ (φ y) = lam₁ y := by
      intro y
      obtain ⟨x, rfl⟩ := D₁.surj y
      rw [hφ, D₂.lam_pi, D₁.lam_pi, hΨ]
    refine ⟨⟨φ, hl, by rw [hφ, hff]⟩, ?_⟩
    apply Subtype.ext
    ext x
    apply iso_uniq D₂
    · rw [(iso_liftE_spec D₂ D₁ φ hl x).1, hφ]
    · rw [(iso_liftE_spec D₂ D₁ φ hl x).2, hΨ]

end IsoAbs

section IsoBlk
variable {K : Type} [CommRing K] {m N : ℕ} (hN : N = m + 1)

def iso_vec {X : Type} (a : Fin m → X) (r : X) : Fin N → X :=
  fun x => Sum.elim a (fun _ => r) ((eN hN).symm x)

theorem iso_vec_inl {X : Type} (a : Fin m → X) (r : X) (i : Fin m) :
    iso_vec hN a r (eN hN (Sum.inl i)) = a i := by
  simp [iso_vec]

theorem iso_vec_inr {X : Type} (a : Fin m → X) (r : X) (u : Unit) :
    iso_vec hN a r (eN hN (Sum.inr u)) = r := by
  simp [iso_vec]

theorem iso_vec_eta {X : Type} (x : Fin N → X) :
    iso_vec hN (fun i => x (eN hN (Sum.inl i))) (x (eN hN (Sum.inr ()))) = x := by
  funext z
  obtain ⟨w, rfl⟩ := (eN hN).surjective z
  rcases w with i | ⟨⟩
  · exact iso_vec_inl hN _ _ i
  · exact iso_vec_inr hN _ _ ()

theorem iso_vec_ext {X : Type} {x y : Fin N → X}
    (h1 : ∀ i, x (eN hN (Sum.inl i)) = y (eN hN (Sum.inl i)))
    (h2 : x (eN hN (Sum.inr ())) = y (eN hN (Sum.inr ()))) : x = y := by
  funext z
  obtain ⟨w, rfl⟩ := (eN hN).surjective z
  rcases w with i | ⟨⟩
  · exact h1 i
  · exact h2

theorem iso_blkM_mulVec (A : Matrix (Fin m) (Fin m) K) (b a : Fin m → K) (d : K)
    (y : Fin m → K) (s : K) :
    blkM hN A b a d *ᵥ iso_vec hN y s = iso_vec hN (A *ᵥ y + s • b) (a ⬝ᵥ y + d * s) := by
  apply iso_vec_ext hN
  · intro i
    rw [iso_vec_inl]
    simp only [mulVec, dotProduct]
    rw [← (eN hN).sum_comp, Fintype.sum_sum_type]
    simp [blkM_ll, blkM_lr, iso_vec_inl, iso_vec_inr, mulVec, dotProduct, mul_comm]
  · rw [iso_vec_inr]
    simp only [mulVec, dotProduct]
    rw [← (eN hN).sum_comp, Fintype.sum_sum_type]
    simp [blkM_rl, blkM_rr, iso_vec_inl, iso_vec_inr, dotProduct]

theorem iso_bigZ_mul_inv (Z : Matrix (Fin m) (Fin m) K) (hZ : IsUnit Z.det) (ξ η : Fin m → K)
    (c : Kˣ) : bigZ hN Z ξ η (c : K) *
      blkM hN (Z⁻¹ + vecMulVec η (((c⁻¹ : Kˣ) : K) • ξ)) (-(((c⁻¹ : Kˣ) : K) • η))
        (-(((c⁻¹ : Kˣ) : K) • ξ)) ((c⁻¹ : Kˣ) : K) = 1 := by
  set ci : K := ((c⁻¹ : Kˣ) : K) with hci
  have hZi : Z * Z⁻¹ = 1 := Matrix.mul_nonsing_inv Z hZ
  have hZi' : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z hZ
  have hc : (c : K) * ci = 1 := by simp [hci]
  have hmv : ∀ w : Fin m → K, Z * vecMulVec η w = vecMulVec (Z *ᵥ η) w := by
    intro w
    ext i j
    simp [vecMulVec, Matrix.mul_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  have hv : ∀ (x w : Fin m → K), x ᵥ* vecMulVec η w = (x ⬝ᵥ η) • w := by
    intro x w
    funext j
    simp [vecMul, vecMulVec, dotProduct, Finset.sum_mul, mul_assoc]
  suffices H : (Z * (Z⁻¹ + vecMulVec η (ci • ξ)) + vecMulVec (Z *ᵥ η) (-(ci • ξ)) = 1) ∧
      (Z *ᵥ -(ci • η) + ci • (Z *ᵥ η) = 0) ∧
      ((ξ ᵥ* Z) ᵥ* (Z⁻¹ + vecMulVec η (ci • ξ)) + (ξ ⬝ᵥ (Z *ᵥ η) + (c : K)) • -(ci • ξ) = 0) ∧
      ((ξ ᵥ* Z) ⬝ᵥ -(ci • η) + (ξ ⬝ᵥ (Z *ᵥ η) + (c : K)) * ci = 1) by
    unfold bigZ
    rw [blkM_mul, H.1, H.2.1, H.2.2.1, H.2.2.2, blkM_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_add, hZi, hmv, add_assoc]
    have h0 : vecMulVec (Z *ᵥ η) (ci • ξ) + vecMulVec (Z *ᵥ η) (-(ci • ξ)) = 0 := by
      ext i j
      simp [vecMulVec]
    rw [h0, add_zero]
  · rw [Matrix.mulVec_neg, Matrix.mulVec_smul]
    simp
  · rw [Matrix.vecMul_add, Matrix.vecMul_vecMul, hZi, Matrix.vecMul_one, hv, ← Matrix.dotProduct_mulVec]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply]
    linear_combination (-(ξ j)) * hc
  · rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_neg, Matrix.mulVec_smul, dotProduct_neg, dotProduct_smul,
      smul_eq_mul]
    linear_combination hc

theorem iso_bigZ_inv (Z : Matrix (Fin m) (Fin m) K) (hZ : IsUnit Z.det) (ξ η : Fin m → K)
    (c : Kˣ) : (bigZ hN Z ξ η (c : K))⁻¹ =
      blkM hN (Z⁻¹ + vecMulVec η (((c⁻¹ : Kˣ) : K) • ξ)) (-(((c⁻¹ : Kˣ) : K) • η))
        (-(((c⁻¹ : Kˣ) : K) • ξ)) ((c⁻¹ : Kˣ) : K) := by
  exact Matrix.inv_eq_right_inv (iso_bigZ_mul_inv hN Z hZ ξ η c)

theorem iso_bigZ_det (Z : Matrix (Fin m) (Fin m) K) (hZ : IsUnit Z.det) (ξ η : Fin m → K)
    (c : Kˣ) : IsUnit (bigZ hN Z ξ η (c : K)).det := by
  exact Matrix.isUnit_det_of_right_inverse (iso_bigZ_mul_inv hN Z hZ ξ η c)

theorem iso_last_sum (w : Fin N → K) :
    (∑ j : Fin N, if j.val + 1 = N then w j else 0) = w (eN hN (Sum.inr ())) := by
  rw [← (eN hN).sum_comp, Fintype.sum_sum_type]
  have h1 : ∀ i : Fin m, ¬ ((eN hN (Sum.inl i) : Fin N) : ℕ) + 1 = N := by
    intro i
    have := i.isLt
    rw [eN_inl]
    omega
  have h2 : ((eN hN (Sum.inr ()) : Fin N) : ℕ) + 1 = N := by
    rw [eN_inr]
    omega
  simp [h1, h2]

end IsoBlk

section IsoConc
variable {K : Type} [CommRing K] (R : Subring K) {m N : ℕ} (hN : N = m + 1)

theorem iso_coeLin_vec (a : Fin m → R) (r : R) :
    coeLin R (iso_vec hN a r) = iso_vec hN (coeLin R a) (r : K) := by
  funext z
  obtain ⟨w, rfl⟩ := (eN hN).surjective z
  rcases w with i | ⟨⟩ <;> (simp [coeLin, iso_vec_inl, iso_vec_inr]; try rfl)

def iso_top : (Fin N → R) →ₗ[R] (Fin m → R) :=
  LinearMap.funLeft R R (fun i => eN hN (Sum.inl i))

def iso_bot : (Fin N → R) →ₗ[R] R := LinearMap.proj (eN hN (Sum.inr ()))

theorem iso_eta (x : Fin N → R) : iso_vec hN (iso_top R hN x) (iso_bot R hN x) = x := by
  exact iso_vec_eta hN x

theorem iso_top_vec (a : Fin m → R) (r : R) : iso_top R hN (iso_vec hN a r) = a := by
  funext i
  exact iso_vec_inl hN a r i

theorem iso_bot_vec (a : Fin m → R) (r : R) : iso_bot R hN (iso_vec hN a r) = r := by
  exact iso_vec_inr hN a r ()

def iso_dot (ξ : Fin m → K) : (Fin m → R) →ₗ[R] K where
  toFun v := ξ ⬝ᵥ coeLin R v
  map_add' v w := by rw [map_add, dotProduct_add]
  map_smul' r v := by
    rw [map_smul, RingHom.id_apply]
    have : r • coeLin R v = (r : K) • coeLin R v := rfl
    rw [this, dotProduct_smul]; rfl

theorem iso_dot_apply (ξ : Fin m → K) (v : Fin m → R) : iso_dot R ξ v = ξ ⬝ᵥ coeLin R v := rfl

def affineForm (ξ : Fin m → K) : (Fin N → R) →ₗ[R] K :=
  (Algebra.linearMap R K).comp (iso_bot R hN) - (iso_dot R ξ).comp (iso_top R hN)

theorem affine_form_apply (ξ : Fin m → K) (x : Fin N → R) :
    affineForm R hN ξ x = (iso_bot R hN x : K) - ξ ⬝ᵥ coeLin R (iso_top R hN x) := rfl

def iso_rho (Z : Matrix (Fin m) (Fin m) K) (ξ : Fin m → K) : (Fin N → R) →ₗ[R] coker R Z × K :=
  LinearMap.prod ((Submodule.mkQ _).comp (iso_top R hN)) (affineForm R hN ξ)

theorem iso_mem_ker (Z : Matrix (Fin m) (Fin m) K) (ξ : Fin m → K) (x : Fin N → R) :
    x ∈ LinearMap.ker (iso_rho R hN Z ξ) ↔ iso_top R hN x ∈ latZ R Z ∧ affineForm R hN ξ x = 0 := by
  simp [iso_rho, LinearMap.mem_ker, Prod.mk_eq_zero, Submodule.Quotient.mk_eq_zero]

abbrev iso_M (Z : Matrix (Fin m) (Fin m) K) (ξ : Fin m → K) : Type :=
  (Fin N → R) ⧸ LinearMap.ker (iso_rho R hN Z ξ)

def iso_Phi (Z : Matrix (Fin m) (Fin m) K) (ξ : Fin m → K) : iso_M R hN Z ξ →ₗ[R] K :=
  (LinearMap.ker (iso_rho R hN Z ξ)).liftQ (affineForm R hN ξ)
    (fun x hx => ((iso_mem_ker R hN Z ξ x).1 hx).2)

def iso_piS (Z : Matrix (Fin m) (Fin m) K) (ξ : Fin m → K) : iso_M R hN Z ξ →ₗ[R] coker R Z :=
  (LinearMap.ker (iso_rho R hN Z ξ)).liftQ ((Submodule.mkQ _).comp (iso_top R hN))
    (fun x hx => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact ((iso_mem_ker R hN Z ξ x).1 hx).1)

theorem iso_ker_le (Z : Matrix (Fin m) (Fin m) K) (ξ η : Fin m → K) (c : K) :
    LinearMap.ker (iso_rho R hN Z ξ) ≤ LinearMap.ker (Submodule.mkQ (latZ R (bigZ hN Z ξ η c))) := by
  intro x hx
  rw [iso_mem_ker] at hx
  obtain ⟨hlat, hphi⟩ := hx
  rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨u, hu⟩ := hlat
  simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hu
  rw [affine_form_apply, sub_eq_zero] at hphi
  refine ⟨iso_vec hN u 0, ?_⟩
  simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  rw [iso_coeLin_vec, bigZ, iso_blkM_mulVec, ← iso_eta R hN x, iso_coeLin_vec, hphi,
    ← hu, ← Matrix.dotProduct_mulVec]
  simp

def iso_piB (Z : Matrix (Fin m) (Fin m) K) (ξ η : Fin m → K) (c : K) :
    iso_M R hN Z ξ →ₗ[R] coker R (bigZ hN Z ξ η c) :=
  (LinearMap.ker (iso_rho R hN Z ξ)).liftQ (Submodule.mkQ _) (iso_ker_le R hN Z ξ η c)

theorem iso_eLast : (eLast R : Fin N → R) = iso_vec hN 0 1 := by
  apply iso_vec_ext hN
  · intro i
    rw [iso_vec_inl]
    simp only [eLast]
    rw [if_neg]
    · rfl
    · rw [eN_inl]
      have := i.isLt
      omega
  · rw [iso_vec_inr]
    simp only [eLast]
    rw [if_pos]
    rw [eN_inr]
    omega

end IsoConc

section IsoData
variable {K : Type} [CommRing K] (R : Subring K) {m N : ℕ} (hN : N = m + 1)
  (Z : Matrix (Fin m) (Fin m) K) (hZ : IsUnit Z.det) (ξ η : Fin m → K) (c : Kˣ)

theorem iso_Phi_mk (x : Fin N → R) :
    iso_Phi R hN Z ξ (Submodule.Quotient.mk x) = affineForm R hN ξ x := rfl

theorem iso_piS_mk (x : Fin N → R) :
    iso_piS R hN Z ξ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (iso_top R hN x) := rfl

theorem iso_piB_mk (x : Fin N → R) :
    iso_piB R hN Z ξ η (c : K) (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

theorem affine_form_on_vector (a : Fin m → R) (r : R) :
    affineForm R hN ξ (iso_vec hN a r) = (r : K) - ξ ⬝ᵥ coeLin R a := by
  rw [affine_form_apply, iso_bot_vec, iso_top_vec]

include hZ in
theorem iso_lamLin_big (x : Fin N → R) :
    lamLin R (bigZ hN Z ξ η (c : K)) x =
      Submodule.Quotient.mk (((c⁻¹ : Kˣ) : K) * affineForm R hN ξ x) := by
  rw [Formalism.DoubleCosetMeasures.P.lamLin_apply, Formalism.DoubleCosetMeasures.P.lastCoord_apply, iso_last_sum hN, iso_bigZ_inv hN Z hZ,
    ← iso_eta R hN x, iso_coeLin_vec, iso_blkM_mulVec, iso_vec_inr, affine_form_on_vector,
    Submodule.mkQ_apply]
  congr 1
  rw [neg_dotProduct, smul_dotProduct, smul_eq_mul]
  ring

theorem iso_datB (b : Fin m → R) (hb : coeLin R b = Z *ᵥ η) (s : R)
    (hs : (s : K) = ξ ⬝ᵥ (Z *ᵥ η) + (c : K)) :
    iso_Dat R (iso_M R hN Z ξ) (coker R (bigZ hN Z ξ η (c : K))) c (iso_Phi R hN Z ξ)
      (iso_piB R hN Z ξ η (c : K)) (Submodule.Quotient.mk (iso_vec hN b s))
      (A5x6.muZ R (bigZ hN Z ξ η (c : K)) (iso_bigZ_det hN Z hZ ξ η c)) where
  surj y := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  ker x hx := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [iso_piB_mk, Submodule.Quotient.mk_eq_zero, Formalism.DoubleCosetMeasures.P.mem_latZ] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨iso_bot R hN y, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, iso_mem_ker]
    rw [← iso_eta R hN y, iso_coeLin_vec, bigZ, iso_blkM_mulVec, ← iso_eta R hN x,
      iso_coeLin_vec] at hy
    have h1 : Z *ᵥ coeLin R (iso_top R hN y) + (iso_bot R hN y : K) • Z *ᵥ η =
        coeLin R (iso_top R hN x) := by
      funext i
      have := congrFun hy (eN hN (Sum.inl i))
      rwa [iso_vec_inl, iso_vec_inl] at this
    have h2 : ξ ᵥ* Z ⬝ᵥ coeLin R (iso_top R hN y) +
        (ξ ⬝ᵥ Z *ᵥ η + (c : K)) * (iso_bot R hN y : K) = (iso_bot R hN x : K) := by
      have := congrFun hy (eN hN (Sum.inr ()))
      rwa [iso_vec_inr, iso_vec_inr] at this
    have h3 : coeLin R (iso_top R hN (x - iso_bot R hN y • iso_vec hN b s)) =
        Z *ᵥ coeLin R (iso_top R hN y) := by
      rw [map_sub, map_sub, map_smul, map_smul, iso_top_vec, hb, ← h1]
      have : iso_bot R hN y • Z *ᵥ η = (iso_bot R hN y : K) • Z *ᵥ η := rfl
      rw [this]; abel
    refine ⟨(Formalism.DoubleCosetMeasures.P.mem_latZ R Z _).2 ⟨_, h3.symm⟩, ?_⟩
    rw [affine_form_apply, h3, map_sub, map_smul, iso_bot_vec, ← Matrix.dotProduct_mulVec] at *
    push_cast
    rw [← h2]
    simp only [smul_eq_mul, Subring.coe_mul, hs]
    ring
  pg := by
    rw [iso_piB_mk, Submodule.Quotient.mk_eq_zero, Formalism.DoubleCosetMeasures.P.mem_latZ]
    refine ⟨iso_vec hN 0 1, ?_⟩
    rw [iso_coeLin_vec, iso_coeLin_vec, bigZ, iso_blkM_mulVec, hb, hs]
    simp
  Pg := by
    rw [iso_Phi_mk, affine_form_on_vector, hs, hb]; ring
  lam_pi x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [iso_piB_mk, A5x6.muZ_mk, iso_lamLin_big R hN Z hZ, iso_Phi_mk]

theorem iso_datS (hξ : ∀ j, (ξ ᵥ* Z) j ∈ R) (α : coker R Z →ₗ[R] KR R)
    (hα : ∀ v, α (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ξ ⬝ᵥ coeLin R v)) :
    iso_Dat R (iso_M R hN Z ξ) (coker R Z) 1 (iso_Phi R hN Z ξ)
      (iso_piS R hN Z ξ) (Submodule.Quotient.mk (iso_vec hN 0 1)) (-α) where
  surj y := by
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk (iso_vec hN a 0), by rw [iso_piS_mk, iso_top_vec]⟩
  ker x hx := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [iso_piS_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨a, ha⟩ := (Formalism.DoubleCosetMeasures.P.mem_latZ R Z _).1 hx
    have hmem : ξ ᵥ* Z ⬝ᵥ coeLin R a ∈ R := by
      refine R.sum_mem fun j _ => R.mul_mem (hξ j) ?_
      rw [Formalism.DoubleCosetMeasures.P.coeLin_apply]; exact (a j).2
    refine ⟨iso_bot R hN x - ⟨_, hmem⟩, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, iso_mem_ker]
    have h3 : iso_top R hN (x - (iso_bot R hN x - ⟨_, hmem⟩) • iso_vec hN 0 1) =
        iso_top R hN x := by
      rw [map_sub, map_smul, iso_top_vec, smul_zero, sub_zero]
    refine ⟨by rw [h3]; exact hx, ?_⟩
    rw [affine_form_apply, h3, map_sub, map_smul, iso_bot_vec, ← ha, Matrix.dotProduct_mulVec]
    simp
  pg := by
    rw [iso_piS_mk, iso_top_vec]; rfl
  Pg := by
    rw [iso_Phi_mk, affine_form_on_vector]; simp
  lam_pi x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [iso_piS_mk, LinearMap.neg_apply, hα, iso_Phi_mk, affine_form_apply, ← Submodule.Quotient.mk_neg,
      Submodule.Quotient.eq]
    refine ⟨-iso_bot R hN x, ?_⟩
    have h0 : (algebraMap R K) (iso_bot R hN x) = (iso_bot R hN x : K) := rfl
    simp only [map_neg, Algebra.linearMap_apply, h0, inv_one, Units.val_one, one_mul]
    ring

end IsoData

theorem card_iso_big {K : Type} [CommRing K] (R : Subring K)
    {m m' N N' : ℕ} (hN : N = m + 1) (hN' : N' = m' + 1)
    (Z₁ : Matrix (Fin m) (Fin m) K) (Z₂ : Matrix (Fin m') (Fin m') K)
    (hZ₁ : IsUnit Z₁.det) (hZ₂ : IsUnit Z₂.det) (ξ₁ η₁ : Fin m → K) (ξ₂ η₂ : Fin m' → K) (c : Kˣ)
    (hi₁ : IsInt R (bigZ hN Z₁ ξ₁ η₁ (c : K))) (hi₂ : IsInt R (bigZ hN' Z₂ ξ₂ η₂ (c : K)))
    (α₁ : coker R Z₁ →ₗ[R] KR R) (α₂ : coker R Z₂ →ₗ[R] KR R)
    (hα₁ : ∀ v, α₁ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ξ₁ ⬝ᵥ coeLin R v))
    (hα₂ : ∀ v, α₂ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ξ₂ ⬝ᵥ coeLin R v))
    (b₁ : Fin m → R) (b₂ : Fin m' → R) (hb₁ : coeLin R b₁ = Z₁ *ᵥ η₁)
    (hb₂ : coeLin R b₂ = Z₂ *ᵥ η₂) :
    Nat.card (isoZZ R (bigZ hN Z₁ ξ₁ η₁ (c : K)) (bigZ hN' Z₂ ξ₂ η₂ (c : K))) =
      Nat.card {θ : coker R Z₁ ≃ₗ[R] coker R Z₂ // (∀ y, α₂ (θ y) = α₁ y) ∧
        θ (Submodule.Quotient.mk b₁) = Submodule.Quotient.mk b₂} := by
  obtain ⟨-, -, hξ₁, hs₁⟩ := (blkM_isInt R hN _ _ _ _).1 hi₁
  obtain ⟨-, -, hξ₂, hs₂⟩ := (blkM_isInt R hN' _ _ _ _).1 hi₂
  have DB₁ := iso_datB R hN Z₁ hZ₁ ξ₁ η₁ c b₁ hb₁ ⟨_, hs₁⟩ rfl
  have DB₂ := iso_datB R hN' Z₂ hZ₂ ξ₂ η₂ c b₂ hb₂ ⟨_, hs₂⟩ rfl
  have DS₁ := iso_datS R hN Z₁ ξ₁ hξ₁ α₁ hα₁
  have DS₂ := iso_datS R hN' Z₂ ξ₂ hξ₂ α₂ hα₂
  have e1 := iso_card DB₂ DB₁ (Submodule.Quotient.mk (iso_vec hN 0 1))
    (Submodule.Quotient.mk (iso_vec hN' 0 1)) (by rw [DS₁.Pg, DS₂.Pg])
  have e2 := iso_card DS₂ DS₁ (Submodule.Quotient.mk (iso_vec hN b₁ ⟨_, hs₁⟩))
    (Submodule.Quotient.mk (iso_vec hN' b₂ ⟨_, hs₂⟩)) (by rw [DB₁.Pg, DB₂.Pg])
  have l1 : Nat.card (isoZZ R (bigZ hN Z₁ ξ₁ η₁ (c : K)) (bigZ hN' Z₂ ξ₂ η₂ (c : K))) =
      Nat.card {φ : coker R (bigZ hN Z₁ ξ₁ η₁ (c : K)) ≃ₗ[R] coker R (bigZ hN' Z₂ ξ₂ η₂ (c : K)) //
        (∀ y, A5x6.muZ R (bigZ hN' Z₂ ξ₂ η₂ (c : K)) (iso_bigZ_det hN' Z₂ hZ₂ ξ₂ η₂ c) (φ y) =
          A5x6.muZ R (bigZ hN Z₁ ξ₁ η₁ (c : K)) (iso_bigZ_det hN Z₁ hZ₁ ξ₁ η₁ c) y) ∧
        φ (iso_piB R hN Z₁ ξ₁ η₁ (c : K) (Submodule.Quotient.mk (iso_vec hN 0 1))) =
          iso_piB R hN' Z₂ ξ₂ η₂ (c : K) (Submodule.Quotient.mk (iso_vec hN' 0 1))} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun φ => ?_)
    rw [iso_piB_mk, iso_piB_mk, ← iso_eLast, ← iso_eLast]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun y => ?_, h1⟩
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨v', hv'⟩ := Submodule.Quotient.mk_surjective _ (φ (Submodule.Quotient.mk v))
      rw [← hv', A5x6.muZ_mk, A5x6.muZ_mk]
      exact h2 v v' hv'.symm
    · rintro ⟨h1, h2⟩
      refine ⟨h2, fun v v' hv => ?_⟩
      have := h1 (Submodule.Quotient.mk v)
      rwa [hv, A5x6.muZ_mk, A5x6.muZ_mk] at this
  have l2 : Nat.card {θ : coker R Z₁ ≃ₗ[R] coker R Z₂ // (∀ y, α₂ (θ y) = α₁ y) ∧
        θ (Submodule.Quotient.mk b₁) = Submodule.Quotient.mk b₂} =
      Nat.card {θ : coker R Z₁ ≃ₗ[R] coker R Z₂ // (∀ y, (-α₂) (θ y) = (-α₁) y) ∧
        θ (iso_piS R hN Z₁ ξ₁ (Submodule.Quotient.mk (iso_vec hN b₁ ⟨_, hs₁⟩))) =
          iso_piS R hN' Z₂ ξ₂ (Submodule.Quotient.mk (iso_vec hN' b₂ ⟨_, hs₂⟩))} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun θ => ?_)
    rw [iso_piS_mk, iso_piS_mk, iso_top_vec, iso_top_vec]
    simp only [LinearMap.neg_apply, neg_inj]
  rw [l1, l2, e1, e2]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun Ψ => ?_)
  tauto

end IsoPart

section Dual
variable {K : Type} [CommRing K] (R : Subring K) {m : ℕ}

open Formalism.DoubleCosetMeasures.P Formalism.FourierDecayAlt.P.A5x3 in
theorem mk_outV (x : Fin m → KR R) (j : Fin m) :
    (Submodule.Quotient.mk (outV R x j) : KR R) = x j := by
  exact Quotient.out_eq (x j)

def iA (Z : Matrix (Fin m) (Fin m) K) (α : coker R Z →ₗ[R] KR R) : Fin m → KR R :=
  fun j => α (Submodule.Quotient.mk (Pi.single j 1))

def iC (Z : Matrix (Fin m) (Fin m) K) (β : coker R Z) : Fin m → KR R :=
  fun j => A5x3.rowFun R Z j (Quotient.out β)

theorem iA_spec (Z : Matrix (Fin m) (Fin m) K) (α : coker R Z →ₗ[R] KR R) (v : Fin m → R) :
    α (Submodule.Quotient.mk v) = Submodule.Quotient.mk (outV R (iA R Z α) ⬝ᵥ coeLin R v) := by
  have key : α.comp (Submodule.mkQ _) =
      (Submodule.mkQ _).comp (iso_dot R (outV R (iA R Z α))) := by
    ext j
    have hc : coeLin R (Pi.single j (1 : R)) = Pi.single j (1 : K) := by
      funext k
      by_cases hk : k = j
      · subst hk
        simp [coeLin]
      · simp [coeLin, Pi.single_apply, hk]
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, iso_dot_apply, LinearMap.single_apply]
    rw [hc, dotProduct_single, mul_one, mk_outV]
    rfl
  have h := LinearMap.congr_fun key v
  simpa [iso_dot_apply] using h

theorem iA_injective (Z : Matrix (Fin m) (Fin m) K) : Function.Injective (iA R Z) := by
  intro α β h
  apply Submodule.linearMap_qext
  ext j
  simpa [iA] using congrFun h j

theorem iC_spec (Z : Matrix (Fin m) (Fin m) K) (hZ : IsInt R Z) (hd : IsUnit Z.det)
    (β : coker R Z) : ∃ b : Fin m → R, coeLin R b = Z *ᵥ outV R (iC R Z β) ∧
      Submodule.Quotient.mk b = β := by
  have h1 : ∀ j, outV R (iC R Z β) j - (Z⁻¹ *ᵥ coeLin R (Quotient.out β)) j ∈ R := by
    intro j
    rw [← A5x3.mk_eq_mk, mk_outV]
    rfl
  let r : Fin m → R := fun j => ⟨_, h1 j⟩
  have hr : outV R (iC R Z β) = Z⁻¹ *ᵥ coeLin R (Quotient.out β) + coeLin R r := by
    funext j
    rw [Pi.add_apply, P.coeLin_apply]
    simp [r]
  have h2 : Z *ᵥ outV R (iC R Z β) = coeLin R (Quotient.out β) + Z *ᵥ coeLin R r := by
    rw [hr, mulVec_add, mulVec_mulVec, Matrix.mul_nonsing_inv Z hd, one_mulVec]
  have h3 : Z *ᵥ coeLin R r = coeLin R (P.liftR R Z hZ *ᵥ r) := by
    rw [P.coeLin_mulVec, P.liftR_map]
  refine ⟨Quotient.out β + P.liftR R Z hZ *ᵥ r, ?_, ?_⟩
  · rw [map_add, h2, h3]
  · rw [Submodule.Quotient.mk_add]
    have h4 : (Submodule.Quotient.mk (P.liftR R Z hZ *ᵥ r) : coker R Z) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero, P.mem_latZ]
      exact ⟨r, h3⟩
    rw [h4, add_zero]
    exact Quotient.out_eq β

theorem iC_injective (Z : Matrix (Fin m) (Fin m) K) (hZ : IsInt R Z) (hd : IsUnit Z.det) :
    Function.Injective (iC R Z) := by
  intro β β' h
  obtain ⟨b, hb, rfl⟩ := iC_spec R Z hZ hd β
  obtain ⟨b', hb', rfl⟩ := iC_spec R Z hZ hd β'
  rw [h, ← hb'] at hb
  rw [P.coeLin_injective R hb]

theorem mem_range_iA (Z : Matrix (Fin m) (Fin m) K) (x : Fin m → KR R)
    (hx : ∀ j, (outV R x ᵥ* Z) j ∈ R) : x ∈ Set.range (iA R Z) := by
  let f : (Fin m → R) →ₗ[R] KR R := (Submodule.mkQ _).comp (iso_dot R (outV R x))
  have hker : latZ R Z ≤ LinearMap.ker f := by
    intro v hv
    obtain ⟨u, hu⟩ := hv
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at hu
    have hmem : (outV R x ᵥ* Z) ⬝ᵥ coeLin R u ∈ R := R.sum_mem fun j _ => R.mul_mem (hx j) (u j).2
    rw [LinearMap.mem_ker, LinearMap.comp_apply, iso_dot_apply, ← hu, Matrix.dotProduct_mulVec,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    exact ⟨⟨_, hmem⟩, rfl⟩
  refine ⟨(latZ R Z).liftQ f hker, ?_⟩
  funext j
  have hc : coeLin R (Pi.single j (1 : R)) = Pi.single j (1 : K) := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp [coeLin]
    · simp [coeLin, Pi.single_apply, hk]
  show (latZ R Z).liftQ f hker (Submodule.Quotient.mk (Pi.single j 1)) = x j
  rw [Submodule.liftQ_apply]
  simp only [f, LinearMap.comp_apply, iso_dot_apply, Submodule.mkQ_apply]
  rw [hc, dotProduct_single, mul_one, mk_outV]

theorem mem_range_iC (Z : Matrix (Fin m) (Fin m) K) (hd : IsUnit Z.det) (x : Fin m → KR R)
    (hx : ∀ j, (Z *ᵥ outV R x) j ∈ R) : x ∈ Set.range (iC R Z) := by
  let b : Fin m → R := fun j => ⟨_, hx j⟩
  have hb : coeLin R b = Z *ᵥ outV R x := by
    funext j; rw [P.coeLin_apply]
  refine ⟨Submodule.Quotient.mk b, ?_⟩
  funext j
  have h1 : iC R Z (Submodule.Quotient.mk b) j =
      (latZ R Z).liftQ (A5x3.rowFun R Z j) (A5x3.rowFun_kills R Z hd j)
        (Submodule.Quotient.mk (Quotient.out (Submodule.Quotient.mk b : coker R Z))) := rfl
  have h2 : (Submodule.Quotient.mk (Quotient.out (Submodule.Quotient.mk b : coker R Z)) :
      coker R Z) = Submodule.Quotient.mk b := Quotient.out_eq _
  rw [h1, h2, Submodule.liftQ_apply, A5x3.rowFun_apply, hb, mulVec_mulVec,
    Matrix.nonsing_inv_mul Z hd, one_mulVec, mk_outV]

theorem iA_eZ (Z : Matrix (Fin m) (Fin m) K) (α : coker R Z →ₗ[R] KR R) :
    α (eZ R Z) = Submodule.Quotient.mk (lastE (outV R (iA R Z α))) := by
  rw [eZ, iA_spec]
  congr 1
  unfold lastE dotProduct
  apply Finset.sum_congr rfl
  intro j _
  simp only [coeLin, eLast, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Algebra.linearMap_apply]
  split_ifs <;> simp

theorem iC_mu (Z : Matrix (Fin m) (Fin m) K) (hZ : IsInt R Z) (hd : IsUnit Z.det)
    (β : coker R Z) :
    A5x6.muZ R Z hd β = Submodule.Quotient.mk (lastE (outV R (iC R Z β))) := by
  obtain ⟨b, hb, hβ⟩ := iC_spec R Z hZ hd β
  conv_lhs => rw [← hβ]
  rw [A5x6.muZ_mk, P.lamLin_apply, hb, mulVec_mulVec, Matrix.nonsing_inv_mul Z hd, one_mulVec,
    P.lastCoord_apply]
  rfl

theorem bigZ_int_iff {N : ℕ} (hN : N = m + 1) (Z : Matrix (Fin m) (Fin m) K) (hZ : IsInt R Z)
    (hd : IsUnit Z.det) (α : coker R Z →ₗ[R] KR R) (β : coker R Z) (c : K) :
    IsInt R (bigZ hN Z (outV R (iA R Z α)) (outV R (iC R Z β)) c) ↔
      α β = -(Submodule.Quotient.mk c : KR R) := by
  obtain ⟨b, hb, hβ⟩ := iC_spec R Z hZ hd β
  unfold bigZ
  rw [blkM_isInt]
  have h1 : ∀ i, (Z *ᵥ outV R (iC R Z β)) i ∈ R := by
    intro i; rw [← hb, P.coeLin_apply]; exact (b i).2
  have h2 : ∀ j, (outV R (iA R Z α) ᵥ* Z) j ∈ R := by
    intro j
    have h3 : (Submodule.Quotient.mk (fun i => (⟨Z i j, hZ i j⟩ : R)) : coker R Z) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero, P.mem_latZ]
      refine ⟨Pi.single j 1, ?_⟩
      funext i
      rw [P.coeLin_apply]
      have : coeLin R (Pi.single j 1 : Fin m → R) = Pi.single j 1 := by
        funext k
        rw [P.coeLin_apply]
        by_cases hk : k = j
        · subst hk; simp
        · simp [hk]
      rw [this, mulVec_single_one]
      rfl
    have h4 := iA_spec R Z α (fun i => (⟨Z i j, hZ i j⟩ : R))
    rw [h3, map_zero, eq_comm, A5x3.mk_eq_zero] at h4
    convert h4 using 1
    simp only [vecMul, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [P.coeLin_apply]
  have h5 : α β = Submodule.Quotient.mk (outV R (iA R Z α) ⬝ᵥ Z *ᵥ outV R (iC R Z β)) := by
    rw [← hb, ← iA_spec, hβ]
  rw [h5, eq_neg_iff_add_eq_zero, ← Submodule.Quotient.mk_add, A5x3.mk_eq_zero]
  exact ⟨fun h => h.2.2.2, fun h => ⟨hZ, h1, h2, h⟩⟩

end Dual

section Comb

open Classical in
theorem comb_identity {A₁ C₁ A₂ C₂ Θ : Type} [Fintype A₁] [Fintype C₁] [Fintype A₂] [Fintype C₂]
    [Fintype Θ] (P₁ : A₁ → C₁ → Prop) (P₂ : A₂ → C₂ → Prop) (ta : Θ → A₁ → A₂) (tc : Θ → C₁ → C₂)
    (Q : Θ → A₁ → C₁ → A₂ → C₂ → Prop)
    (hQ : ∀ θ a₁ c₁ a₂ c₂, Q θ a₁ c₁ a₂ c₂ ↔ a₂ = ta θ a₁ ∧ c₂ = tc θ c₁)
    (hP : ∀ θ a c, P₂ (ta θ a) (tc θ c) ↔ P₁ a c) (f₁ : A₁ → C₁ → ℂ) (f₂ : A₂ → C₂ → ℂ) :
    ∑ s : (A₁ × C₁) × (A₂ × C₂), (if P₁ s.1.1 s.1.2 ∧ P₂ s.2.1 s.2.2 then
        (Nat.card {θ // Q θ s.1.1 s.1.2 s.2.1 s.2.2} : ℂ) else 0) * f₁ s.1.1 s.1.2 * f₂ s.2.1 s.2.2 =
      ∑ θ, ∑ a, ∑ c, if P₁ a c then f₁ a c * f₂ (ta θ a) (tc θ c) else 0 := by
  have key : ∀ s : (A₁ × C₁) × (A₂ × C₂), (if P₁ s.1.1 s.1.2 ∧ P₂ s.2.1 s.2.2 then
        (Nat.card {θ // Q θ s.1.1 s.1.2 s.2.1 s.2.2} : ℂ) else 0) * f₁ s.1.1 s.1.2 * f₂ s.2.1 s.2.2 =
      ∑ θ, if s.2 = (ta θ s.1.1, tc θ s.1.2) then
        (if P₁ s.1.1 s.1.2 then f₁ s.1.1 s.1.2 * f₂ (ta θ s.1.1) (tc θ s.1.2) else 0) else 0 := by
    rintro ⟨⟨a₁, c₁⟩, ⟨a₂, c₂⟩⟩
    simp only
    have h1 : ∀ θ, (if (a₂, c₂) = (ta θ a₁, tc θ c₁) then
        (if P₁ a₁ c₁ then f₁ a₁ c₁ * f₂ (ta θ a₁) (tc θ c₁) else 0) else 0) =
        (if P₁ a₁ c₁ ∧ P₂ a₂ c₂ then ((if Q θ a₁ c₁ a₂ c₂ then 1 else 0 : ℕ) : ℂ) else 0) *
          f₁ a₁ c₁ * f₂ a₂ c₂ := by
      intro θ
      by_cases h : a₂ = ta θ a₁ ∧ c₂ = tc θ c₁
      · obtain ⟨rfl, rfl⟩ := h
        have hq : Q θ a₁ c₁ (ta θ a₁) (tc θ c₁) := (hQ _ _ _ _ _).2 ⟨rfl, rfl⟩
        by_cases hp : P₁ a₁ c₁
        · simp [hq, hP, hp]
        · simp [hp]
      · have hq : ¬ Q θ a₁ c₁ a₂ c₂ := fun hq => h ((hQ _ _ _ _ _).1 hq)
        have hne : ¬ (a₂, c₂) = (ta θ a₁, tc θ c₁) := fun he => h (Prod.ext_iff.1 he)
        simp [hq, hne]
    rw [Finset.sum_congr rfl fun θ _ => h1 θ, ← Finset.sum_mul, ← Finset.sum_mul,
      Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
    congr 2
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun s _ => key s, Fintype.sum_prod_type]
  simp only
  have h2 : ∀ x : A₁ × C₁, (∑ y : A₂ × C₂, ∑ θ, if y = (ta θ x.1, tc θ x.2) then
        (if P₁ x.1 x.2 then f₁ x.1 x.2 * f₂ (ta θ x.1) (tc θ x.2) else 0) else 0) =
      ∑ θ, if P₁ x.1 x.2 then f₁ x.1 x.2 * f₂ (ta θ x.1) (tc θ x.2) else 0 := by
    intro x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [Finset.sum_ite_eq']
    simp
  rw [Finset.sum_congr rfl fun x _ => h2 x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [Fintype.sum_prod_type]

end Comb

section Inner

theorem finsum_of_inj {X S : Type} (ι : S → X) (hι : Function.Injective ι) (t : X → ℂ)
    (ht : Function.support t ⊆ Set.range ι) : ∑ᶠ x, t x = ∑ᶠ s, t (ι s) := by
  have h1 : ∑ᶠ x ∈ Set.range ι, t x = ∑ᶠ x, t x := by
    rw [finsum_mem_def, Set.indicator_eq_self.mpr ht]
  have h2 : ∑ᶠ x ∈ Set.range ι, t x = ∑ᶠ s, t (ι s) := finsum_mem_range hι
  rw [← h1, h2]

variable {K : Type} [CommRing K]

open Classical in

def tTerm (R : Subring K) (ψ : AddChar K ℂ) {m m' N N' : ℕ} (hN : N = m + 1) (hN' : N' = m' + 1)
    (Z₁ : Matrix (Fin m) (Fin m) K) (Z₂ : Matrix (Fin m') (Fin m') K) (c : K)
    (y : ((Fin m → KR R) × (Fin m → KR R)) × ((Fin m' → KR R) × (Fin m' → KR R))) : ℂ :=
  (if IsInt R (bigZ hN Z₁ (outV R y.1.1) (outV R y.1.2) c) ∧
      IsInt R (bigZ hN' Z₂ (outV R y.2.1) (outV R y.2.2) c) then
    (Nat.card (isoZZ R (bigZ hN Z₁ (outV R y.1.1) (outV R y.1.2) c)
      (bigZ hN' Z₂ (outV R y.2.1) (outV R y.2.2) c)) : ℂ) else 0) *
    ψ (lastE (outV R y.1.1) + lastE (outV R y.1.2)) *
    conj (ψ (lastE (outV R y.2.1) + lastE (outV R y.2.2)))

open Classical in
theorem tTerm_mk (R : Subring K) (ψ : AddChar K ℂ) {m m' N N' : ℕ} (hN : N = m + 1)
    (hN' : N' = m' + 1) (Z₁ : Matrix (Fin m) (Fin m) K) (Z₂ : Matrix (Fin m') (Fin m') K) (c : K)
    (x y : Fin m → KR R) (x' y' : Fin m' → KR R) :
    tTerm R ψ hN hN' Z₁ Z₂ c ((x, y), (x', y')) =
      (if IsInt R (bigZ hN Z₁ (outV R x) (outV R y) c) ∧
          IsInt R (bigZ hN' Z₂ (outV R x') (outV R y') c) then
        (Nat.card (isoZZ R (bigZ hN Z₁ (outV R x) (outV R y) c)
          (bigZ hN' Z₂ (outV R x') (outV R y') c)) : ℂ) else 0) *
        ψ (lastE (outV R x) + lastE (outV R y)) *
        conj (ψ (lastE (outV R x') + lastE (outV R y'))) := rfl

def iota (R : Subring K) {m m' : ℕ} (Z₁ : Matrix (Fin m) (Fin m) K)
    (Z₂ : Matrix (Fin m') (Fin m') K)
    (s : ((coker R Z₁ →ₗ[R] KR R) × coker R Z₁) × ((coker R Z₂ →ₗ[R] KR R) × coker R Z₂)) :
    ((Fin m → KR R) × (Fin m → KR R)) × ((Fin m' → KR R) × (Fin m' → KR R)) :=
  ((iA R Z₁ s.1.1, iC R Z₁ s.1.2), (iA R Z₂ s.2.1, iC R Z₂ s.2.2))

theorem iota_injective (R : Subring K) {m m' : ℕ} (Z₁ : Matrix (Fin m) (Fin m) K)
    (Z₂ : Matrix (Fin m') (Fin m') K) (h₁ : IsInt R Z₁) (h₂ : IsInt R Z₂) (d₁ : IsUnit Z₁.det)
    (d₂ : IsUnit Z₂.det) : Function.Injective (iota R Z₁ Z₂) := by
  rintro ⟨⟨a, b⟩, ⟨a', b'⟩⟩ ⟨⟨x, y⟩, ⟨x', y'⟩⟩ h
  simp only [iota, Prod.mk.injEq] at h
  obtain ⟨⟨e1, e2⟩, e3, e4⟩ := h
  rw [iA_injective R Z₁ e1, iC_injective R Z₁ h₁ d₁ e2, iA_injective R Z₂ e3,
    iC_injective R Z₂ h₂ d₂ e4]

theorem tTerm_supp (R : Subring K) (ψ : AddChar K ℂ) {m m' N N' : ℕ} (hN : N = m + 1)
    (hN' : N' = m' + 1) (Z₁ : Matrix (Fin m) (Fin m) K) (Z₂ : Matrix (Fin m') (Fin m') K) (c : K)
    (d₁ : IsUnit Z₁.det) (d₂ : IsUnit Z₂.det) :
    Function.support (tTerm R ψ hN hN' Z₁ Z₂ c) ⊆ Set.range (iota R Z₁ Z₂) := by
  rintro ⟨⟨x, y⟩, ⟨x', y'⟩⟩ hy
  by_cases hI : IsInt R (bigZ hN Z₁ (outV R x) (outV R y) c) ∧
      IsInt R (bigZ hN' Z₂ (outV R x') (outV R y') c)
  · obtain ⟨hI1, hI2⟩ := hI
    unfold bigZ at hI1 hI2
    rw [blkM_isInt] at hI1 hI2
    obtain ⟨a, rfl⟩ := mem_range_iA R Z₁ x hI1.2.2.1
    obtain ⟨b, rfl⟩ := mem_range_iC R Z₁ d₁ y hI1.2.1
    obtain ⟨a', rfl⟩ := mem_range_iA R Z₂ x' hI2.2.2.1
    obtain ⟨b', rfl⟩ := mem_range_iC R Z₂ d₂ y' hI2.2.1
    exact ⟨((a, b), (a', b')), rfl⟩
  · exfalso
    apply hy
    rw [tTerm_mk, if_neg hI]
    simp

open Classical in
theorem tTerm_iota (R : Subring K) (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) {m m' N N' : ℕ}
    (hN : N = m + 1) (hN' : N' = m' + 1) (Z₁ : Matrix (Fin m) (Fin m) K)
    (Z₂ : Matrix (Fin m') (Fin m') K) (c : Kˣ) (h₁ : IsInt R Z₁) (h₂ : IsInt R Z₂)
    (d₁ : IsUnit Z₁.det) (d₂ : IsUnit Z₂.det)
    (s : ((coker R Z₁ →ₗ[R] KR R) × coker R Z₁) × ((coker R Z₂ →ₗ[R] KR R) × coker R Z₂)) :
    tTerm R ψ hN hN' Z₁ Z₂ (c : K) (iota R Z₁ Z₂ s) =
      (if s.1.1 s.1.2 = -(Submodule.Quotient.mk (c : K) : KR R) ∧
          s.2.1 s.2.2 = -(Submodule.Quotient.mk (c : K) : KR R) then
        (Nat.card {θ : coker R Z₁ ≃ₗ[R] coker R Z₂ //
          (∀ y, s.2.1 (θ y) = s.1.1 y) ∧ θ s.1.2 = s.2.2} : ℂ) else 0) *
      psiKR R ψ (s.1.1 (eZ R Z₁) + A5x6.muZ R Z₁ d₁ s.1.2) *
      conj (psiKR R ψ (s.2.1 (eZ R Z₂) + A5x6.muZ R Z₂ d₂ s.2.2)) := by
  obtain ⟨⟨a, b⟩, ⟨a', b'⟩⟩ := s
  rw [show iota R Z₁ Z₂ ((a, b), (a', b')) =
    ((iA R Z₁ a, iC R Z₁ b), (iA R Z₂ a', iC R Z₂ b')) from rfl, tTerm_mk]
  simp only
  rw [iA_eZ, iA_eZ, iC_mu R Z₁ h₁ d₁, iC_mu R Z₂ h₂ d₂, ← Submodule.Quotient.mk_add,
    ← Submodule.Quotient.mk_add, A5x6.psiKR_mk R ψ hψ, A5x6.psiKR_mk R ψ hψ]
  congr 2
  by_cases hI : a b = -(Submodule.Quotient.mk (c : K) : KR R) ∧
      a' b' = -(Submodule.Quotient.mk (c : K) : KR R)
  · have hI1 := (bigZ_int_iff R hN Z₁ h₁ d₁ a b (c : K)).2 hI.1
    have hI2 := (bigZ_int_iff R hN' Z₂ h₂ d₂ a' b' (c : K)).2 hI.2
    rw [if_pos hI, if_pos ⟨hI1, hI2⟩]
    obtain ⟨v, hv, hb⟩ := iC_spec R Z₁ h₁ d₁ b
    obtain ⟨v', hv', hb'⟩ := iC_spec R Z₂ h₂ d₂ b'
    rw [card_iso_big R hN hN' Z₁ Z₂ d₁ d₂ _ _ _ _ c hI1 hI2 a a' (iA_spec R Z₁ a)
      (iA_spec R Z₂ a') v v' hv hv', hb, hb']
  · rw [if_neg hI, if_neg]
    rintro ⟨hI1, hI2⟩
    exact hI ⟨(bigZ_int_iff R hN Z₁ h₁ d₁ a b (c : K)).1 hI1,
      (bigZ_int_iff R hN' Z₂ h₂ d₂ a' b' (c : K)).1 hI2⟩

end Inner

section InnerSum
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem psiKR_conj (R : Subring K) (ψ : AddChar K ℂ) (hD : LocalDatum K R ψ) (x : KR R) :
    conj (psiKR R ψ x) = psiKR R ψ (-x) := by
  unfold psiKR
  rw [hD.unitary]
  have e1 : (Submodule.Quotient.mk (Quotient.out (-x)) : KR R) = -x := Quotient.out_eq _
  have e2 : (Submodule.Quotient.mk (Quotient.out x) : KR R) = x := Quotient.out_eq _
  have hx : (Submodule.Quotient.mk (Quotient.out (-x)) : KR R) = Submodule.Quotient.mk (-Quotient.out x) := by
    rw [Submodule.Quotient.mk_neg, e1, e2]
  rw [Submodule.Quotient.eq, LinearMap.mem_range] at hx
  obtain ⟨r, hr⟩ := hx
  have hr' : (r : K) = Quotient.out (-x) - -Quotient.out x := hr
  have hr1 : ψ (r : K) = 1 := by
    have := (hD.selfDual (r : K)).2 r.2 1 R.one_mem
    simpa using this
  have h3 : Quotient.out (-x) = -Quotient.out x + (r : K) := by rw [hr']; ring
  rw [h3, AddChar.map_add_eq_mul, hr1, mul_one]

theorem inner_sum (R : Subring K) (ψ : AddChar K ℂ) (hD : LocalDatum K R ψ) {m m' N N' : ℕ}
    (hN : N = m + 1) (hN' : N' = m' + 1) (Z₁ : Matrix (Fin m) (Fin m) K)
    (Z₂ : Matrix (Fin m') (Fin m') K) (c : Kˣ) (h₁ : IsInt R Z₁) (h₂ : IsInt R Z₂)
    (d₁ : IsUnit Z₁.det) (d₂ : IsUnit Z₂.det) :
    ∑ᶠ y, tTerm R ψ hN hN' Z₁ Z₂ (c : K) y = singleBlockInner R ψ Z₁ Z₂ (c : K) := by
  classical
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => A5x3.psi_of_mem hD.selfDual hr
  have := A5x3.finite_coker hD Z₁ h₁ d₁
  have := A5x3.finite_coker hD Z₂ h₂ d₂
  have : Finite (coker R Z₁ →ₗ[R] KR R) := A5x3.finite_dual hD.selfDual
  have : Finite (coker R Z₂ →ₗ[R] KR R) := A5x3.finite_dual hD.selfDual
  have : Finite (coker R Z₁ ≃ₗ[R] coker R Z₂) :=
    Finite.of_injective (fun θ => (θ : coker R Z₁ → coker R Z₂)) DFunLike.coe_injective
  let := Fintype.ofFinite (coker R Z₁)
  let := Fintype.ofFinite (coker R Z₂)
  let := Fintype.ofFinite (coker R Z₁ →ₗ[R] KR R)
  let := Fintype.ofFinite (coker R Z₂ →ₗ[R] KR R)
  let := Fintype.ofFinite (coker R Z₁ ≃ₗ[R] coker R Z₂)
  rw [finsum_of_inj _ (iota_injective R Z₁ Z₂ h₁ h₂ d₁ d₂) _ (tTerm_supp R ψ hN hN' Z₁ Z₂ _ d₁ d₂),
    finsum_eq_sum_of_fintype,
    Finset.sum_congr rfl fun s _ => tTerm_iota R ψ hψ hN hN' Z₁ Z₂ c h₁ h₂ d₁ d₂ s]
  have hc := comb_identity (Θ := coker R Z₁ ≃ₗ[R] coker R Z₂)
    (P₁ := fun (a : coker R Z₁ →ₗ[R] KR R) (b : coker R Z₁) =>
      a b = -(Submodule.Quotient.mk (c : K) : KR R))
    (P₂ := fun (a : coker R Z₂ →ₗ[R] KR R) (b : coker R Z₂) =>
      a b = -(Submodule.Quotient.mk (c : K) : KR R))
    (ta := fun θ a => a.comp θ.symm.toLinearMap) (tc := fun θ b => θ b)
    (Q := fun θ a b a' b' => (∀ y, a' (θ y) = a y) ∧ θ b = b')
    (by
      intro θ a b a' b'
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2.symm⟩
        apply LinearMap.ext
        intro y
        simp [← h1]
      · rintro ⟨rfl, rfl⟩
        exact ⟨fun y => by simp, rfl⟩)
    (by intro θ a b; simp)
    (fun a b => psiKR R ψ (a (eZ R Z₁) + A5x6.muZ R Z₁ d₁ b))
    (fun a b => conj (psiKR R ψ (a (eZ R Z₂) + A5x6.muZ R Z₂ d₂ b)))
  refine Eq.trans ?_ (hc.trans ?_)
  · exact Finset.sum_congr rfl fun s _ => rfl
  · unfold singleBlockInner
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : a b = -(Submodule.Quotient.mk (c : K) : KR R)
    · rw [if_pos hab, if_pos hab, psiKR_conj R ψ hD, ← A5x6.psiKR_add R ψ hψ,
        A5x6.lamLin_out R Z₁ d₁, A5x6.lamLin_out R Z₂ d₂]
      congr 1
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_sub]
      abel
    · rw [if_neg hab, if_neg hab]

end InnerSum

section Final
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem tTerm_zero (R : Subring K) (ψ : AddChar K ℂ) {m m' N N' : ℕ}
    (hN : N = m + 1) (hN' : N' = m' + 1) (Z₁ : Matrix (Fin m) (Fin m) K)
    (Z₂ : Matrix (Fin m') (Fin m') K) (c : K) (hn : ¬ (IsInt R Z₁ ∧ IsInt R Z₂))
    (y : ((Fin m → KR R) × (Fin m → KR R)) × ((Fin m' → KR R) × (Fin m' → KR R))) :
    tTerm R ψ hN hN' Z₁ Z₂ c y = 0 := by
  unfold tTerm
  rw [if_neg]
  · simp
  · rintro ⟨h1, h2⟩
    unfold bigZ at h1 h2
    exact hn ⟨((blkM_isInt R hN _ _ _ _).1 h1).1, ((blkM_isInt R hN' _ _ _ _).1 h2).1⟩

theorem tTerm_fin (R : Subring K) (ψ : AddChar K ℂ) (hD : LocalDatum K R ψ) {m m' N N' : ℕ}
    (hN : N = m + 1) (hN' : N' = m' + 1) (Z₁ : Matrix (Fin m) (Fin m) K)
    (Z₂ : Matrix (Fin m') (Fin m') K) (c : K) (d₁ : IsUnit Z₁.det) (d₂ : IsUnit Z₂.det) :
    (Function.support (tTerm R ψ hN hN' Z₁ Z₂ c)).Finite := by
  by_cases hI : IsInt R Z₁ ∧ IsInt R Z₂
  · have := A5x3.finite_coker hD Z₁ hI.1 d₁
    have := A5x3.finite_coker hD Z₂ hI.2 d₂
    have : Finite (coker R Z₁ →ₗ[R] KR R) := A5x3.finite_dual hD.selfDual
    have : Finite (coker R Z₂ →ₗ[R] KR R) := A5x3.finite_dual hD.selfDual
    exact (Set.finite_range (iota R Z₁ Z₂)).subset (tTerm_supp R ψ hN hN' Z₁ Z₂ c d₁ d₂)
  · have : Function.support (tTerm R ψ hN hN' Z₁ Z₂ c) = ∅ := by
      ext y
      simp [tTerm_zero R ψ hN hN' Z₁ Z₂ c hI y]
    rw [this]
    exact Set.finite_empty

theorem orbZ_unit (w : Point K) (p : lowW K w.1 w.2 × upUniG K w.1.sum) :
    IsUnit (orbZ w p).det := by
  rw [A5x6.orbZ_det]; exact A5x6.pt_det_isUnit w

theorem first_kernel_formula_proof : SingleBlockFormula := by
  intro K _ _ _ R ψ hD h h' c _
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => A5x3.psi_of_mem hD.selfDual hr
  have hNs : Ns R ψ 1 h h' c c = Kp R ψ (addBlock h 1 c) (addBlock h' 1 c) := by simp [Ns]
  rw [hNs]
  obtain ⟨σ, hσb, hσ⟩ := section_exists R h c
  obtain ⟨σ', hσb', hσ'⟩ := section_exists R h' c
  rw [Kp_eq_section R ψ hψ _ _ _ _ σ σ' hσb hσb']
  let F : (Cos R h × Cos R h') × (((Fin h.1.sum → KR R) × (Fin h.1.sum → KR R)) ×
      ((Fin h'.1.sum → KR R) × (Fin h'.1.sum → KR R))) → ℂ := fun z =>
    tTerm R ψ (addBlock_sum h c) (addBlock_sum h' c) (orbZ h (rep R z.1.1)) (orbZ h' (rep R z.1.2))
      (c : K) z.2 * (phase ψ (rep R z.1.1) * conj (phase ψ (rep R z.1.2)))
  have hG : ∀ x : Par R h × Par R h', Gterm R ψ _ _ (σ x.1) (σ' x.2) =
      F (Equiv.prodProdProdComm _ _ _ _ x) := by
    rintro ⟨⟨q, x, y⟩, ⟨q', x', y'⟩⟩
    simp only [F, Equiv.prodProdProdComm_apply]
    rw [tTerm_mk]
    unfold Gterm
    rw [(hσ (q, x, y)).1, (hσ' (q', x', y')).1, (hσ (q, x, y)).2 ψ, (hσ' (q', x', y')).2 ψ, map_mul]
    ring
  rw [finsum_congr hG, finsum_comp_equiv]
  have hI := Formalism.FourierDecayAlt.P.integral_points_finite K R ψ hD h
  have hI' := Formalism.FourierDecayAlt.P.integral_points_finite K R ψ hD h'
  have hfin : (Function.support F).Finite := by
    refine ((hI.prod hI').biUnion (t := fun q => (Prod.mk q) ''
      Function.support (tTerm R ψ (addBlock_sum h c) (addBlock_sum h' c) (orbZ h (rep R q.1))
        (orbZ h' (rep R q.2)) (c : K))) fun q _ => (tTerm_fin R ψ hD _ _ _ _ _
        (orbZ_unit _ _) (orbZ_unit _ _)).image _).subset ?_
    rintro ⟨q, y⟩ hz
    have h1 : tTerm R ψ (addBlock_sum h c) (addBlock_sum h' c) (orbZ h (rep R q.1))
        (orbZ h' (rep R q.2)) (c : K) y ≠ 0 := fun h0 => hz (by simp [F, h0])
    have h2 : IsInt R (orbZ h (rep R q.1)) ∧ IsInt R (orbZ h' (rep R q.2)) := by
      by_contra hn
      exact h1 (tTerm_zero R ψ _ _ _ _ _ hn y)
    exact Set.mem_biUnion (x := q) ⟨h2.1, h2.2⟩ ⟨y, h1, rfl⟩
  rw [finsum_curry F hfin]
  refine finsum_congr fun q => ?_
  simp only [F]
  rw [← finsum_mul]
  by_cases hq : IsInt R (orbZ h (rep R q.1)) ∧ IsInt R (orbZ h' (rep R q.2))
  · rw [if_pos hq, inner_sum R ψ hD _ _ _ _ c hq.1 hq.2 (orbZ_unit _ _) (orbZ_unit _ _)]
    ring
  · rw [if_neg hq, finsum_congr (tTerm_zero R ψ _ _ _ _ _ hq)]
    simp

end Final

end Formalism.FourierDecayAlt.P.A5x8

namespace Formalism.FourierDecayAlt.P

theorem first_kernel_explicit_formula : Formalism.FourierDecayAlt.A5.SingleBlockFormula := A5x8.first_kernel_formula_proof

end Formalism.FourierDecayAlt.P
