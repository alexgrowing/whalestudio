import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.ChainTwTopQ
import Formalism.LocalToGlobal.Columns.DiagUnitMemAndNormalizesKOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetTwist
import Formalism.LocalToGlobal.Columns.ChainTopLawTw
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep

namespace GlobalTheory.BlockDecompositionK1

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem reduction_eq_zero_of_integral_absNorm_pow_inv_mul {c : ℕ} {a : E} (h : IntAt P (((qOf P : E) ^ (c + 1))⁻¹ * a)) : redP P a = 0 := by
  apply redP_eq_zero_of_div
  have hq := qOf_ne_zero (P := P)
  have h2 := (intAt_pow (intAt_nat (P := P) (qOf P)) c).mul h
  convert h2 using 1
  rw [pow_succ]
  field_simp

theorem intAt_inv_of_isUnit {a : E} (ha : IntAt P a) (hu : IsUnit (redP P a)) : a ≠ 0 ∧ IntAt P a⁻¹ := by
  obtain ⟨r, s, hs, h⟩ := id ha
  have hsp := reduction_spec P hs h
  have hr : r ∉ P.asIdeal := fun hr => by
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hr] at hsp
    have hs0 : (Ideal.Quotient.mk P.asIdeal) s ≠ 0 := fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    exact hs0 ((hu.mul_left_eq_zero).1 hsp)
  have hr0 : algebraMap (𝓞 E) E r ≠ 0 := by
    rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    intro h0
    exact hr (h0 ▸ Ideal.zero_mem _)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact hr0 h.symm
  refine ⟨ha0, ?_⟩
  have h1 := (IntAt.coe P s).div_of_notMem hr
  convert h1 using 1
  rw [eq_div_iff hr0, ← h]
  field_simp

theorem mulVec_mem_stdAt {n : ℕ} {M : Matrix (Fin n) (Fin n) E} (hM : ∀ i l, IntAt P (M i l)) {x : Sp E n}
    (hx : x ∈ stdAt E n P) : M.mulVec x ∈ stdAt E n P :=
  mem_stdAt.2 fun i => by
    show IntAt P (∑ l, M i l * x l)
    exact intAt_sum _ fun l _ => (hM i l).mul (mem_stdAt.1 hx l)

theorem exists_glint_of_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (hA : ∀ i l, IntAt P (A i l))
    (hd : IsUnit (redP P A.det)) : ∃ j : GLint E n P, ∀ x, j.1 x = A.mulVec x := by
  obtain ⟨hne, hinv⟩ := intAt_inv_of_isUnit (det_int hA).1 hd
  have hU : IsUnit A.det := isUnit_iff_ne_zero.2 hne
  let I : Invertible A := Matrix.invertibleOfIsUnitDet A hU
  have hB : ∀ i l, IntAt P (A⁻¹ i l) := by
    intro i l
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    refine hinv.mul ?_
    rw [Matrix.adjugate_apply]
    refine (det_int fun a b => ?_).1
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs
      · exact intAt_one
      · exact intAt_zero
    · exact hA a b
  have hf : ∀ x, Matrix.toLinearEquiv' A I x = A.mulVec x := fun x => rfl
  have hf' : ∀ x, (Matrix.toLinearEquiv' A I).symm x = A⁻¹.mulVec x := fun x => by
    rw [← Matrix.invOf_eq_nonsing_inv]
    rfl
  refine ⟨⟨Matrix.toLinearEquiv' A I, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩, hf⟩
  · have := mulVec_mem_stdAt hB h
    rwa [← hf', LinearEquiv.symm_apply_apply] at this
  · rw [hf]
    exact mulVec_mem_stdAt hA h

theorem inv_extI_mul_mem {N n : ℕ} (hN : N = n + 1) (c : ℕ) (g : GLint E N P) (j : GLint E n P)
    (hj : ∀ i l, j.1 (Pi.single l 1) i = g.1 (Pi.single (Br.iC hN l) 1) (Br.iC hN i))
    (hB : ∀ i : Fin n, IntAt P (((qOf P : E) ^ c)⁻¹ * g.1 (Pi.single (Br.iL hN) 1) (Br.iC hN i)))
    (hC : ∀ l : Fin n, IntAt P (((qOf P : E) ^ c)⁻¹ * g.1 (Pi.single (Br.iC hN l) 1) (Br.iL hN)))
    (hD : IntAt P (((qOf P : E) ^ c)⁻¹ * (g.1 (Pi.single (Br.iL hN) 1) (Br.iL hN) - 1))) :
    (extI hN P j)⁻¹ * g ∈ prinCong N P c := by
  subst hN
  rw [inv_mul_mem_prinCong]
  intro x hx
  have hxi := mem_stdAt.1 hx
  have eg : ∀ i, g.1 x i = ∑ l : Fin n, x l.castSucc * g.1 (Pi.single l.castSucc 1) i +
      x (Fin.last n) * g.1 (Pi.single (Fin.last n) 1) i := fun i => by
    have := apply_eq_sum (g.1 : Sp E (n + 1) →ₗ[E] Sp E (n + 1)) x i
    rw [Fin.sum_univ_castSucc] at this
    exact this
  refine mem_stdAt.2 fun k => ?_
  show IntAt P (((qOf P : E) ^ c)⁻¹ * (g.1 x k - (extI rfl P j).1 x k))
  rw [extI_val]
  refine Fin.lastCases ?_ (fun i => ?_) k
  · have e : sumE rfl j.1 1 x (Fin.last n) = x (Fin.last n) := by
      have := sumE_last (rfl : n + 1 = n + 1) j.1 1 x
      rw [Units.val_one, one_mul] at this
      exact this
    rw [e, eg]
    have e2 : ((qOf P : E) ^ c)⁻¹ * (∑ l : Fin n, x l.castSucc * g.1 (Pi.single l.castSucc 1) (Fin.last n) +
        x (Fin.last n) * g.1 (Pi.single (Fin.last n) 1) (Fin.last n) - x (Fin.last n)) =
        ∑ l : Fin n, x l.castSucc * (((qOf P : E) ^ c)⁻¹ * g.1 (Pi.single l.castSucc 1) (Fin.last n)) +
        x (Fin.last n) * (((qOf P : E) ^ c)⁻¹ * (g.1 (Pi.single (Fin.last n) 1) (Fin.last n) - 1)) := by
      rw [show ∑ l : Fin n, x l.castSucc * (((qOf P : E) ^ c)⁻¹ * g.1 (Pi.single l.castSucc 1) (Fin.last n)) =
          ((qOf P : E) ^ c)⁻¹ * ∑ l : Fin n, x l.castSucc * g.1 (Pi.single l.castSucc 1) (Fin.last n) by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring]
      ring
    rw [e2]
    exact IntAt.add (intAt_sum _ fun l _ => (hxi _).mul (hC l)) ((hxi _).mul hD)
  · have e : sumE rfl j.1 1 x i.castSucc = ∑ l : Fin n, x l.castSucc * g.1 (Pi.single l.castSucc 1) i.castSucc := by
      have h1 := congrFun (prH_sumE (rfl : n + 1 = n + 1) j.1 1 x) i
      rw [prH_apply] at h1
      have h2 := apply_eq_sum (j.1 : Sp E n →ₗ[E] Sp E n) (prH E rfl x) i
      rw [LinearEquiv.coe_coe] at h2
      rw [show i.castSucc = Br.iC (rfl : n + 1 = n + 1) i from rfl, h1, h2]
      exact Finset.sum_congr rfl fun l _ => by rw [prH_apply, hj]; rfl
    rw [e, eg, add_sub_cancel_left, mul_left_comm]
    exact (hxi _).mul (hB i)

theorem det_last {κ : Type} [CommRing κ] {n : ℕ} (R : Matrix (Fin (n + 1)) (Fin (n + 1)) κ)
    (h0 : ∀ l : Fin n, R (Fin.last n) l.castSucc = 0) (h1 : R (Fin.last n) (Fin.last n) = 1) :
    R.det = (R.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row R (Fin.last n), Fin.sum_univ_castSucc]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, h1, mul_one, Fin.succAbove_last, Fin.val_last]
  rw [Even.neg_one_pow ⟨n, rfl⟩, one_mul]

theorem coarse_two {r b n : ℕ} (hn : n = r + b) (k : Fin n) : coarse r [b] k.1 = if k.1 < r then 0 else 1 := by
  split_ifs with h
  · exact coarse_of_lt h
  · rw [coarse_of_le (Nat.not_lt.1 h)]
    simp only [blkIdx]
    rw [if_pos (by have := k.2; omega)]

theorem exists_block_of_twisted_k1 : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {N n : ℕ} (hN : N = n + 1) (r b c : ℕ), n = r + b → ∀ g : GLint E N P, g ∈ twK1H P N r (c + 1) → ∃ j : GLint E n P, redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b ∧ (extI hN P j)⁻¹ * g ∈ prinCong N P (c + 1) := by
  intro E _ _ _ P N n hN r b c hn g hg
  subst hN
  obtain ⟨-, hT1, hT2⟩ := isKOneType_of_mem_kOne P g hg
  have eC : ∀ l : Fin n, Br.iC (rfl : n + 1 = n + 1) l = l.castSucc := fun l => rfl
  have eL : Br.iL (rfl : n + 1 = n + 1) = Fin.last n := rfl
  have hlast : (Fin.last n).1 + 1 = n + 1 := by simp
  have hC' : ∀ i : Fin n, ¬ (i.castSucc : Fin (n + 1)).1 + 1 = n + 1 := fun i h => by
    simp only [Fin.coe_castSucc] at h; omega
  have hB : ∀ i : Fin n, IntAt P (((qOf P : E) ^ (c + 1))⁻¹ * g.1 (Pi.single (Br.iL rfl) 1) (Br.iC rfl i)) :=
    fun i => hT1 _ _ (iff_of_false (hC' i) (not_not.2 hlast))
  have hC : ∀ l : Fin n, IntAt P (((qOf P : E) ^ (c + 1))⁻¹ * g.1 (Pi.single (Br.iC rfl l) 1) (Br.iL rfl)) :=
    fun l => hT1 _ _ (iff_of_true hlast (hC' l))
  have hD : IntAt P (((qOf P : E) ^ (c + 1))⁻¹ * (g.1 (Pi.single (Br.iL rfl) 1) (Br.iL rfl) - 1)) := hT2 _ hlast
  let A : Matrix (Fin n) (Fin n) E := Matrix.of fun i l => g.1 (Pi.single (Br.iC rfl l) 1) (Br.iC rfl i)
  have hAint : ∀ i l, IntAt P (A i l) := fun i l => glint_entry g _ _
  have hdet : IsUnit (redP P A.det) := by
    rw [redP_det A hAint]
    have hR := IsUnit.map Matrix.detMonoidHom (Units.isUnit (redGL (n + 1) P g))
    have e1 : A.map (redP P) = (redMat g).submatrix Fin.castSucc Fin.castSucc := by
      ext i l
      rfl
    rw [e1, ← det_last]
    · exact hR
    · intro l
      exact reduction_eq_zero_of_integral_absNorm_pow_inv_mul (hC l)
    · have h := reduction_eq_zero_of_integral_absNorm_pow_inv_mul hD
      rw [reduction_sub (glint_entry g _ _) intAt_one, reduction_one₂, sub_eq_zero] at h
      exact h
  obtain ⟨j, hj⟩ := exists_glint_of_matrix A hAint hdet
  have hj' : ∀ i l, j.1 (Pi.single l 1) i = g.1 (Pi.single (Br.iC rfl l) 1) (Br.iC rfl i) := fun i l => by
    rw [hj]
    simp [Matrix.mulVec_single_one, A]
  refine ⟨j, ?_, inv_extI_mul_mem rfl (c + 1) g j hj' hB hC hD⟩
  show redGL n P j ∈ btG n _ (coarse r [b])
  rw [mem_btG]
  intro i l hil
  rw [coarse_two hn, coarse_two hn] at hil
  have hl : l.1 < r := by
    by_contra h
    rw [if_neg h] at hil
    split_ifs at hil <;> omega
  have hi : r ≤ i.1 := by
    by_contra h
    rw [if_pos (Nat.lt_of_not_le h)] at hil
    omega
  rw [redGL_val]
  show redP P (j.1 (Pi.single l 1) i) = 0
  rw [hj']
  have hv : (Pi.single (Br.iC rfl l) 1 : Sp E (n + 1 + 0)) ∈ LocE.parL P (qOf P) r (n + 1) 0 :=
    GlobalTheory.LastSteps.mem_sclLat.2 fun k => by
      by_cases hk : k = Br.iC rfl l
      · subst hk
        have : ¬ (r ≤ (Br.iC (rfl : n + 1 = n + 1) l).1 ∧ (Br.iC (rfl : n + 1 = n + 1) l).1 < n + 1) := fun h => by
          have := h.1; simp [Br.iC] at this; omega
        simp only [if_neg this, zpow_zero, inv_one, one_mul, Pi.single_eq_same]
        exact intAt_one
      · simp only [Pi.single_apply, hk, if_false, mul_zero]
        exact intAt_zero
  have h1 := GlobalTheory.LastSteps.mem_sclLat.1 (((hg.1.2 _).2 hv)) (Br.iC rfl i)
  have h2 : r ≤ (Br.iC (rfl : n + 1 = n + 1) i).1 ∧ (Br.iC (rfl : n + 1 = n + 1) i).1 < n + 1 := by
    simp [Br.iC]; omega
  rw [if_pos h2, zpow_one] at h1
  apply redP_eq_zero_of_div
  rw [div_eq_inv_mul]
  exact h1

end GlobalTheory.BlockDecompositionK1
