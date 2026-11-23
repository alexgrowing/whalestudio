import Mathlib
import Formalism.PeriodIntegrals.VolNzeroOne

noncomputable section

namespace PI.VolNzeroOne.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem coord_zero_of_row {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (v : Fin n → E)
    (hv : Matrix.mulVec G v = 0) (k i : Fin n) (d : E) (hd : d ≠ 0)
    (hrow : ∀ j, G k j = if j = i then d else 0) : v i = 0 := by
  have h := congrFun hv k
  simp only [Matrix.mulVec, dotProduct, hrow, Pi.zero_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact (mul_eq_zero.mp h).resolve_left hd

theorem linIndep_of_gram {n M : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) (h : (gramE σ J X).det ≠ 0) : LinearIndependent E X := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have key : ∀ a, ∑ b, gramE σ J X a b * c b = hE σ J (X a) (∑ b, c b • X b) := by
    intro a
    simp only [gramE, hE, Formalism.UG.hform, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hG : Matrix.mulVec (gramE σ J X) c = 0 := by
    funext a
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [key, hc]
    simp [hE, Formalism.UG.hform]
  have hc0 := Matrix.eq_zero_of_mulVec_eq_zero h hG
  intro i
  exact congrFun hc0 i

end Alg

section Frames

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem frameInitialVectors_castSucc {M r : ℕ} (P : Frame E M r) (a : Fin r) : F0 P (Fin.castSucc a) = P.e a := by
  simp [F0]

theorem frameInitialVectors_last {M r : ℕ} (P : Frame E M r) : F0 P (Fin.last r) = P.z := by
  simp [F0]

theorem tupH_e {M r : ℕ} (P : Frame E M r) (a : Fin r) :
    tupH P (Fin.castAdd r (Fin.castSucc a)) = P.e a := by
  simp [tupH, F0]

theorem tupH_alt {M r : ℕ} (P : Frame E M r) : tupH P (Fin.castAdd r (Fin.last r)) = P.z := by
  simp [tupH, F0]

theorem tupH_f {M r : ℕ} (P : Frame E M r) (a : Fin r) : tupH P (Fin.natAdd (r + 1) a) = P.f a := by
  simp [tupH]

theorem iz_ne_ie {r : ℕ} (a : Fin r) :
    (Fin.castAdd r (Fin.last r) : Fin (r + 1 + r)) ≠ Fin.castAdd r (Fin.castSucc a) := by
  intro h
  have h' := congrArg Fin.val h
  simp at h'
  omega

theorem if_ne_ie {r : ℕ} (a b : Fin r) :
    (Fin.natAdd (r + 1) a : Fin (r + 1 + r)) ≠ Fin.castAdd r (Fin.castSucc b) := by
  intro h
  have h' := congrArg Fin.val h
  simp at h'
  omega

theorem if_ne_iz {r : ℕ} (a : Fin r) :
    (Fin.natAdd (r + 1) a : Fin (r + 1 + r)) ≠ Fin.castAdd r (Fin.last r) := by
  intro h
  have h' := congrArg Fin.val h
  simp at h'
  omega

theorem ie_inj {r : ℕ} {a b : Fin r}
    (h : (Fin.castAdd r (Fin.castSucc a) : Fin (r + 1 + r)) = Fin.castAdd r (Fin.castSucc b)) :
    a = b := by
  have h' := congrArg Fin.val h
  simp at h'
  exact Fin.ext h'

theorem if_inj {r : ℕ} {a b : Fin r}
    (h : (Fin.natAdd (r + 1) a : Fin (r + 1 + r)) = Fin.natAdd (r + 1) b) : a = b := by
  have h' := congrArg Fin.val h
  simp at h'
  exact Fin.ext h'

variable {M r : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (P : Frame E M r) (T : F)

theorem row_f (hP : P.IsStd σ J T)
    (hT1 : ∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) (a : Fin r) :
    ∀ j, gramE σ J (tupH P) (Fin.natAdd (r + 1) a) j =
      if j = Fin.castAdd r (Fin.castSucc a) then 1 else 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP
  intro j
  induction j using Fin.addCases with
  | left k =>
    induction k using Fin.lastCases with
    | last =>
      simp only [gramE, tupH_alt, tupH_f]
      rw [h5 a, if_neg (iz_ne_ie a)]
    | cast c =>
      rw [← hT1]
      simp only [gramE, tupH_e, tupH_f]
      rw [h3 c a]
      by_cases hca : c = a
      · subst hca
        simp
      · rw [if_neg hca, if_neg (fun h => hca (ie_inj h)), map_zero]
  | right b =>
    simp only [gramE, tupH_f]
    rw [h2 a b, if_neg (if_ne_ie b a)]

theorem herm_wCell_last_mul_mulVec_eq_of_inWb (hP : P.IsStd σ J T)
    (hT1 : ∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) :
    ∀ j, gramE σ J (tupH P) (Fin.castAdd r (Fin.last r)) j =
      if j = Fin.castAdd r (Fin.last r) then algebraMap F E (-T) else 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP
  intro j
  induction j using Fin.addCases with
  | left k =>
    induction k using Fin.lastCases with
    | last =>
      simp only [gramE, tupH_alt]
      rw [h6]
      simp
    | cast c =>
      rw [← hT1]
      simp only [gramE, tupH_e, tupH_alt]
      rw [h4 c, map_zero, if_neg (fun h => iz_ne_ie c h.symm)]
  | right b =>
    rw [← hT1]
    simp only [gramE, tupH_alt, tupH_f]
    rw [h5 b, map_zero, if_neg (if_ne_iz b)]

theorem row_e (hP : P.IsStd σ J T) (a : Fin r) :
    ∀ j, gramE σ J (tupH P) (Fin.castAdd r (Fin.castSucc a)) j =
      if j = Fin.natAdd (r + 1) a then 1 else 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP
  intro j
  induction j using Fin.addCases with
  | left k =>
    induction k using Fin.lastCases with
    | last =>
      simp only [gramE, tupH_e, tupH_alt]
      rw [h4 a, if_neg (fun h => if_ne_iz a h.symm)]
    | cast c =>
      simp only [gramE, tupH_e]
      rw [h1 a c, if_neg (fun h => if_ne_ie a c h.symm)]
  | right b =>
    simp only [gramE, tupH_e, tupH_f]
    rw [h3 a b]
    by_cases hab : a = b
    · subst hab
      simp
    · rw [if_neg hab, if_neg (fun h => hab (if_inj h).symm)]

theorem det_gram_tupH_ne_zero (hP : P.IsStd σ J T)
    (hT1 : ∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) :
    (gramE σ J (tupH P)).det ≠ 0 := by
  have hTne : algebraMap F E (-T) ≠ 0 := by
    rw [map_neg, neg_ne_zero]
    exact (map_ne_zero (algebraMap F E)).mpr hP.2.2.2.2.2.2
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  funext j
  induction j using Fin.addCases with
  | left k =>
    induction k using Fin.lastCases with
    | last => exact coord_zero_of_row _ v hv _ _ _ hTne (herm_wCell_last_mul_mulVec_eq_of_inWb σ J P T hP hT1)
    | cast c => exact coord_zero_of_row _ v hv _ _ 1 one_ne_zero (row_f σ J P T hP hT1 c)
  | right b => exact coord_zero_of_row _ v hv _ _ 1 one_ne_zero (row_e σ J P T hP b)

theorem linearIndependent_frame_with_normal (hP : P.IsStd σ J T)
    (hT1 : ∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) :
    LinearIndependent E (F0 P) := by
  have h := linIndep_of_gram σ J (tupH P) (det_gram_tupH_ne_zero σ J P T hP hT1)
  have he : F0 P = tupH P ∘ Fin.castAdd r := by
    funext i
    simp [tupH]
  rw [he]
  exact h.comp _ (Fin.castAdd_injective _ _)

theorem gram_frame_with_normal_eq_diag (hP : P.IsStd σ J T)
    (hT0 : ∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j) :
    ∀ i j, gramE σ J (F0 P) i j =
      if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP
  intro i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simp only [gramE, frameInitialVectors_last]
      rw [h6]
      simp
    | cast b =>
      rw [← hT0]
      simp only [gramE, frameInitialVectors_last, frameInitialVectors_castSucc]
      rw [h4 b, map_zero]
      simp [(Fin.castSucc_lt_last b).ne]
  | cast a =>
    induction j using Fin.lastCases with
    | last =>
      simp only [gramE, frameInitialVectors_last, frameInitialVectors_castSucc]
      rw [h4 a]
      simp [(Fin.castSucc_lt_last a).ne]
    | cast b =>
      simp only [gramE, frameInitialVectors_castSucc]
      rw [h1 a b]
      simp [(Fin.castSucc_lt_last a).ne]

end Frames

end PI.VolNzeroOne.W
