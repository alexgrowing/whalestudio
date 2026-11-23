import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalSplitTypeMixedSecond

noncomputable section

namespace Formalism.L2.SG.Pf.LocUnramB

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups MeasureTheory
open Classical

section GLR

variable {B : Type} [CommRing B] (R : Subring B) {n : ℕ}

def IsGL (A : Matrix (Fin n) (Fin n) B) : Prop :=
  (∀ i j, A i j ∈ R) ∧ ∃ C : Matrix (Fin n) (Fin n) B, (∀ i j, C i j ∈ R) ∧ A * C = 1

theorem int_mul {A A' : Matrix (Fin n) (Fin n) B} (h : ∀ i j, A i j ∈ R) (h' : ∀ i j, A' i j ∈ R) :
    ∀ i j, (A * A') i j ∈ R := fun i j => by
  rw [Matrix.mul_apply]; exact R.sum_mem fun k _ => R.mul_mem (h _ _) (h' _ _)

theorem isGL_mul {A A' : Matrix (Fin n) (Fin n) B} (h : IsGL R A) (h' : IsGL R A') : IsGL R (A * A') := by
  obtain ⟨hA, C, hC, hAC⟩ := h
  obtain ⟨hA', C', hC', hAC'⟩ := h'
  refine ⟨int_mul R hA hA', C' * C, int_mul R hC' hC, ?_⟩
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc A' C' C, hAC', Matrix.one_mul, hAC]

theorem isGL_of_det_one {A : Matrix (Fin n) (Fin n) B} (h : ∀ i j, A i j ∈ R) (hd : A.det = 1) : IsGL R A :=
  ⟨h, A⁻¹, fun i j => Formalism.MainNotions.LocalModelPeriodLattices.isInt_inv_of R A h 1 R.one_mem (by rw [hd, mul_one]) i j,
    Matrix.mul_nonsing_inv _ (by rw [hd]; exact isUnit_one)⟩

def IsLoU (A : Matrix (Fin n) (Fin n) B) : Prop := (∀ a, A a a = 1) ∧ ∀ a b, a < b → A a b = 0

def IsUpU (A : Matrix (Fin n) (Fin n) B) : Prop := (∀ a, A a a = 1) ∧ ∀ a b, b < a → A a b = 0

theorem isLowUni_of {A : Matrix (Fin n) (Fin n) B} (h : IsLoU A) : Formalism.DoubleCosetMeasures.IsLowUni A :=
  ⟨fun i j hij => h.2 i j hij, h.1⟩

theorem isUpUni_of {A : Matrix (Fin n) (Fin n) B} (h : IsUpU A) : Formalism.DoubleCosetMeasures.IsUpUni A :=
  ⟨fun i j hij => h.2 i j hij, h.1⟩

theorem isLoU_of {A : Matrix (Fin n) (Fin n) B} (h : Formalism.DoubleCosetMeasures.IsLowUni A) : IsLoU A :=
  ⟨h.2, fun i j hij => h.1 hij⟩

theorem isUpU_of {A : Matrix (Fin n) (Fin n) B} (h : Formalism.DoubleCosetMeasures.IsUpUni A) : IsUpU A :=
  ⟨h.2, fun i j hij => h.1 hij⟩

theorem isLoU_mul {A A' : Matrix (Fin n) (Fin n) B} (h : IsLoU A) (h' : IsLoU A') : IsLoU (A * A') :=
  isLoU_of (Formalism.DoubleCosetMeasures.isLowUni_mul B (isLowUni_of h) (isLowUni_of h'))

theorem isUpU_mul {A A' : Matrix (Fin n) (Fin n) B} (h : IsUpU A) (h' : IsUpU A') : IsUpU (A * A') :=
  isUpU_of (Formalism.DoubleCosetMeasures.isUpUni_mul B (isUpUni_of h) (isUpUni_of h'))

theorem isLoU_inv {A : Matrix (Fin n) (Fin n) B} (h : IsLoU A) : IsLoU A⁻¹ :=
  isLoU_of (Formalism.DoubleCosetMeasures.isLowUni_inv B (isLowUni_of h))

theorem isUpU_inv {A : Matrix (Fin n) (Fin n) B} (h : IsUpU A) : IsUpU A⁻¹ :=
  isUpU_of (Formalism.DoubleCosetMeasures.isUpUni_inv B (isUpUni_of h))

theorem det_loU {A : Matrix (Fin n) (Fin n) B} (h : IsLoU A) : A.det = 1 := Formalism.DoubleCosetMeasures.isLowUni_det B (isLowUni_of h)

theorem det_upU {A : Matrix (Fin n) (Fin n) B} (h : IsUpU A) : A.det = 1 := Formalism.DoubleCosetMeasures.isUpUni_det B (isUpUni_of h)

theorem inv_int_loU {A : Matrix (Fin n) (Fin n) B} (h : IsLoU A) (hi : ∀ i j, A i j ∈ R) : ∀ i j, A⁻¹ i j ∈ R :=
  Formalism.MainNotions.LocalModelPeriodLattices.isInt_inv_of R A hi 1 R.one_mem (by rw [det_loU h, mul_one])

theorem inv_int_upU {A : Matrix (Fin n) (Fin n) B} (h : IsUpU A) (hi : ∀ i j, A i j ∈ R) : ∀ i j, A⁻¹ i j ∈ R :=
  Formalism.MainNotions.LocalModelPeriodLattices.isInt_inv_of R A hi 1 R.one_mem (by rw [det_upU h, mul_one])

theorem mul_inv_loU {A : Matrix (Fin n) (Fin n) B} (h : IsLoU A) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (by rw [det_loU h]; exact isUnit_one)

theorem inv_mul_loU {A : Matrix (Fin n) (Fin n) B} (h : IsLoU A) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul _ (by rw [det_loU h]; exact isUnit_one)

theorem mul_inv_upU {A : Matrix (Fin n) (Fin n) B} (h : IsUpU A) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (by rw [det_upU h]; exact isUnit_one)

theorem inv_mul_upU {A : Matrix (Fin n) (Fin n) B} (h : IsUpU A) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul _ (by rw [det_upU h]; exact isUnit_one)

end GLR

section Cls

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E]

theorem cok_sub_of_isGL (M : Loc.Model F E) {m : ℕ} (ZZ : M.Mat (m + 1)) (h : IsGL M.R (ZZ.Z.map M.R.subtype)) :
    Subsingleton (M.Cok ZZ) := by
  obtain ⟨-, C, hC, hAC⟩ := h
  let CR : Matrix (Fin (m + 1)) (Fin (m + 1)) M.R := Matrix.of fun i j => ⟨C i j, hC i j⟩
  have hCR : ZZ.Z * CR = 1 := by
    apply Matrix.map_injective (f := M.R.subtype) Subtype.val_injective
    show (ZZ.Z * CR).map M.R.subtype = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) M.R).map M.R.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hAC
  unfold Loc.Model.Cok
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  intro x _
  refine ⟨Matrix.mulVec CR x, ?_⟩
  simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hCR]

theorem clsOf_triv (M : Loc.Model F E) {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (h : IsGL M.R A) :
    clsOf M A = some (LocModel.trivCls M m) := by
  obtain ⟨hA, C, hC, hAC⟩ := h
  have hu : IsUnit A.det := Matrix.isUnit_det_of_right_inverse hAC
  unfold clsOf
  rw [dif_pos ⟨hA, hu⟩]
  congr 1
  apply (LocModel.sub_iff_triv M _).1
  exact cok_sub_of_isGL M _ ⟨hA, C, hC, hAC⟩

end Cls

end Formalism.L2.SG.Pf.LocUnramB

namespace Formalism.L2.SG.Pf.LocUnramB

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups MeasureTheory Formalism.L2.SG.Pf.AtPt
open Classical

section Blocks

variable {K : Type}

theorem pSt_pSig : ∀ (bs : List (K × ℕ)) (i : ℕ), pSt bs (pSig bs i) = pSt bs i
  | [], _ => rfl
  | (t, s) :: bs, i => by
    have h := pSt_pSig bs (i - s)
    by_cases hi : i < s
    · have h2 : s - 1 - i < s := by omega
      simp [pSig, pSt, hi, h2]
    · have h2 : ¬ (s + pSig bs (i - s) < s) := by omega
      simp [pSig, pSt, hi, h2, h]

theorem pSz_pSig : ∀ (bs : List (K × ℕ)) (i : ℕ), pSz bs (pSig bs i) = pSz bs i
  | [], _ => rfl
  | (t, s) :: bs, i => by
    have h := pSz_pSig bs (i - s)
    by_cases hi : i < s
    · have h2 : s - 1 - i < s := by omega
      simp [pSig, pSz, hi, h2]
    · have h2 : ¬ (s + pSig bs (i - s) < s) := by omega
      simp [pSig, pSz, hi, h2, h]

theorem pSt_lt : ∀ (bs : List (K × ℕ)) (i j : ℕ), i < j → pSt bs i ≠ pSt bs j → pSt bs i + pSz bs i ≤ pSt bs j
  | [], i, j, _, h => absurd rfl h
  | (t, s) :: bs, i, j, hij, h => by
    have ih := pSt_lt bs (i - s) (j - s)
    simp only [pSt, pSz] at h ⊢
    by_cases hi : i < s
    · by_cases hj : j < s
      · rw [if_pos hi, if_pos hj] at h; exact absurd rfl h
      · rw [if_pos hi, if_pos hi, if_neg hj]; omega
    · rw [if_neg hi, if_neg (by omega)] at h
      rw [if_neg hi, if_neg hi, if_neg (by omega)]
      have h' : pSt bs (i - s) ≠ pSt bs (j - s) := fun e => h (by rw [e])
      have := ih (by omega) h'
      omega

theorem sameBlock_of : ∀ {E : Type} [CommRing E] (bs : List (Eˣ × ℕ+)) (cs : List (K × ℕ)),
    bs.map (fun b => (b.2 : ℕ)) = cs.map Prod.snd → ∀ a b, pSt cs a = pSt cs b →
      a < (cs.map Prod.snd).sum → b < (cs.map Prod.snd).sum → Loc.sameBlock bs a b = true
  | _, _, [], [], _, a, _, _, ha, _ => by simp at ha
  | _, _, [], _ :: _, h, _, _, _, _, _ => by simp at h
  | _, _, _ :: _, [], h, _, _, _, _, _ => by simp at h
  | E, _, (t, s) :: bs, (t', s') :: cs, h, a, b, hab, ha, hb => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hs, hrest⟩ := h
    simp only [List.map_cons, List.sum_cons] at ha hb
    have s1 : 1 ≤ s' := by rw [← hs]; exact s.pos
    simp only [pSt] at hab
    simp only [Loc.sameBlock, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, hs]
    by_cases ha' : a < s'
    · by_cases hb' : b < s'
      · exact Or.inl ⟨ha', hb'⟩
      · rw [if_pos ha', if_neg hb'] at hab; omega
    · by_cases hb' : b < s'
      · rw [if_neg ha', if_pos hb'] at hab; omega
      · rw [if_neg ha', if_neg hb'] at hab
        refine Or.inr ⟨⟨by omega, by omega⟩, sameBlock_of bs cs hrest (a - s') (b - s') (by omega) (by omega) (by omega)⟩

end Blocks

section Conj

variable {E : Type} [CommRing E] (R : Subring E) {m : ℕ}

structure Mono (W : Matrix (Fin m) (Fin m) E) where
  σ : Fin m → Fin m
  c : Fin m → E
  σσ : ∀ a, σ (σ a) = a
  cσ : ∀ a, c (σ a) = c a
  hc : ∀ a, c a ∈ R
  hci : ∀ a, Ring.inverse (c a) ∈ R
  hcu : ∀ a, IsUnit (c a)
  hW : ∀ a b, W a b = if b = σ a then c a else 0

namespace Mono

variable {R} {W : Matrix (Fin m) (Fin m) E} (H : Mono R W)

def inv : Matrix (Fin m) (Fin m) E := fun a b => if b = H.σ a then Ring.inverse (H.c a) else 0

theorem mul_inv : W * H.inv = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (H.σ a)]
  · rw [H.hW, if_pos rfl]
    unfold inv
    by_cases hb : b = a
    · subst hb; rw [if_pos (H.σσ b).symm, H.cσ, Matrix.one_apply_eq, Ring.mul_inverse_cancel _ (H.hcu b)]
    · rw [if_neg (fun h => hb (by rw [h, H.σσ])), mul_zero, Matrix.one_apply_ne (Ne.symm hb)]
  · intro k _ hk; rw [H.hW, if_neg hk, zero_mul]
  · simp

theorem inv_mul : H.inv * W = 1 := by
  rw [← Matrix.inv_eq_right_inv H.mul_inv]
  exact Matrix.nonsing_inv_mul W (Matrix.isUnit_det_of_right_inverse H.mul_inv)

include H in
theorem int : ∀ a b, W a b ∈ R := fun a b => by
  rw [H.hW]; split_ifs
  · exact H.hc a
  · exact R.zero_mem

theorem inv_int : ∀ a b, H.inv a b ∈ R := fun a b => by
  unfold inv; split_ifs
  · exact H.hci a
  · exact R.zero_mem

include H in
theorem isGL : IsGL R W := ⟨H.int, H.inv, H.inv_int, H.mul_inv⟩

theorem conj_apply (N : Matrix (Fin m) (Fin m) E) (a b : Fin m) :
    (W * N * H.inv) a b = H.c a * N (H.σ a) (H.σ b) * Ring.inverse (H.c b) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (H.σ b)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (H.σ a)]
    · unfold inv
      rw [H.hW, if_pos rfl, if_pos (H.σσ b).symm, H.cσ]
    · intro k _ hk; rw [H.hW, if_neg hk, zero_mul]
    · simp
  · intro k _ hk
    unfold inv
    rw [if_neg (fun h => hk (by rw [h, H.σσ])), mul_zero]
  · simp

end Mono

theorem int_of_orbL {W L N : Matrix (Fin m) (Fin m) E} (H : Mono R W) (hL : IsLoU L)
    (hU : IsUpU (W * N * H.inv)) (hY : ∀ i j, (L * W * N) i j ∈ R) :
    (∀ i j, L i j ∈ R) ∧ ∀ i j, N i j ∈ R := by
  have e : L * (W * N * H.inv) = L * W * N * H.inv := by simp only [Matrix.mul_assoc]
  have hI : Formalism.DoubleCosetMeasures.IsInt R (L * (W * N * H.inv)) := by
    rw [e]; exact int_mul R hY H.inv_int
  obtain ⟨h1, h2⟩ := Formalism.FourierDecayAlt.P.A5x7.lu_int R (isLowUni_of hL) (isUpUni_of hU) hI
  refine ⟨h1, ?_⟩
  have e2 : N = H.inv * (W * N * H.inv) * W := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, H.inv_mul, Matrix.one_mul, Matrix.mul_assoc, H.inv_mul,
      Matrix.mul_one]
  rw [e2]
  exact int_mul R (int_mul R H.inv_int h2) H.int

end Conj

end Formalism.L2.SG.Pf.LocUnramB

namespace Formalism.L2.SG.Pf.LocUnramB

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups MeasureTheory Formalism.L2.SG.Pf.AtPt
open Formalism.L2.SG.LsDatumB
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Local

variable {D : Formalism.BasicNotions.D7}

theorem pTau_mem {K : Type} [Zero K] : ∀ (bs : List (K × ℕ)) (i : ℕ), i < (bs.map Prod.snd).sum →
    pTau bs i ∈ bs.map Prod.fst
  | [], i, h => by simp at h
  | (t, s) :: bs, i, h => by
    simp only [List.map_cons, List.sum_cons] at h
    simp only [pTau, List.map_cons, List.mem_cons]
    by_cases hi : i < s
    · rw [if_pos hi]; exact Or.inl rfl
    · rw [if_neg hi]; exact Or.inr (pTau_mem bs (i - s) (by omega))

theorem uLow_zero {E : Type} [CommRing E] {n : ℕ} : Loc.uLow (0 : Loc.IL n → E) = 1 := by
  ext a b
  simp only [Loc.uLow, Pi.zero_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem uUp_zero {E : Type} [CommRing E] {n : ℕ} (w : Loc.Pt E n) : Loc.uUp w (0 : Loc.IN w → E) = 1 := by
  ext a b
  simp only [Loc.uUp, Pi.zero_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem blkMod_good {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (T T' : ℕ) (p : PlF D) (hA : Agree δ M p)
    (hsM : (M p).split = none)
    (hδ1 : δ p ∈ 𝒪[(D.s.atP p).Fp]) (hδ2 : (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp])
    (hUp : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧
      (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O)
    {t : D.host.E} (ht0 : t ≠ 0) (ht : (D.s.atP p).ιE t ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE t⁻¹ ∈ (D.s.atP p).O)
    (a s : ℕ) :
    blkMod δ T T' p a s t ∈ (M p).R ∧ Ring.inverse (blkMod δ T T' p a s t) ∈ (M p).R ∧
      IsUnit (blkMod δ T T' p a s t) ∧
      (nu D.R.rS a (a + s - 1) = 0 → blkMod δ T T' p a s t = (D.s.atP p).ιE t) := by
  have hsD : (D.s.atP p).split = none := LocModel.split_none_of_agree hA hsM
  obtain ⟨hOK, hδ0, hcj, hO, hpsi, -⟩ := hA
  have hRL : (M p).R = (M p).L.O := by simp only [Loc.Model.R, hsM]
  have hR : (M p).R = (D.s.atP p).O := hRL.trans hO
  set w0 : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)
    with hw0
  set w1 : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ *
    (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) with hw1
  have hw01 : w0 * w1 = 1 := by
    rw [hw0, hw1, mul_mul_mul_comm, ← map_mul, ← map_mul, mul_inv_cancel₀ hδ0,
      mul_inv_cancel₀ (by exact_mod_cast LocModel.unitAt_ne_zero₂ p), map_one, map_one, one_mul]
  have hw0O : w0 ∈ (D.s.atP p).O := Subring.mul_mem _ (LocModel.LM.algebraMap_mem_O p hδ1) hUp.1
  have hw1O : w1 ∈ (D.s.atP p).O := Subring.mul_mem _ (LocModel.LM.algebraMap_mem_O p hδ2) hUp.2
  have htau : tau0 p T T' = 0 := by simp only [tau0, hsD]
  have hb : blkMod δ T T' p a s t = w1 ^ nu D.R.rS a (a + s - 1) * (D.s.atP p).ιE t := by
    simp only [blkMod, htau, ite_self, sub_zero, tMod, twist, qE, hsD, Ring.inverse_one, mul_one]
    rw [LocModel.ring_inverse_pow_eq hw01]
  set ν := nu D.R.rS a (a + s - 1)
  have htt : (D.s.atP p).ιE t * (D.s.atP p).ιE t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ ht0, map_one]
  have hprod : w1 ^ ν * (D.s.atP p).ιE t * (w0 ^ ν * (D.s.atP p).ιE t⁻¹) = 1 := by
    calc w1 ^ ν * (D.s.atP p).ιE t * (w0 ^ ν * (D.s.atP p).ιE t⁻¹)
        = (w0 * w1) ^ ν * ((D.s.atP p).ιE t * (D.s.atP p).ιE t⁻¹) := by ring
      _ = 1 := by rw [hw01, htt, one_pow, one_mul]
  have hinv : Ring.inverse (w1 ^ ν * (D.s.atP p).ιE t) = w0 ^ ν * (D.s.atP p).ιE t⁻¹ := by
    simpa using LocModel.ring_inverse_pow_eq hprod 1
  rw [hb, hR, hinv]
  refine ⟨Subring.mul_mem _ (Subring.pow_mem _ hw1O _) ht.1, Subring.mul_mem _ (Subring.pow_mem _ hw0O _) ht.2,
    IsUnit.of_mul_eq_one _ hprod, fun h0 => by rw [h0, pow_zero, one_mul]⟩

end Local

end Formalism.L2.SG.Pf.LocUnramB

namespace Formalism.L2.SG.Pf.LocUnramB

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups MeasureTheory Formalism.L2.SG.Pf.AtPt
open Formalism.L2.SG.LsDatumB
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Place

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

def Good (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (w : Point D.host.E (D.R.rS + 1)) (p : PlF D) : Prop :=
  (M p).split = none ∧
    (δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]) ∧
    ((D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧
      (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O) ∧
    ∀ t ∈ (w.1.map Prod.fst).toFinset, ∀ k : Fin 3, t + ((k : ℕ) : D.host.E) ≠ 0 →
      (D.s.atP p).ιE (t + ((k : ℕ) : D.host.E)) ∈ (D.s.atP p).O ∧
        (D.s.atP p).ιE ((t + ((k : ℕ) : D.host.E))⁻¹) ∈ (D.s.atP p).O

theorem good_scalar {w : Point D.host.E (D.R.rS + 1)} {p : PlF D} (hg : Good δ M w p) (a : Fin (D.R.rS + 1)) :
    (D.s.atP p).ιE (pTau w.1 a.val) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE (pTau w.1 a.val)⁻¹ ∈ (D.s.atP p).O := by
  have hmem : pTau w.1 a.val ∈ (w.1.map Prod.fst).toFinset :=
    List.mem_toFinset.2 (pTau_mem w.1 a.val (by rw [w.2.2]; exact a.2))
  have h := hg.2.2.2 _ hmem 0 (by simpa using pTau_ne' w a)
  simpa using h

def monoW (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D) (hA : Agree δ M p) (hg : Good δ M w p) :
    Mono (M p).R (modMat δ T T' p w) where
  σ := sgF w
  c := fun a => blkMod δ T T' p (1 + pSt w.1 a.val) (pSz w.1 a.val) (pTau w.1 a.val)
  σσ := sgF_sgF w
  cσ := fun a => by simp only [sgF]; rw [pSt_pSig, pSz_pSig, pTau_pSig]
  hc := fun a => (blkMod_good T T' p hA hg.1 hg.2.1.1 hg.2.1.2 hg.2.2.1 (pTau_ne' w a) (good_scalar hg a) _ _).1
  hci := fun a => (blkMod_good T T' p hA hg.1 hg.2.1.1 hg.2.1.2 hg.2.2.1 (pTau_ne' w a) (good_scalar hg a) _ _).2.1
  hcu := fun a => (blkMod_good T T' p hA hg.1 hg.2.1.1 hg.2.1.2 hg.2.2.1 (pTau_ne' w a) (good_scalar hg a) _ _).2.2.1
  hW := modMat_apply' δ T T' p w

theorem sizes_of_modPt (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)
    (w₀ : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (hw₀ : modPt δ T T' p w = some w₀) :
    w₀.blocks.map (fun b => (b.2 : ℕ)) = w.1.map Prod.snd := by
  have h1 := congrArg (List.map Prod.snd) (modPt_blocks δ T T' p w w₀ hw₀)
  rw [List.map_map, mapBlocks_snd] at h1
  exact h1

theorem conj_upU (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D) (hA : Agree δ M p) (hg : Good δ M w p)
    (w₀ : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (hw₀ : modPt δ T T' p w = some w₀) (y : Loc.IN w₀ → (D.s.atP p).Ep) :
    IsUpU (modMat δ T T' p w * Loc.uUp w₀ y * (monoW T T' w p hA hg).inv) := by
  set H := monoW T T' w p hA hg
  have hsz := sizes_of_modPt T T' w p w₀ hw₀
  have hsum : (w.1.map Prod.snd).sum = D.R.rS + 1 := w.2.2
  constructor
  · intro a
    rw [Mono.conj_apply]
    have : Loc.uUp w₀ y (H.σ a) (H.σ a) = 1 := by simp [Loc.uUp]
    rw [this, mul_one, Ring.mul_inverse_cancel _ (H.hcu a)]
  · intro a b hba
    rw [Mono.conj_apply]
    suffices h0 : Loc.uUp w₀ y (H.σ a) (H.σ b) = 0 by rw [h0, mul_zero, zero_mul]
    have hσ : H.σ = sgF w := rfl
    have hne : H.σ a ≠ H.σ b := fun h => (ne_of_gt hba) (by rw [← H.σσ a, ← H.σσ b, h])
    unfold Loc.uUp
    rw [if_neg hne, dif_neg]
    rintro ⟨hlt, hsb⟩
    obtain ⟨a1, a2, a3, -, -⟩ := pBlock w.1 a.val (by rw [hsum]; exact a.2)
    obtain ⟨b1, b2, b3, -, -⟩ := pBlock w.1 b.val (by rw [hsum]; exact b.2)
    have hσa : (H.σ a).val = pSig w.1 a.val := rfl
    have hσb : (H.σ b).val = pSig w.1 b.val := rfl
    have hlt' : (H.σ a).val < (H.σ b).val := hlt
    by_cases hst : pSt w.1 a.val = pSt w.1 b.val
    · have hsame : Loc.sameBlock w₀.blocks (H.σ a).val (H.σ b).val = true := by
        refine sameBlock_of w₀.blocks w.1 hsz _ _ ?_ ?_ ?_
        · rw [hσa, hσb, pSt_pSig, pSt_pSig, hst]
        · rw [hsum]; exact (H.σ a).2
        · rw [hsum]; exact (H.σ b).2
      rw [hsame] at hsb
      exact Bool.noConfusion hsb
    · have hlt2 := pSt_lt w.1 b.val a.val hba (Ne.symm hst)
      have hba' : b.val < a.val := hba
      omega

theorem orb_int (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D) (hA : Agree δ M p) (hg : Good δ M w p)
    (w₀ : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (hw₀ : modPt δ T T' p w = some w₀)
    (x : Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) (y : Loc.IN w₀ → (D.s.atP p).Ep)
    (hY : ∀ i j, (Loc.uLow x * modMat δ T T' p w * Loc.uUp w₀ y) i j ∈ (M p).R) :
    (∀ i j, Loc.uLow x i j ∈ (M p).R) ∧ ∀ i j, Loc.uUp w₀ y i j ∈ (M p).R :=
  int_of_orbL (M p).R (monoW T T' w p hA hg) (isLoU_of (Formalism.MainNotions.LocalModelPeriodLattices.isLowUni_uLow x))
    (conj_upU T T' w p hA hg w₀ hw₀ y) hY

theorem kkOrb_eq (p : PlF D) {Y W L N : LsDatumB.MatP D p} (hL : IsLoU L) (hLi : ∀ i j, L i j ∈ (M p).R)
    (hN : IsUpU N) (hNi : ∀ i j, N i j ∈ (M p).R) (hY : Y = L * W * N) : kkOrb M p Y = kkOrb M p W := by
  ext Y'
  constructor
  · rintro ⟨l, ρ, hl, hρ, rfl⟩
    have hl' : IsLoU l := ⟨hl.1, hl.2.1⟩
    have hρ' : IsUpU ρ := ⟨hρ.1, hρ.2.1⟩
    refine ⟨l * L, N * ρ, ⟨(isLoU_mul hl' hL).1, (isLoU_mul hl' hL).2, int_mul _ hl.2.2 hLi⟩,
      ⟨(isUpU_mul hN hρ').1, (isUpU_mul hN hρ').2, int_mul _ hNi hρ.2.2⟩, ?_⟩
    rw [hY]; simp only [Matrix.mul_assoc]
  · rintro ⟨l, ρ, hl, hρ, rfl⟩
    have hl' : IsLoU l := ⟨hl.1, hl.2.1⟩
    have hρ' : IsUpU ρ := ⟨hρ.1, hρ.2.1⟩
    have hLinv := isLoU_inv hL
    have hNinv := isUpU_inv hN
    refine ⟨l * L⁻¹, N⁻¹ * ρ, ⟨(isLoU_mul hl' hLinv).1, (isLoU_mul hl' hLinv).2,
      int_mul _ hl.2.2 (inv_int_loU _ hL hLi)⟩,
      ⟨(isUpU_mul hNinv hρ').1, (isUpU_mul hNinv hρ').2, int_mul _ (inv_int_upU _ hN hNi) hρ.2.2⟩, ?_⟩
    rw [hY]
    have e : l * L⁻¹ * (L * W * N) * (N⁻¹ * ρ) = l * (L⁻¹ * L) * W * (N * N⁻¹) * ρ := by
      simp only [Matrix.mul_assoc]
    rw [e, inv_mul_loU hL, mul_inv_upU hN, Matrix.mul_one, Matrix.mul_one]

end Place

end Formalism.L2.SG.Pf.LocUnramB

namespace Formalism.L2.SG.Pf.LocUnramB

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups MeasureTheory Formalism.L2.SG.Pf.AtPt
open Formalism.L2.SG.LsDatumB
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

def cornerM (p : PlF D) (c : (D.s.atP p).Ep) : LsDatumB.MatP D p :=
  Matrix.of fun a b => if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then c else 0

theorem loU_corner (p : PlF D) (c : (D.s.atP p).Ep) {L N : LsDatumB.MatP D p} (hL : IsLoU L) (hN : IsUpU N) :
    L * cornerM p c * N = cornerM p c := by
  have hLl : ∀ a, L a (Fin.last _) = if a = Fin.last _ then 1 else 0 := fun a => by
    split_ifs with h
    · rw [h]; exact hL.1 _
    · exact hL.2 a _ (lt_of_le_of_ne (Fin.le_last a) h)
  have hNl : ∀ b, N (Fin.last _) b = if b = Fin.last _ then 1 else 0 := fun b => by
    split_ifs with h
    · rw [h]; exact hN.1 _
    · exact hN.2 _ b (lt_of_le_of_ne (Fin.le_last b) h)
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last _)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last _)]
    · simp only [cornerM, Matrix.of_apply, true_and, and_true]
      rw [hLl, hNl]
      by_cases ha : a = Fin.last _ <;> by_cases hb : b = Fin.last _ <;> simp [ha, hb]
    · intro k _ hk; simp [cornerM, hk]
    · simp
  · intro k _ hk
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro l _; simp [cornerM, hk]
  · simp

theorem shift_isGL (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D) (hA : Agree δ M p)
    (hg : Good δ M w p) : IsGL (M p).R (modMat δ T T' p w + cornerM p (cornerSh δ T T' p w)) := by
  set H := monoW T T' w p hA hg
  by_cases hD : Dmin w D.R.rS = 0
  · have : cornerSh δ T T' p w = 0 := by unfold cornerSh; rw [if_pos hD]
    rw [this]
    have h0 : cornerM p (0 : (D.s.atP p).Ep) = 0 := by ext a b; simp [cornerM]
    rw [h0, add_zero]
    exact H.isGL
  obtain ⟨l0, t, hb, hs⟩ := last_one w hD
  have hz : zetaOf w = t := zeta_snoc w hD l0 t hb hs
  have ht0 : t ≠ 0 := (w.2.1 (t, 1) (by rw [hb]; simp)).1

  have hpm := ptMat_last w l0 t hb hs
  rw [ptMat_apply'] at hpm
  have hσl : sgF w (Fin.last _) = Fin.last _ := by
    by_contra h
    rw [if_neg (Ne.symm h)] at hpm
    exact ht0 hpm.symm
  rw [if_pos hσl.symm] at hpm
  obtain ⟨c1, c2⟩ := (cond_iff w (Fin.last _)).2 ⟨rfl, hσl⟩
  have hst : pSt w.1 (Fin.last D.R.rS).val = D.R.rS := by
    simp only [Fin.val_last] at c1 c2 ⊢; omega
  have hcl : H.c (Fin.last _) = blkMod δ T T' p (D.R.rS + 1) 1 t := by
    show blkMod δ T T' p (1 + pSt w.1 (Fin.last D.R.rS).val) (pSz w.1 (Fin.last D.R.rS).val)
      (pTau w.1 (Fin.last D.R.rS).val) = _
    rw [c2, hpm, hst, add_comm]
  have hcl' : blkMod δ T T' p (D.R.rS + 1) 1 t = (D.s.atP p).ιE t := by
    have hmem : t ∈ (w.1.map Prod.fst).toFinset := List.mem_toFinset.2 (by rw [hb]; simp)
    have h := hg.2.2.2 t hmem 0 (by simpa using ht0)
    simp only [Fin.val_zero, Nat.cast_zero, add_zero] at h
    exact (blkMod_good T T' p hA hg.1 hg.2.1.1 hg.2.1.2 hg.2.2.1 ht0 h _ _).2.2.2 (by simp only [nu]; omega)
  have hcs : cornerSh δ T T' p w = ((nSh ((D.s.atP p).ιE t) : ℕ) : (D.s.atP p).Ep) := by
    unfold cornerSh; rw [if_neg hD, hz, hcl']

  have htt : (D.s.atP p).ιE t * (D.s.atP p).ιE t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ ht0, map_one]
  have hc : ∃ k : Fin 3, IsUnit ((D.s.atP p).ιE t + (((k : Fin 3) : ℕ) : (D.s.atP p).Ep)) :=
    ⟨0, by simpa using IsUnit.of_mul_eq_one _ htt⟩
  set k := hc.choose with hk
  have hku : IsUnit ((D.s.atP p).ιE t + (((k : Fin 3) : ℕ) : (D.s.atP p).Ep)) := hc.choose_spec
  have hnsh : nSh ((D.s.atP p).ιE t) = ((k : Fin 3) : ℕ) := by unfold nSh; rw [dif_pos hc]
  have he : (D.s.atP p).ιE t + (((k : Fin 3) : ℕ) : (D.s.atP p).Ep) =
      (D.s.atP p).ιE (t + (((k : Fin 3) : ℕ) : D.host.E)) := by rw [map_add, map_natCast]
  have hne : t + (((k : Fin 3) : ℕ) : D.host.E) ≠ 0 := by
    intro h0'
    rw [he, h0', map_zero] at hku
    haveI := PI.ProdFormulaE.Base.nontrivial (D.s.atP p)
    exact not_isUnit_zero hku
  have hmem : t ∈ (w.1.map Prod.fst).toFinset := List.mem_toFinset.2 (by rw [hb]; simp)
  obtain ⟨hk1, hk2⟩ := hg.2.2.2 t hmem k hne
  have hsD : (D.s.atP p).split = none := LocModel.split_none_of_agree hA hg.1
  have hR : (M p).R = (D.s.atP p).O := by
    have hRL : (M p).R = (M p).L.O := by simp only [Loc.Model.R, hg.1]
    exact hRL.trans hA.2.2.2.1

  let c' : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a =>
    if a = Fin.last _ then (D.s.atP p).ιE (t + (((k : Fin 3) : ℕ) : D.host.E)) else H.c a
  have hσne : ∀ a, a ≠ Fin.last _ → H.σ a ≠ Fin.last _ := fun a ha h =>
    ha (by rw [← H.σσ a, h]; exact hσl)
  have hinvt : Ring.inverse ((D.s.atP p).ιE (t + (((k : Fin 3) : ℕ) : D.host.E))) =
      (D.s.atP p).ιE ((t + (((k : Fin 3) : ℕ) : D.host.E))⁻¹) := by
    have h1 : (D.s.atP p).ιE (t + (((k : Fin 3) : ℕ) : D.host.E)) *
        (D.s.atP p).ιE ((t + (((k : Fin 3) : ℕ) : D.host.E))⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hne, map_one]
    simpa using LocModel.ring_inverse_pow_eq h1 1
  let H' : Mono (M p).R (modMat δ T T' p w + cornerM p (cornerSh δ T T' p w)) :=
    { σ := H.σ
      c := c'
      σσ := H.σσ
      cσ := fun a => by
        by_cases ha : a = Fin.last _
        · have hs' : H.σ a = Fin.last _ := by rw [ha]; exact hσl
          simp only [c', if_pos hs', if_pos ha]
        · simp only [c', if_neg ha, if_neg (hσne a ha)]; exact H.cσ a
      hc := fun a => by
        by_cases ha : a = Fin.last _
        · simp only [c', if_pos ha]; rw [hR]; exact hk1
        · simp only [c', if_neg ha]; exact H.hc a
      hci := fun a => by
        by_cases ha : a = Fin.last _
        · simp only [c', if_pos ha]; rw [hinvt, hR]; exact hk2
        · simp only [c', if_neg ha]; exact H.hci a
      hcu := fun a => by
        by_cases ha : a = Fin.last _
        · simp only [c', if_pos ha]; rw [← he]; exact hku
        · simp only [c', if_neg ha]; exact H.hcu a
      hW := fun a b => by
        rw [Matrix.add_apply, H.hW]
        simp only [cornerM, Matrix.of_apply, c']
        by_cases ha : a = Fin.last _
        · have hs' : H.σ a = Fin.last _ := by rw [ha]; exact hσl
          by_cases hbl : b = Fin.last _
          · have hb' : b = H.σ a := by rw [hs', hbl]
            rw [if_pos hb', if_pos ⟨ha, hbl⟩, if_pos hb', if_pos ha, ha, hcl, hcl', hcs, hnsh, he]
          · have hb' : ¬ b = H.σ a := by rw [hs']; exact hbl
            rw [if_neg hb', if_neg (show ¬ (a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS) from fun h => hbl h.2),
              if_neg hb', add_zero]
        · rw [if_neg (show ¬ (a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS) from fun h => ha h.1), add_zero]
          by_cases hb' : b = H.σ a
          · rw [if_pos hb', if_pos hb', if_neg ha]
          · rw [if_neg hb', if_neg hb'] }
  exact H'.isGL

theorem local_unram (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D) (hA : ∀ p, Agree δ M p)
    (hg : Good δ M w p) (hψ : ∀ x ∈ (M p).R, (M p).psiR x = 1) (w₀ : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1))
    (hw₀ : modPt δ T T' p w = some w₀) (τ : Option ((M p).Cls D.R.rS)) (O : Set (LsDatumB.MatP D p)) :
    fL M δ T T' p w τ O = (if O = x0L M δ T T' p w ∧ τ = LocModel.thTriv M p then 1 else 0) ∧
      gL M δ T T' p w τ O = (if O = x0L M δ T T' p w ∧ τ = LocModel.thTriv M p then 1 else 0) := by
  set H := monoW T T' w p (hA p) hg
  have hint := orb_int T T' w p (hA p) hg w₀ hw₀

  have hcls : ∀ O, IsLCls M δ T T' p w O → O = x0L M δ T T' p w := by
    rintro O ⟨Y, hYi, ⟨w₀', hw₀', xy, hxy⟩, rfl⟩
    rw [hw₀] at hw₀'
    cases hw₀'
    obtain ⟨h1, h2⟩ := hint xy.1 xy.2 (by rw [← hxy]; exact hYi)
    exact kkOrb_eq p (isLoU_of (Formalism.MainNotions.LocalModelPeriodLattices.isLowUni_uLow _)) h1
      (isUpU_of (Formalism.MainNotions.LocalModelPeriodLattices.isUpUni_uUp _ _)) h2 hxy
  have hx0 : IsLCls M δ T T' p w (x0L M δ T T' p w) :=
    ⟨modMat δ T T' p w, H.int, ⟨w₀, hw₀, (0, 0), by rw [uLow_zero, uUp_zero, Matrix.one_mul, Matrix.mul_one]⟩, rfl⟩

  obtain ⟨hY0i, ⟨w₀', hw₀', xy0, hxy0⟩, hO0⟩ : IntP M p (repL M δ T T' p w (x0L M δ T T' p w)) ∧
      InOrbP δ T T' p w (repL M δ T T' p w (x0L M δ T T' p w)) ∧
      x0L M δ T T' p w = kkOrb M p (repL M δ T T' p w (x0L M δ T T' p w)) := by
    have := hx0.choose_spec
    unfold repL
    rw [dif_pos hx0]
    exact this
  rw [hw₀] at hw₀'
  cases hw₀'
  set Y0 := repL M δ T T' p w (x0L M δ T T' p w) with hY0
  have hsD : (D.s.atP p).split = none := LocModel.split_none_of_agree (hA p) hg.1
  have hd : dfac M δ T T' p w = 1 := by unfold dfac; rw [hsD]

  have hex : ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep),
      Y0 = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2 := ⟨xy0, hxy0⟩
  have hph : phL M δ T T' p w Y0 = 1 := by
    unfold phL
    rw [hw₀]
    simp only
    rw [dif_pos hex, hd, one_mul]
    obtain ⟨h1, h2⟩ := hint _ _ (by rw [← hex.choose_spec]; exact hY0i)
    apply hψ
    refine (M p).R.add_mem ?_ ?_
    · unfold Loc.simpleLow
      exact (M p).R.sum_mem fun a _ => (M p).R.sum_mem fun b _ => by
        split_ifs
        · exact h1 a b
        · exact (M p).R.zero_mem
    · unfold Loc.simpleUp
      exact (M p).R.sum_mem fun a _ => (M p).R.sum_mem fun b _ => by
        split_ifs
        · exact h2 a b
        · exact (M p).R.zero_mem

  have hOK := (hA p).1
  haveI := hOK.haar.sf
  have hwt : wtL M δ T T' p w Y0 = 1 := by
    unfold wtL
    rw [hw₀]
    simp only
    have hset : {xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep) |
        Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2 ∈ kkOrb M p Y0} =
        (Set.univ.pi fun _ => ((M p).R : Set (D.s.atP p).Ep)) ×ˢ
          (Set.univ.pi fun _ => ((M p).R : Set (D.s.atP p).Ep)) := by
      ext ⟨x, y⟩
      simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ_pi, SetLike.mem_coe]
      rw [← hO0]
      constructor
      · rintro ⟨l, ρ, hl, hρ, he⟩
        have hYint : ∀ i j, (Loc.uLow x * modMat δ T T' p w * Loc.uUp w₀ y) i j ∈ (M p).R := by
          rw [he]; exact int_mul _ (int_mul _ hl.2.2 H.int) hρ.2.2
        obtain ⟨h1, h2⟩ := hint x y hYint
        refine ⟨fun i => ?_, fun i => ?_⟩
        · have := h1 i.1.1 i.1.2
          simp only [Loc.uLow, if_neg (ne_of_gt i.2), dif_pos i.2] at this
          exact this
        · have := h2 i.1.1 i.1.2
          simp only [Loc.uUp, if_neg (ne_of_lt i.2.1), dif_pos i.2] at this
          exact this
      · rintro ⟨hx, hy⟩
        have hL := isLoU_of (Formalism.MainNotions.LocalModelPeriodLattices.isLowUni_uLow x)
        have hN := isUpU_of (Formalism.MainNotions.LocalModelPeriodLattices.isUpUni_uUp w₀ y)
        refine ⟨Loc.uLow x, Loc.uUp w₀ y, ⟨hL.1, hL.2, fun a b => ?_⟩, ⟨hN.1, hN.2, fun a b => ?_⟩, rfl⟩
        · unfold Loc.uLow
          split_ifs
          · exact (M p).R.one_mem
          · exact hx _
          · exact (M p).R.zero_mem
        · unfold Loc.uUp
          split_ifs
          · exact (M p).R.one_mem
          · exact hy _
          · exact (M p).R.zero_mem
    rw [hset, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
    simp [hOK.haar.volR]

  have hth : thL M δ T T' p w Y0 = some (LocModel.trivCls (M p) D.R.rS) := by
    obtain ⟨h1, h2⟩ := hint _ _ (by rw [← hxy0]; exact hY0i)
    have hL := isLoU_of (Formalism.MainNotions.LocalModelPeriodLattices.isLowUni_uLow xy0.1)
    have hN := isUpU_of (Formalism.MainNotions.LocalModelPeriodLattices.isUpUni_uUp w₀ xy0.2)
    unfold thL
    apply clsOf_triv
    have e : Y0 + (Matrix.of fun a b => if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then
        cornerSh δ T T' p w else 0) =
        Loc.uLow xy0.1 * (modMat δ T T' p w + cornerM p (cornerSh δ T T' p w)) * Loc.uUp w₀ xy0.2 := by
      rw [Matrix.mul_add, Matrix.add_mul, loU_corner p _ hL hN, ← hxy0]
      rfl
    rw [e]
    exact isGL_mul _ (isGL_mul _ (isGL_of_det_one _ h1 (det_loU hL)) (shift_isGL T T' w p (hA p) hg))
      (isGL_of_det_one _ h2 (det_upU hN))

  have hnIso : ∀ τ : Option ((M p).Cls D.R.rS),
      (nIsoO M p τ (some (LocModel.trivCls (M p) D.R.rS)) : ℂ) = if τ = LocModel.thTriv M p then 1 else 0 := by
    intro τ
    cases τ with
    | none => simp [nIsoO, LocModel.thTriv]
    | some c =>
      simp only [nIsoO, LocModel.thTriv, Option.some.injEq]
      haveI hT : Subsingleton ((M p).Cok (Quotient.out (LocModel.trivCls (M p) D.R.rS))) :=
        (LocModel.sub_iff_triv (M p) _).2 (Quotient.out_eq (s := (M p).isoSetoid D.R.rS) _)
      by_cases hc : c = LocModel.trivCls (M p) D.R.rS
      · rw [if_pos hc, hc, LocModel.nIso_self_eq_one (M p) _ hT, Nat.cast_one]
      · rw [if_neg hc, Nat.cast_eq_zero]
        unfold Loc.Model.nIso
        rw [Nat.card_eq_zero]
        refine Or.inl ⟨fun φ => hc ?_⟩
        haveI : Subsingleton ((M p).Cok (Quotient.out c)) := φ.1.injective.subsingleton
        exact (Quotient.out_eq (s := (M p).isoSetoid D.R.rS) c).symm.trans
          ((LocModel.sub_iff_triv (M p) (Quotient.out c)).1 this)
  by_cases hO : O = x0L M δ T T' p w
  · subst hO
    constructor
    · unfold fL
      rw [if_pos hx0, hph, hwt, hth, hnIso]
      by_cases hτ : τ = LocModel.thTriv M p <;> simp [hτ]
    · unfold gL
      by_cases hτ : τ = LocModel.thTriv M p
      · rw [if_pos ⟨hx0, by rw [hth, hτ]; rfl⟩, hph, hwt, if_pos ⟨rfl, hτ⟩]; simp
      · rw [if_neg (fun h => hτ (by rw [← h.2, hth]; rfl)), if_neg (fun h => hτ h.2)]
  · have hn : ¬ IsLCls M δ T T' p w O := fun h => hO (hcls O h)
    constructor
    · unfold fL; rw [if_neg hn, if_neg (fun h => hO h.1)]
    · unfold gL; rw [if_neg (fun h => hn h.1), if_neg (fun h => hO h.1)]

theorem locUnram_triv (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) :
    LocUnram M δ u u' (LocModel.thTriv M) := by
  intro w _
  have hall := LocModel.good_cofinite δ M hA (w.1.map Prod.fst).toFinset
  rw [Filter.eventually_cofinite] at hall
  refine ⟨hall.toFinset, fun p hp => ?_⟩
  have hg : Good δ M w p := not_not.1 (fun h => hp (hall.mem_toFinset.2 h))
  obtain ⟨hψ, w₀, hw₀, -⟩ := LocModel.good_place (D.mem u).A.T (D.mem u').A.T w p (hA p) hg.1 hg.2.1.1 hg.2.1.2
    hg.2.2.1 fun b hb k hk => hg.2.2.2 b.1 (List.mem_toFinset.2 (List.mem_map.2 ⟨b, hb, rfl⟩)) k hk
  exact ⟨LocModel.autP_thTriv M p, fun τ O => local_unram _ _ w p hA hg hψ w₀ hw₀ τ O⟩

end Main

end Formalism.L2.SG.Pf.LocUnramB

namespace Formalism.L2.SG.Pf.LocUnramB

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups MeasureTheory Formalism.L2.SG.Pf.AtPt
open Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.MainNotions.S.Lat
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Restr

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

theorem permSign_mul_self₂ (p : PlF D) : LsDatumB.sgnP p * LsDatumB.sgnP p = 1 := by
  unfold LsDatumB.sgnP
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← mul_pow]
  simp

theorem corner_sgn (p : PlF D) (c : (D.s.atP p).Ep) : cornerM p c * LsDatumB.sgnP p = cornerM p c := by
  ext a b
  rw [LsDatumB.sgnP, Matrix.mul_diagonal]
  simp only [cornerM, Matrix.of_apply]
  split_ifs with h
  · rw [h.2, Fin.val_last, Nat.sub_self, pow_zero, mul_one]
  · rw [zero_mul]

theorem isGL_sgn (p : PlF D) : IsGL (M p).R (LsDatumB.sgnP p) := by
  have hint : ∀ i j, LsDatumB.sgnP p i j ∈ (M p).R := fun i j => by
    unfold LsDatumB.sgnP
    rw [Matrix.diagonal_apply]
    split_ifs
    · exact Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _
    · exact Subring.zero_mem _
  exact ⟨hint, LsDatumB.sgnP p, hint, permSign_mul_self₂ p⟩

theorem one_intLow (p : PlF D) : TieN.IntLow (M p) (1 : LsDatumB.MatP D p) :=
  ⟨fun a => Matrix.one_apply_eq a, fun a b h => Matrix.one_apply_ne (ne_of_lt h),
    fun a b => by rw [Matrix.one_apply]; split_ifs; exacts [Subring.one_mem _, Subring.zero_mem _]⟩

theorem one_intUp (p : PlF D) : TieN.IntUp (M p) (1 : LsDatumB.MatP D p) :=
  ⟨fun a => Matrix.one_apply_eq a, fun a b h => Matrix.one_apply_ne (ne_of_gt h),
    fun a b => by rw [Matrix.one_apply]; split_ifs; exacts [Subring.one_mem _, Subring.zero_mem _]⟩

end Restr

end Formalism.L2.SG.Pf.LocUnramB

namespace Formalism.L2.SG.Pf

theorem locUnram_holds {D : Formalism.BasicNotions.D7} {δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp}
    {M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) (u u' : D.what₂.Word) :
    Formalism.L2.SG.LsDatumB.LocUnram M δ u u' (LocModel.thTriv M) :=
  LocUnramB.locUnram_triv hA u u'

end Formalism.L2.SG.Pf
