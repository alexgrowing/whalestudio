import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgePlace
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WittOrthonormalBasis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerFourthCondition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Bridge

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting
open Formalism.L2.SG.RealObj.InfCut

section Pt

variable {K : Type} [Field K] (σ : K →+* ℂ) (κ : ℂ) (r : ℕ)

def Af (x : ℕ) : ℂ := star (κ ^ (r - x))

def Bf (y : ℕ) : ℂ := (-1) ^ (r - y) * κ ^ (r - y)

def blkF (x y : ℕ) : ℂ := (-1) ^ ((r - x) + (r - y)) * κ ^ ((r - x) + (r - y))

theorem AB_eq (hκ : star κ = -κ) (x y : ℕ) : Af κ r x * Bf κ r y = blkF κ r x y := by
  unfold Af Bf blkF
  rw [star_pow, hκ, neg_pow, pow_add, pow_add]
  ring

def lptOf : ℕ → List (K × ℕ) → Formalism.FourierDecayAlt.C.LPt
  | _, [] => []
  | o, (t, s) :: rest => (s, blkF κ r o (o + s - 1) * σ t) :: lptOf (o + s) rest

theorem ptEntry_lptOf (hκ : star κ = -κ) : ∀ (L : List (K × ℕ)) (o i j : ℕ),
    o + (L.map Prod.snd).sum ≤ r + 1 → i < (L.map Prod.snd).sum → j < (L.map Prod.snd).sum →
    Formalism.FourierDecayAlt.D.ptEntry (lptOf σ κ r o L) i j = Af κ r (o + i) * σ (Formalism.MainNotions.S.ptEntry L i j) * Bf κ r (o + j)
  | [], o, i, j, _, hi, _ => by simp at hi
  | (t, s) :: rest, o, i, j, ho, hi, hj => by
    simp only [List.map_cons, List.sum_cons] at ho hi hj
    simp only [lptOf, Formalism.FourierDecayAlt.D.ptEntry, Formalism.MainNotions.S.ptEntry]
    by_cases h1 : i < s ∧ j < s
    · rw [if_pos h1, if_pos h1]
      by_cases h2 : i + j + 1 = s
      · rw [if_pos h2, if_pos h2, show Af κ r (o + i) * σ t * Bf κ r (o + j) =
          (Af κ r (o + i) * Bf κ r (o + j)) * σ t by ring, AB_eq κ r hκ]
        unfold blkF
        have he : (r - (o + i)) + (r - (o + j)) = (r - o) + (r - (o + s - 1)) := by omega
        rw [he]
      · rw [if_neg h2, if_neg h2, map_zero, mul_zero, zero_mul]
    · rw [if_neg h1, if_neg h1]
      by_cases h3 : s ≤ i ∧ s ≤ j
      · rw [if_pos h3, if_pos h3, ptEntry_lptOf hκ rest (o + s) (i - s) (j - s) (by omega) (by omega) (by omega)]
        have e1 : o + s + (i - s) = o + i := by omega
        have e2 : o + s + (j - s) = o + j := by omega
        rw [e1, e2]
      · rw [if_neg h3, if_neg h3, map_zero, mul_zero, zero_mul]

end Pt

section Model

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

end Model

section PointMat

variable {K : Type} [Field K] (σ : K →+* ℂ) (κ : ℂ) (r : ℕ)

theorem ptMatN_lptOf (hκ : star κ = -κ) (w : Formalism.MainNotions.S.Point K (r + 1)) :
    Formalism.FourierDecayAlt.D.ptMatN (lptOf σ κ r 0 w.1) (r + 1) =
      Matrix.diagonal (fun x : Fin (r + 1) => Af κ r x) * (Formalism.MainNotions.S.ptMat w).map σ *
        Matrix.diagonal (fun y : Fin (r + 1) => Bf κ r y) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
  have hs := w.2.2
  have ha := a.isLt
  have hb := b.isLt
  have key := ptEntry_lptOf σ κ r hκ w.1 0 a b (by omega) (by omega) (by omega)
  simp only [zero_add] at key
  unfold Formalism.FourierDecayAlt.D.ptMatN Formalism.MainNotions.S.ptMat
  exact key

theorem lptOf_fst : ∀ (L : List (K × ℕ)) (o : ℕ), (lptOf σ κ r o L).map Prod.fst = L.map Prod.snd
  | [], _ => rfl
  | (t, s) :: rest, o => by simp [lptOf, lptOf_fst rest (o + s)]

theorem blkF_ne (hκ0 : κ ≠ 0) (x y : ℕ) : blkF κ r x y ≠ 0 := by
  unfold blkF
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hκ0)

theorem lptOf_mem (hκ0 : κ ≠ 0) : ∀ (L : List (K × ℕ)) (o : ℕ), (∀ b ∈ L, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    ∀ b ∈ lptOf σ κ r o L, 1 ≤ b.1 ∧ b.2 ≠ 0
  | [], _, _, b, hb => by simp [lptOf] at hb
  | (t, s) :: rest, o, hL, b, hb => by
    simp only [lptOf, List.mem_cons] at hb
    rcases hb with rfl | hb
    · have h := hL (t, s) (by simp)
      exact ⟨h.2, mul_ne_zero (blkF_ne κ r hκ0 _ _) ((map_ne_zero σ).mpr h.1)⟩
    · exact lptOf_mem hκ0 rest (o + s) (fun b hb => hL b (List.mem_cons_of_mem _ hb)) b hb

theorem isLocPt_lptOf (hκ0 : κ ≠ 0) (w : Formalism.MainNotions.S.Point K (r + 1)) :
    Formalism.FourierDecayAlt.D.IsLocPt (lptOf σ κ r 0 w.1) (r + 1) :=
  ⟨lptOf_mem σ κ r hκ0 w.1 0 w.2.1, by unfold Formalism.FourierDecayAlt.D.ptSize; rw [lptOf_fst]; exact w.2.2⟩

theorem G_diag (Y : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (a b : Fin (r + 1) → ℂ) (TT : ℝ)
    (hl : ‖a (Fin.last r)‖ * ‖b (Fin.last r)‖ = 1) :
    ‖RealObj.Dl (Matrix.diagonal a * Y * Matrix.diagonal b) (r + 1)‖ ^ 2 -
        TT * ‖RealObj.Dl (Matrix.diagonal a * Y * Matrix.diagonal b) r‖ ^ 2 =
      (‖∏ i : Fin r, a (Fin.castLE (Nat.le_succ r) i)‖ * ‖∏ i : Fin r, b (Fin.castLE (Nat.le_succ r) i)‖) ^ 2 *
        (‖RealObj.Dl Y (r + 1)‖ ^ 2 - TT * ‖RealObj.Dl Y r‖ ^ 2) := by
  have key : ∀ (l : ℕ) (h : l ≤ r + 1), RealObj.Dl (Matrix.diagonal a * Y * Matrix.diagonal b) l =
      (∏ i : Fin l, a (Fin.castLE h i)) * RealObj.Dl Y l * ∏ i : Fin l, b (Fin.castLE h i) := by
    intro l h
    unfold RealObj.Dl
    rw [dif_pos h, dif_pos h]
    have e : (Matrix.diagonal a * Y * Matrix.diagonal b).submatrix (Fin.castLE h) (Fin.castLE h) =
        Matrix.diagonal (fun i => a (Fin.castLE h i)) * Y.submatrix (Fin.castLE h) (Fin.castLE h) *
          Matrix.diagonal (fun i => b (Fin.castLE h i)) := by
      ext i j
      simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  rw [key (r + 1) le_rfl, key r (Nat.le_succ r), Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  have ea : ∀ i : Fin r, Fin.castLE (le_refl (r + 1)) (Fin.castSucc i) = Fin.castLE (Nat.le_succ r) i :=
    fun i => Fin.ext rfl
  have el : Fin.castLE (le_refl (r + 1)) (Fin.last r) = Fin.last r := Fin.ext rfl
  simp only [ea, el, norm_mul]
  have hx : ‖a (Fin.last r)‖ ^ 2 * ‖b (Fin.last r)‖ ^ 2 = 1 := by
    rw [← mul_pow, hl, one_pow]
  linear_combination (‖∏ i : Fin r, a (Fin.castLE (Nat.le_succ r) i)‖ * ‖RealObj.Dl Y (r + 1)‖ *
    ‖∏ i : Fin r, b (Fin.castLE (Nat.le_succ r) i)‖) ^ 2 * hx

end PointMat

section NX

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

def IsXv (v : Fin (2 * r + k + 1) → ℂ) : Prop := ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0

theorem isXv_eq (v : Fin (2 * r + k + 1) → ℂ) (hv : IsXv v) :
    v = ∑ a : Fin r, v (Formalism.QuantumDeterminants.eI k r a) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, Formalism.QuantumDeterminants.bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases h : i.val < r
  · rw [Finset.sum_eq_single ⟨i.val, h⟩]
    · have e : i = Formalism.QuantumDeterminants.eI k r ⟨i.val, h⟩ := Fin.ext rfl
      rw [if_pos e, ← e]
    · intro b _ hb
      rw [if_neg]
      intro hh
      apply hb
      have hv' := congrArg Fin.val hh
      exact Fin.ext (by simp [Formalism.QuantumDeterminants.eI] at hv' ⊢; omega)
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [hv i (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro a _
    rw [if_neg]
    intro hh
    apply h
    rw [hh]
    simp [Formalism.QuantumDeterminants.eI]

def NoXs (v : Fin (2 * r + k + 1) → ℂ) : Prop := ∀ a : Fin r, v (Formalism.QuantumDeterminants.esI k r a) = 0

theorem N_sub_X {M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hM : M ∈ Formalism.QuantumDeterminants.Nset k r)
    (x : Fin (2 * r + k + 1) → ℂ) (hx : NoXs x) : IsXv ((M - 1) *ᵥ x) := by
  unfold IsXv
  intro i hi
  have hx' : ∀ j : Fin (2 * r + k + 1), r + k < j.val → x j = 0 := by
    intro j hj
    have hj2 := j.isLt
    have h0 := hx ⟨2 * r + k - j.val, by omega⟩
    have e : Formalism.QuantumDeterminants.esI k r ⟨2 * r + k - j.val, by omega⟩ = j :=
      Fin.ext (by simp [Formalism.QuantumDeterminants.esI]; omega)
    rwa [e] at h0
  have hM1 : ∀ j : Fin (2 * r + k + 1), j.val ≤ r + k → M i j = if i = j then 1 else 0 := by
    intro j hj
    by_cases hjr : j.val < r
    · have e : Formalism.QuantumDeterminants.eI k r ⟨j.val, hjr⟩ = j := Fin.ext rfl
      have h0 := hM.2.1 ⟨j.val, hjr⟩ i (by simp; omega)
      rwa [e] at h0
    · exact hM.2.2 i j (by omega) hj hi
  have key : ∀ j, M i j * x j = if i = j then x i else 0 := by
    intro j
    by_cases hj : j.val ≤ r + k
    · rw [hM1 j hj]
      split_ifs with h
      · rw [h]; ring
      · ring
    · rw [hx' j (by omega)]
      split_ifs with h
      · rw [h, hx' j (by omega)]; ring
      · ring
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, sub_eq_zero]
  show ∑ j, M i j * x j = x i
  simp_rw [key]
  simp

end NX

section NX2

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

theorem Qi_noXs (hT : TrHyp F Qm Qim c) (w : Fin n → ℂ) (hw : ∀ a, hJ ε (F.e a) w = 0) : NoXs (Qim *ᵥ w) := by
  intro a
  have ha := a.isLt
  have hrow : ∀ j, Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.eI k r a) j = if j = Formalism.QuantumDeterminants.esI k r a then 1 else 0 := by
    intro j
    have hj := j.isLt
    simp only [Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.eI, Formalism.QuantumDeterminants.esI, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | rfl | omega
  have h1 : (Formalism.QuantumDeterminants.Hpk k r *ᵥ (Qim *ᵥ w)) (Formalism.QuantumDeterminants.eI k r a) = (Qim *ᵥ w) (Formalism.QuantumDeterminants.esI k r a) := by
    show ∑ j, Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.eI k r a) j * (Qim *ᵥ w) j = _
    simp_rw [hrow]
    simp
  have h3 : Formalism.L2.SG.HidaSetting.hJ ε (Qm *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) w = 0 := by
    have hw' := hw a
    unfold Formalism.L2.SG.HidaSetting.hJ at hw' ⊢
    rw [hT.he a]
    simp [star_smul, hw']
  have h4 : Formalism.L2.SG.HidaSetting.hJ ε (Qm *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) w =
      ((Qmᴴ * Formalism.REAL.Jm ε) *ᵥ w) (Formalism.QuantumDeterminants.eI k r a) := by
    unfold Formalism.L2.SG.HidaSetting.hJ
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
    simp [Formalism.QuantumDeterminants.bvec, dotProduct, Pi.single_apply, apply_ite star]
  show (Qim *ᵥ w) (Formalism.QuantumDeterminants.esI k r a) = 0
  rw [← h1, ← hT.hH, Matrix.mulVec_mulVec, Matrix.mul_assoc (Qmᴴ * Formalism.REAL.Jm ε) Qm Qim, hT.h2, Matrix.mul_one, ← h4, h3]

theorem Q_X (hT : TrHyp F Qm Qim c) (v : Fin (2 * r + k + 1) → ℂ) (hv : IsXv v) :
    Qm *ᵥ v ∈ Submodule.span ℂ (Set.range F.e) := by
  rw [isXv_eq v hv, Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [Matrix.mulVec_smul, hT.he, smul_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

structure NLike (F : PtRepPf.Fr ε r k) (g : Matrix (Fin n) (Fin n) ℂ) : Prop where
  he : ∀ a, g *ᵥ F.e a = F.e a
  hz : g *ᵥ F.z = F.z
  hy : ∀ y, (∀ a, hJ ε (F.e a) y = 0) → (g - 1) *ᵥ y ∈ Submodule.span ℂ (Set.range F.e)

theorem psiR_of {g : Matrix (Fin n) (Fin n) ℂ} (hg : NLike F g) (gg : ℕ) : Formalism.L2.SG.HidaSetting.psiR ε gg F.e F.fd F.z g = 1 := by
  have h0 : ∀ a, Formalism.L2.SG.HidaSetting.rootCoord ε F.e F.fd F.z g a = 0 := by
    intro a
    unfold Formalism.L2.SG.HidaSetting.rootCoord Formalism.L2.SG.HidaSetting.nxt
    split_ifs with h
    · rw [hg.he, F.fe]
      rw [if_neg]
      intro e; have := congrArg Fin.val e; simp at this
    · rw [hg.hz, F.fz]
  unfold Formalism.L2.SG.HidaSetting.psiR
  simp [h0]

end NX2

section PlaceNC

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F F' : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

theorem delta_GV (hT : TrHyp F Qm Qim c) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε) : Qim * A * Qm ∈ Formalism.FourierDecayAlt.B.GV k r := by
  show (Qim * A * Qm)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Qim * A * Qm) = Formalism.QuantumDeterminants.Hpk k r
  have h2 : Qimᴴ * Qmᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hT.h2, Matrix.conjTranspose_one]
  rw [← hT.hH]
  calc (Qim * A * Qm)ᴴ * (Qmᴴ * Formalism.REAL.Jm ε * Qm) * (Qim * A * Qm)
      = Qmᴴ * (Aᴴ * ((Qimᴴ * Qmᴴ) * (Formalism.REAL.Jm ε * ((Qm * Qim) * (A * Qm))))) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Qmᴴ * ((Aᴴ * Formalism.REAL.Jm ε * A) * Qm) := by
        rw [hT.h2, h2]; simp only [Matrix.one_mul, Matrix.mul_assoc]
    _ = Qmᴴ * Formalism.REAL.Jm ε * Qm := by rw [hA, Matrix.mul_assoc]

theorem tz_Qi' (hT : TrHyp F Qm Qim c) : Formalism.QuantumDeterminants.Tz k r (Qim *ᵥ F.z) = F.T := by
  have hv : Qm *ᵥ (Qim *ᵥ F.z) = F.z := by
    rw [Matrix.mulVec_mulVec, hT.h2, Matrix.one_mulVec]
  unfold Formalism.QuantumDeterminants.Tz Formalism.QuantumDeterminants.herm
  rw [← hT.hH, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hv]
  have hz := F.zz
  unfold Formalism.L2.SG.HidaSetting.hJ at hz
  rw [hz]
  simp

theorem cS_lam {κ : ℂ} (hc : ∀ a : Fin r, c a = κ ^ (r - a.val)) {sc : ℝ} (hsc : sc ≠ 0) (j : Fin (r + 1)) :
    Formalism.L2.SG.Pf.CarrierTop.cS r sc j * lam c sc j = κ ^ (r - j.val) ∧
      star (lam c sc j) * Formalism.L2.SG.Pf.CarrierTop.cS r sc j = star (κ ^ (r - j.val)) := by
  have hsc' : (sc : ℂ) ≠ 0 := by exact_mod_cast hsc
  unfold Formalism.L2.SG.Pf.CarrierTop.cS lam
  by_cases h : j.val < r
  · rw [dif_pos h, hc]
    simp only
    have hp : (sc : ℂ) ^ (r - j.val) ≠ 0 := pow_ne_zero _ hsc'
    have hs : star ((sc : ℂ) ^ (r - j.val)) = (sc : ℂ) ^ (r - j.val) := by
      rw [star_pow, Complex.star_def, Complex.conj_ofReal]
    refine ⟨?_, ?_⟩
    · rw [inv_mul_eq_iff_eq_mul₀ hp]
      ring
    · rw [star_mul', hs, mul_inv_cancel_right₀ hp]
  · rw [dif_neg h]
    have hj : j.val = r := by have := j.isLt; omega
    simp [hj]

end PlaceNC

end Formalism.L2.SG.Pf.Bridge
