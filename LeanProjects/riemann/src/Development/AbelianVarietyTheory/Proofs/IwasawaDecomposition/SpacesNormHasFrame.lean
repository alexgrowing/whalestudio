import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSingleSingle

noncomputable section

namespace GlobalTheory.Mem.DiagSp

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField IsDedekindDomain
open scoped TensorProduct

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem signSpace_cut_eq (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N N' p q : ℕ)
    (hN : N = N') (hp : p ≤ N) (hq : N - p = q) :
    signSpace hstar N (cut N p) = stdSpace hstar N' (fun i => decide (p ≤ i.1)) p q := by
  subst hN hq
  rw [signSpace, card_cut_false N p hp, card_cut_true N p hp]
  rfl

theorem signSpace_false_eq (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ) :
    signSpace hstar N (fun _ => false) = stdSpace hstar N (fun _ => false) N 0 := by
  simp [signSpace]

def planeVec (N n h : ℕ) (hN : n + 2 * h ≤ N) (a b : E) (i : Fin h) : Fin N → E :=
  Pi.single (⟨n + i, by omega⟩ : Fin N) a + Pi.single (⟨n + h + i, by omega⟩ : Fin N) b

theorem planeVec_planeVec (N n h p : ℕ) (hN : n + 2 * h ≤ N) (hp : p = n + h) (a b c d : E) (i j : Fin h) :
    diagForm N (cut N p) (planeVec N n h hN a b i) (planeVec N n h hN c d j) =
      if i = j then star a * c - star b * d else 0 := by
  subst hp
  have hi := i.isLt
  have hj := j.isLt
  have c1 : cut N (n + h) ⟨n + i, by omega⟩ = false := by simp [cut]
  have c2 : cut N (n + h) ⟨n + h + i, by omega⟩ = true := by simp [cut]
  simp only [planeVec, map_add, LinearMap.add_apply, diag_single_single, c1, c2]
  have e1 : ¬ (n + (i : ℕ) = n + h + j) := by omega
  have e2 : ¬ (n + h + (i : ℕ) = n + j) := by omega
  rw [if_neg e1, if_neg e2]
  by_cases hij : i = j
  · subst hij
    simp [sgn, sub_eq_add_neg]
  · have h' : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
    have e3 : ¬ (n + (i : ℕ) = n + j) := by omega
    have e4 : ¬ (n + h + (i : ℕ) = n + h + j) := by omega
    rw [if_neg e3, if_neg e4, if_neg hij]
    simp

theorem ext_planeVec (N n h : ℕ) (hN : n + 2 * h ≤ N) (neg : Fin N → Bool) (x : Fin n → E) (a b : E)
    (i : Fin h) : diagForm N neg (extTo n N x) (planeVec N n h hN a b i) = 0 := by
  rw [planeVec, map_add, diag_ext_single, diag_ext_single, add_zero]
  · simp only; omega
  · simp only; omega

theorem single_planeVec (N n h : ℕ) (hN : n + 2 * h ≤ N) (neg : Fin N → Bool) (l : Fin N)
    (hl : n + 2 * h ≤ l) (c a b : E) (i : Fin h) :
    diagForm N neg (Pi.single l c) (planeVec N n h hN a b i) = 0 := by
  have hi := i.isLt
  rw [planeVec, map_add, diag_single_single, diag_single_single, if_neg, if_neg, add_zero]
  · simp only; omega
  · simp only; omega

end General

section Main

variable (R : Ranks)

theorem rankY_eq_N_add (j : ℕ) (hj : j < R.m) : R.rankY j = R.N j + (R.m - 1 - j) := by
  simp only [Ranks.rankY, Ranks.r, Ranks.N, mul_add]
  omega

theorem pY_eq_N_add (j : ℕ) (hj : j < R.m) : pY R j = R.N j + (R.m - 1 - j) / 2 := by
  have := rankY_eq_N_add R j hj
  simp only [pY]
  omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)

include hpz in
theorem top_line_norm :
    diagForm (R.N R.m) (fun _ => false)
      (Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) pz)
      (Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) pz) = (T : E) := by
  refine (diag_single_single _ (fun _ => false) _ _ pz pz).trans ?_
  rw [if_pos rfl, ← hpz]
  simp [sgn]

def spacesNorm : Spaces R F E :=
  { spacesStd R cm T hT pz hpz (fun _ => false) with
    z := Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) pz
    z_anis := ne_of_eq_of_ne (top_line_norm R T pz hpz) (Nat.cast_ne_zero.2 hT.ne_zero)
    z_orth := fun x => diag_ext_single _ _ (fun _ => false) x _ pz le_rfl }

theorem spacesNorm_z_norm :
    ((spacesNorm R cm T hT pz hpz).X R.m).hT (spacesNorm R cm T hT pz hpz).z (spacesNorm R cm T hT pz hpz).z =
      ((spacesNorm R cm T hT pz hpz).T : E) :=
  top_line_norm R T pz hpz

theorem spacesNorm_hasFrame (j : ℕ) (hj : j < R.m) : HasHyperbolicAuxiliaryFrame (spacesNorm R cm T hT pz hpz) j := by
  have h1 := rankY_eq_N_add R j hj
  have h2 := pY_eq_N_add R j hj
  have hN : R.N j + 2 * ((R.m - 1 - j) / 2) ≤ R.rankY j := by omega
  refine ⟨planeVec _ _ _ hN (1 : E) 1, planeVec _ _ _ hN (1 / 2 : E) (-(1 / 2)),
    fun i i' => (planeVec_planeVec _ _ _ _ hN h2 _ _ _ _ i i').trans (by simp),
    fun i i' => (planeVec_planeVec _ _ _ _ hN h2 _ _ _ _ i i').trans (by simp),
    fun i i' => (planeVec_planeVec _ _ _ _ hN h2 _ _ _ _ i i').trans ?_,
    fun i x => ⟨ext_planeVec _ _ _ hN (cut _ (pY R j)) x _ _ i, ext_planeVec _ _ _ hN (cut _ (pY R j)) x _ _ i⟩,
    fun he => ?_⟩
  · split_ifs
    · rw [star_one]; norm_num
    · rfl
  · obtain ⟨a, ha⟩ := he
    obtain ⟨b, hb⟩ := R.m_even
    have hl : R.N j + 2 * ((R.m - 1 - j) / 2) < R.rankY j := by omega
    refine ⟨(Pi.single (⟨_, hl⟩ : Fin (R.rankY j)) pz : Fin (R.rankY j) → E), ?_,
      fun x => diag_ext_single _ _ (cut _ (pY R j)) x _ pz (Nat.le_add_right _ _),
      fun i => ⟨single_planeVec _ _ _ hN (cut _ (pY R j)) _ le_rfl _ _ _ i,
        single_planeVec _ _ _ hN (cut _ (pY R j)) _ le_rfl _ _ _ i⟩⟩
    refine (diag_single_single _ (cut _ (pY R j)) _ _ pz pz).trans ?_
    have c : cut (R.rankY j) (pY R j) ⟨_, hl⟩ = true := by
      simp only [cut, decide_eq_true_eq]; omega
    rw [if_pos rfl, c]
    change _ = -(T : E)
    rw [← hpz]
    simp [sgn]

theorem spacesNorm_coord :
    ∃ hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x),
      (∀ j, (spacesNorm R cm T hT pz hpz).X j = posSpace hstar (R.N j)) ∧
      (spacesNorm R cm T hT pz hpz).X' = posSpace hstar R.rankX' ∧
      (∀ j, (spacesNorm R cm T hT pz hpz).Y j =
        stdSpace hstar (R.rankY j) (fun i => decide ((sigYD R j).1 ≤ i.1)) (sigYD R j).1 (sigYD R j).2) ∧
      (∀ j, 1 ≤ j → j ≤ R.m → (spacesNorm R cm T hT pz hpz).W j =
        stdSpace hstar R.r (fun i => decide ((R.sigW j).1 ≤ i.1)) (R.sigW j).1 (R.sigW j).2) ∧
      ∀ j, (spacesNorm R cm T hT pz hpz).V j =
        stdSpace hstar R.nV (fun _ => (spacesNorm R cm T hT pz hpz).Vneg j)
          (if (spacesNorm R cm T hT pz hpz).Vneg j then 0 else R.nV)
          (if (spacesNorm R cm T hT pz hpz).Vneg j then R.nV else 0) := by
  refine ⟨star_isIntegral, fun _ => rfl, rfl, fun j => ?_, fun j h1 h2 => ?_, fun j => ?_⟩
  · exact signSpace_cut_eq _ _ _ _ _ rfl (Nat.sub_le _ _) (sub_pY R j)
  · have h : R.rankY 0 = R.k + R.m - 1 := by simp [Ranks.rankY, Ranks.r]
    refine signSpace_cut_eq _ (R.rankY 0) R.r (R.k + j - 1) (R.m - j) h ?_ ?_ <;> omega
  · exact signSpace_false_eq _ _

theorem spacesNorm_T : (spacesNorm R cm T hT pz hpz).T = T := rfl

theorem spacesNorm_Vneg (j : ℕ) : (spacesNorm R cm T hT pz hpz).Vneg j = false := rfl

theorem spacesNorm_Y_sig (j : ℕ) (τ : E →+* ℂ) : ((spacesNorm R cm T hT pz hpz).Y j).sig τ = sigYD R j :=
  spY_sig R j τ

end Main

end GlobalTheory.Mem.DiagSp

end
