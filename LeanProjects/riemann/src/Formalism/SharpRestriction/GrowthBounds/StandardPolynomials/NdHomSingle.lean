import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.StdPolyEq
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TopOddNeEndAny
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.MonomialSumEqProdTensor

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Rig

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X}

def rig0 (L : LvDat C0 CE1 CE2 mu X β) (a0 : Fin (numSeg X.TT) → ℕ) (j0 : Fin (numSeg X.TT)) : MonH X :=
  ∑ j, (rPl L j + Finsupp.single ((topEnd X j, true), 0) (segAPlus X.TT X.aT j - (β j).oPlus - usedX X β a0 j0 (rot _ j)))

def rig (L : LvDat C0 CE1 CE2 mu X β) (a0 : Fin (numSeg X.TT) → ℕ) (j0 : Fin (numSeg X.TT)) : MonH X :=
  rig0 L a0 j0 + Finsupp.single ((topStart X j0, true), 0) X.c

theorem ndHom_single (v : VarH X) (n : ℕ) : ndHom X (Finsupp.single v n) = n * wN X v := by
  rw [← Finsupp.smul_single_one, map_nsmul, smul_eq_mul]
  congr 1
  show degUS (hhLetters X.TT) 1 (Finsupp.single v 1) = wN X v
  rw [Formalism.MainNotions.LemmaBAlt.degUS_single]
  rfl

theorem nd_rig (L : LvDat C0 CE1 CE2 mu X β) (a0 : Fin (numSeg X.TT) → ℕ) (j0 : Fin (numSeg X.TT)) :
    ndM X (rig L a0 j0) = 0 := by
  show ndHom X (rig L a0 j0) = 0
  unfold rig rig0 rPl
  simp only [map_add, map_sum, ndHom_single, normal_weight_vector_zero_eq_zero, wN_covS, mul_zero, Finset.sum_const_zero, add_zero]

theorem std_eq (O : Type) [CommRing O] [IsDomain O] (L : LvDat C0 CE1 CE2 mu X β) (a0 : Fin (numSeg X.TT) → ℕ)
    (j0 : Fin (numSeg X.TT))
    (hsg : ∀ j (i : Fin (segS X.TT j)), ¬ (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma → (β j).sg i = 0)
    (hroom : ∀ j, usedX X β a0 j0 (rot _ j) ≤ segAPlus X.TT X.aT j - (β j).oPlus)
    (Std : MonH X) (hStd : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j) :
    Std = rig L a0 j0 + ((∑ j, (Finsupp.single ((topStart X j, true), 0) ((X.seg C0 CE1 CE2 j).Qj X.p * a0 j) +
      zPart C0 CE1 CE2 X β j)) + ∑ j, bMk C0 CE1 CE2 X β j) := by
  classical
  have h1 : Std = ∑ j, stdE L j := by
    have : (monomial Std (1 : KK O) : RHH O X) = monomial (∑ j, stdE L j) 1 := by
      rw [hStd, monomial_sum_one]
      exact Finset.prod_congr rfl fun j _ => stdPoly_eq O L j (hsg j)
    exact monomial_left_injective (one_ne_zero) this
  rw [h1]
  set u1 : Fin (numSeg X.TT) → ℕ := fun j => X.p ^ segG X.TT j * (∑ i : Fin (segS X.TT j), (β j).sg i) +
      (∑ i : Fin (segS X.TT j), X.p ^ (segDists X.TT j).get i * ((∑ c : Fin X.m, (β j).rz i c.succ) + (β j).ry i 0)) +
      X.c * (X.m * (X.p ^ segG X.TT j - 1)) with hu1
  have hb : ∀ j, bMk C0 CE1 CE2 X β j = Finsupp.single ((topStart X j, true), 0) (u1 j) + nPart C0 CE1 CE2 X β j := by
    intro j
    unfold bMk nPart
    rw [add_assoc]
  have hus : ∀ j, usedX X β a0 j0 j = (X.seg C0 CE1 CE2 j).Qj X.p * a0 j + u1 j + (if j = j0 then X.c else 0) := by
    intro j
    unfold usedX
    show _ = X.p ^ segG X.TT j * a0 j + u1 j + _
    simp only [hu1]
    ring
  have hX : ∑ j, Finsupp.single ((topStart X j, true), (0 : Fin (X.m + 1))) (usedX X β a0 j0 j) =
      (∑ j, Finsupp.single ((topStart X j, true), (0 : Fin (X.m + 1))) ((X.seg C0 CE1 CE2 j).Qj X.p * a0 j)) +
      (∑ j, Finsupp.single ((topStart X j, true), (0 : Fin (X.m + 1))) (u1 j)) +
      Finsupp.single ((topStart X j0, true), (0 : Fin (X.m + 1))) X.c := by
    simp only [hus, Finsupp.single_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single j0]
    · rw [if_pos rfl]
    · intro j _ hj
      rw [if_neg hj, Finsupp.single_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hrot : ∑ j, Finsupp.single ((topStart X j, true), (0 : Fin (X.m + 1))) (usedX X β a0 j0 j) =
      ∑ j, Finsupp.single ((topEnd X j, true), (0 : Fin (X.m + 1))) (usedX X β a0 j0 (rot _ j)) :=
    ((Equiv.ofBijective _ (rot_bij (numSeg X.TT))).sum_comp
      (fun j => Finsupp.single ((topStart X j, true), (0 : Fin (X.m + 1))) (usedX X β a0 j0 j))).symm
  have hz : ∑ j, Finsupp.single ((topEnd X j, true), (0 : Fin (X.m + 1))) (segAPlus X.TT X.aT j - (β j).oPlus) =
      (∑ j, Finsupp.single ((topEnd X j, true), (0 : Fin (X.m + 1)))
        (segAPlus X.TT X.aT j - (β j).oPlus - usedX X β a0 j0 (rot _ j))) +
      ∑ j, Finsupp.single ((topEnd X j, true), (0 : Fin (X.m + 1))) (usedX X β a0 j0 (rot _ j)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finsupp.single_add, Nat.sub_add_cancel (hroom j)]
  unfold rig rig0 stdE
  simp only [hb, Finset.sum_add_distrib]
  rw [hz, ← hrot, hX]
  abel

end Rig

section Tot

variable {σ K : Type} [CommRing K] {J : Type} [Fintype J] {A : J → Type} [∀ j, Fintype (A j)] {B : J → Type}
  [∀ j, Fintype (B j)] {M : Type} [Fintype M]

theorem wh_total (ω : σ → ℕ) {sR : MvPolynomial σ K} {dR : ℕ} (hR : IsWeightedHomogeneous ω sR dR)
    {sC : ∀ j, A j → MvPolynomial σ K} {dC : ∀ j, A j → ℕ} (hC : ∀ j a, IsWeightedHomogeneous ω (sC j a) (dC j a))
    {sH : ∀ j, B j → MvPolynomial σ K} {dH : ∀ j, B j → ℕ} (hH : ∀ j i, IsWeightedHomogeneous ω (sH j i) (dH j i))
    {sM : M → MvPolynomial σ K} {dM : M → ℕ} (hM : ∀ a, IsWeightedHomogeneous ω (sM a) (dM a))
    (lv : ∀ j, B j → ℕ) (mult : M → ℕ) :
    IsWeightedHomogeneous ω (sR * ((∏ j, ∏ a, sC j a) * ((∏ j, ∏ i, sH j i ^ lv j i) * ∏ a, sM a ^ mult a)))
      (dR + ((∑ j, ∑ a, dC j a) + ((∑ j, ∑ i, lv j i * dH j i) + ∑ a, mult a * dM a))) := by
  have h1 := IsWeightedHomogeneous.prod Finset.univ (fun j => ∏ a, sC j a) (fun j => ∑ a, dC j a)
    (fun j _ => IsWeightedHomogeneous.prod Finset.univ (sC j) (dC j) fun a _ => hC j a)
  have h2 := IsWeightedHomogeneous.prod Finset.univ (fun j => ∏ i, sH j i ^ lv j i)
    (fun j => ∑ i, lv j i * dH j i)
    (fun j _ => IsWeightedHomogeneous.prod Finset.univ (fun i => sH j i ^ lv j i) (fun i => lv j i * dH j i)
      fun i _ => by simpa only [smul_eq_mul] using (hH j i).pow (lv j i))
  have h3 := IsWeightedHomogeneous.prod Finset.univ (fun a => sM a ^ mult a) (fun a => mult a * dM a)
    fun a _ => by simpa only [smul_eq_mul] using (hM a).pow (mult a)
  exact hR.mul (h1.mul (h2.mul h3))

end Tot

end Formalism.MainNotions.ColumnSystems.Pf
