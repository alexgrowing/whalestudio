import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTorsionFormPoint

set_option autoImplicit false

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

namespace GlobalTheory.TorsionForm.OneVec

open GlobalTheory.TorsionForm

def basePart {m g : ℕ} (U : Finset (Fin (m + g))) : Finset (Fin m) :=
  Finset.univ.filter fun i => Fin.castAdd g i ∈ U

def fibrePart {m g : ℕ} (U : Finset (Fin (m + g))) : Finset (Fin g) :=
  Finset.univ.filter fun c => Fin.natAdd m c ∈ U

def pullBase {n : ℕ} (a : Fin n → ℂ) (y : Ext (n + n)) : Ext (1 + 1) := fun S =>
  if S = ∅ then y ∅
  else if S = {Fin.castAdd 1 (0 : Fin 1)} then ∑ i, a i * y {i.castAdd n}
  else if S = {Fin.natAdd 1 (0 : Fin 1)} then ∑ k, star (a k) * y {k.natAdd n}
  else ∑ i, ∑ k, a i * star (a k) * y {i.castAdd n, k.natAdd n}

def pullBaseL {n : ℕ} (a : Fin n → ℂ) : Ext (n + n) →L[ℂ] Ext (1 + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := pullBase a
      map_add' := fun x y => by
        funext S
        simp only [pullBase, Pi.add_apply]
        split_ifs <;> simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        funext S
        simp only [pullBase, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> simp [Finset.mul_sum] <;> refine Finset.sum_congr rfl fun _ _ => ?_ <;>
          try (refine Finset.sum_congr rfl fun _ _ => ?_)
        all_goals ring }

def pullFull {n g : ℕ} (a : Fin n → ℂ) (x : Ext (n + n + g)) : Ext (1 + 1 + g) := fun U =>
  pullBase a (fun S => x (join S (fibrePart U))) (basePart U)

def pullFullL {n g : ℕ} (a : Fin n → ℂ) : Ext (n + n + g) →L[ℂ] Ext (1 + 1 + g) :=
  LinearMap.toContinuousLinearMap
    { toFun := pullFull a
      map_add' := fun x y => by
        funext U
        have := (pullBaseL a).map_add (fun S => x (join S (fibrePart U)))
          (fun S => y (join S (fibrePart U)))
        exact congrFun this (basePart U)
      map_smul' := fun c x => by
        funext U
        have := (pullBaseL a).map_smul c (fun S => x (join S (fibrePart U)))
        exact congrFun this (basePart U) }

def wedgeL {m : ℕ} (i : Fin m) : Ext m →L[ℂ] Ext m :=
  LinearMap.toContinuousLinearMap
    { toFun := wedge i
      map_add' := fun x y => by funext S; simp only [wedge, Pi.add_apply]; split_ifs <;> ring
      map_smul' := fun c x => by
        funext S; simp only [wedge, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring }

def lamL {g : ℕ} (S : Finset (Fin (1 + 1))) : Ext (1 + 1 + g) →L[ℂ] Ext (1 + 1 + g) :=
  (if Fin.castAdd 1 (0 : Fin 1) ∈ S then wedgeL (dt g (0 : Fin 1)) else ContinuousLinearMap.id ℂ _).comp
    (if Fin.natAdd 1 (0 : Fin 1) ∈ S then wedgeL (dtb g (0 : Fin 1)) else ContinuousLinearMap.id ℂ _)

def rhoL {n g : ℕ} (S : Finset (Fin (1 + 1))) : Ext (1 + 1 + g) →L[ℂ] Ext (n + n + g) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w U => if basePart U = ∅ then w (join S (fibrePart U)) else 0
      map_add' := fun x y => by funext U; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c x => by funext U; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp }

def pullOp {n g : ℕ} (a : Fin n → ℂ) (K : Ext (n + n + g) →L[ℂ] Ext (n + n + g)) :
    Ext (1 + 1 + g) →L[ℂ] Ext (1 + 1 + g) :=
  ∑ S : Finset (Fin (1 + 1)), (lamL S).comp ((pullFullL a).comp (K.comp (rhoL S)))

end GlobalTheory.TorsionForm.OneVec
