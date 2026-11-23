import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestPair

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem comm_of_disj {E : GLOps n K V} (hE : IsGLRep E) {a b c d : Fin n} (h1 : b ≠ c) (h2 : d ≠ a) :
    Commute (E a b) (E c d) := by
  have := hE.1 a b c d
  rw [if_neg h1, if_neg h2, sub_zero, sub_eq_zero] at this
  exact this

theorem divPow_comm {E : GLOps n K V} {a b c d : Fin n} (h : Commute (E a b) (E c d)) (j k : ℕ) :
    Commute (divPowE E a b j) (divPowE E c d k) := by
  unfold divPowE
  exact ((h.pow_pow j k).smul_left _).smul_right _

theorem pf_comm {E : GLOps n K V} (hE : IsGLRep E) {a b c d : Fin n} (h1 : a ≠ c) (h2 : a ≠ d) (h3 : b ≠ c)
    (h4 : b ≠ d) (s s' T : ℕ) : Commute (pf E a b s T) (pf E c d s' T) := by
  unfold pf
  refine Commute.sum_left _ _ _ fun j _ => Commute.sum_right _ _ _ fun k _ => ?_
  refine (Commute.smul_left ?_ _).smul_right _
  have c1 : Commute (E b a) (E d c) := comm_of_disj hE h2 h3.symm
  have c2 : Commute (E b a) (E c d) := comm_of_disj hE h1 h4.symm
  have c3 : Commute (E a b) (E d c) := comm_of_disj hE h4 h1.symm
  have c4 : Commute (E a b) (E c d) := comm_of_disj hE h3 h2.symm
  exact Commute.mul_left (Commute.mul_right (divPow_comm c1 j k) (divPow_comm c2 j k))
    (Commute.mul_right (divPow_comm c3 j k) (divPow_comm c4 j k))

theorem dual_mem (E : GLOps n K V) (ν : Fin n → ℤ) (x : V) :
    x ∈ weightSp (dualOps E) (-ν) ↔ x ∈ weightSp E ν := by
  rw [mem_weightSpace_iff_diagonal_eigen, mem_weightSpace_iff_diagonal_eigen]
  refine forall_congr' fun a => ?_
  simp only [dualOps, LinearMap.neg_apply, Pi.neg_apply, Int.cast_neg, neg_smul, neg_inj]

theorem dual_rep {E : GLOps n K V} (hE : IsGLRep E) : IsGLRep (dualOps E) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    have := hE.1 b a d c
    simp only [dualOps, neg_mul_neg]
    rw [this, if_congr (eq_comm (a := a) (b := d)) rfl rfl, if_congr (eq_comm (a := c) (b := b)) rfl rfl]
    split_ifs <;> abel
  · intro x
    obtain ⟨W, h1, h2, h3⟩ := hE.2.1 x
    exact ⟨W, h1, h2, fun a b y hy => by
      simp only [dualOps, LinearMap.neg_apply]
      exact W.neg_mem (h3 b a y hy)⟩
  · rw [eq_top_iff, ← hE.2.2]
    refine iSup_le fun ν => le_iSup_of_le (-ν) fun x hx => (dual_mem E ν x).2 hx

theorem divPow_dual (E : GLOps n K V) (x y : Fin n) (k : ℕ) :
    divPowE (dualOps E) x y k = (-1 : K) ^ k • divPowE E y x k := by
  simp only [divPowE, dualOps]
  rw [show -E y x = (-1 : K) • E y x by simp, smul_pow, smul_comm]

theorem pf_dual (E : GLOps n K V) (x y : Fin n) (c T : ℕ) : pf (dualOps E) x y c T = pf E y x c T := by
  unfold pf
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [divPow_dual, divPow_dual, smul_mul_smul_comm, ← mul_pow]
  simp

end

theorem restComm : RestComm := fun _ _ _ _ _ _ _ hE _ _ _ _ h1 h2 h3 h4 s s' T => pf_comm hE h1 h2 h3 h4 s s' T

theorem restPair'_of (h : RestPair) : RestPair' := by
  intro K V _ _ _ _ _ n E hE a b c hab hac hbc ν t u hu T hT w hw
  have := h K V n (dualOps E) (dual_rep hE) c b a hbc.symm hac.symm hab.symm (-ν) t u
    (by simp only [Pi.neg_apply]; omega) T hT w ((dual_mem E ν w).2 hw)
  simp only [pf_dual] at this
  simp only [dualOps, LinearMap.neg_apply, map_neg, neg_inj] at this
  exact this

theorem ybat_symm (sg ta : ℕ) (h : YBat sg ta) : YBat ta sg := by
  intro K V _ _ _ _ _ n E hE a b c hab hac hbc ν s t hs ht T hT x hx
  have := h K V n (dualOps E) (dual_rep hE) c b a hbc.symm hac.symm hab.symm (-ν) t s
    (by simp only [Pi.neg_apply]; omega) (by simp only [Pi.neg_apply]; omega) T hT x ((dual_mem E ν x).2 hx)
  simp only [pf_dual] at this
  rw [add_comm t s] at this
  exact this.symm

end Formalism.MainNotions.G.ExtremalProjector
