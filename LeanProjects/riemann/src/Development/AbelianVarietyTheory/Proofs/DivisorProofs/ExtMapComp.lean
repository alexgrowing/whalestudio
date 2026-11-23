import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExtFunctor

variable {m : ℕ}

def wedgeLin (k : Fin m) : Ext m →ₗ[ℂ] Ext m where
  toFun := wedge k
  map_add' v w := by funext S; simp only [wedge, Pi.add_apply]; split_ifs <;> ring
  map_smul' c w := by
    funext S; simp only [wedge, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

def wedgeVec (v : Fin m → ℂ) : Ext m →ₗ[ℂ] Ext m := ∑ k, v k • wedgeLin k

theorem wedgeVec_apply (v : Fin m → ℂ) (w : Ext m) : wedgeVec v w = ∑ k, v k • wedge k w := by
  simp [wedgeVec, wedgeLin]

theorem sgn_erase_of_lt {k l : Fin m} {S : Finset (Fin m)} (hk : k ∈ S) (h : k < l) :
    sgn l (S.erase k) = - sgn l S := by
  unfold sgn
  rw [Finset.filter_erase, Finset.card_erase_of_mem (by simp [hk, h])]
  have : 0 < (S.filter (· < l)).card := Finset.card_pos.2 ⟨k, by simp [hk, h]⟩
  obtain ⟨n, hn⟩ : ∃ n, (S.filter (· < l)).card = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos this).symm⟩
  rw [hn]; simp [pow_succ]

theorem sgn_erase_of_not_lt {k l : Fin m} {S : Finset (Fin m)} (h : ¬ k < l) :
    sgn l (S.erase k) = sgn l S := by
  unfold sgn
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem (by simp [h])]

theorem wedge_wedge_add (k l : Fin m) (w : Ext m) :
    wedge k (wedge l w) + wedge l (wedge k w) = 0 := by
  funext S
  simp only [wedge, Pi.add_apply, Pi.zero_apply, Finset.mem_erase]
  by_cases hkl : k = l
  · subst hkl; simp
  rcases lt_or_gt_of_ne hkl with h | h
  · by_cases hk : k ∈ S <;> by_cases hl : l ∈ S <;> simp [hk, hl, hkl, Ne.symm hkl]
    rw [Finset.erase_right_comm, sgn_erase_of_lt hk h, sgn_erase_of_not_lt (not_lt.2 h.le)]
    ring
  · by_cases hk : k ∈ S <;> by_cases hl : l ∈ S <;> simp [hk, hl, hkl, Ne.symm hkl]
    rw [Finset.erase_right_comm, sgn_erase_of_lt hl h, sgn_erase_of_not_lt (not_lt.2 h.le)]
    ring

theorem wedgeVec_comm (v v' : Fin m → ℂ) (w : Ext m) :
    wedgeVec v (wedgeVec v' w) = - wedgeVec v' (wedgeVec v w) := by
  have e : ∀ a b : Fin m → ℂ, wedgeVec a (wedgeVec b w) =
      ∑ k, ∑ l, (a k * b l) • wedge k (wedge l w) := by
    intro a b
    rw [wedgeVec_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [wedgeVec_apply, show wedge k (∑ l, b l • wedge l w) = wedgeLin k (∑ l, b l • wedge l w) from rfl,
      map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, smul_smul]; rfl
  rw [e, e, eq_neg_iff_add_eq_zero, Finset.sum_comm (f := fun k l => (v' k * v l) • wedge k (wedge l w)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [mul_comm (v' l), ← smul_add, wedge_wedge_add, smul_zero]

theorem wedgeVec_self (v : Fin m → ℂ) (w : Ext m) : wedgeVec v (wedgeVec v w) = 0 := by
  have h := wedgeVec_comm v v w
  funext S
  have h2 := congrFun h S
  simp only [Pi.neg_apply, Pi.zero_apply] at h2 ⊢
  linear_combination h2 / 2

theorem genProd_empty (φ : Matrix (Fin m) (Fin m) ℂ) : genProd φ ∅ = Pi.single ∅ 1 := by
  simp [genProd]

theorem genProd_insert_min (φ : Matrix (Fin m) (Fin m) ℂ) {a : Fin m} {T : Finset (Fin m)}
    (ha : ∀ x ∈ T, a < x) : genProd φ (insert a T) = wedgeVec (φ a) (genProd φ T) := by
  have haT : a ∉ T := fun h => lt_irrefl a (ha a h)
  unfold genProd
  rw [Finset.sort_insert (· ≤ ·) (fun x hx => (ha x hx).le) haT, List.foldr_cons, wedgeVec_apply]

theorem sgn_insert_of_lt {a i : Fin m} {T : Finset (Fin m)} (ha : a ∉ T) (h : a < i) :
    sgn i (insert a T) = - sgn i T := by
  have := sgn_erase_of_lt (S := insert a T) (Finset.mem_insert_self a T) h
  rw [Finset.erase_insert ha] at this
  rw [this, neg_neg]

theorem sgn_of_lt_all {i : Fin m} {T : Finset (Fin m)} (h : ∀ x ∈ T, i < x) : sgn i T = 1 := by
  unfold sgn
  rw [Finset.filter_false_of_mem (fun x hx => not_lt.2 (h x hx).le)]
  simp

theorem key (φ : Matrix (Fin m) (Fin m) ℂ) (S : Finset (Fin m)) : ∀ i,
    (i ∈ S → wedgeVec (φ i) (genProd φ S) = 0) ∧
    (i ∉ S → genProd φ (insert i S) = sgn i S • wedgeVec (φ i) (genProd φ S)) := by
  refine Finset.induction_on_min S ?_ ?_
  · intro i
    refine ⟨by simp, fun _ => ?_⟩
    rw [genProd_insert_min φ (by simp), sgn_of_lt_all (by simp), one_smul]
  · intro a T hmin ih
    have haT : a ∉ T := fun h => lt_irrefl a (hmin a h)
    intro i
    rw [genProd_insert_min φ hmin]
    refine ⟨fun hi => ?_, fun hi => ?_⟩
    · rcases Finset.mem_insert.1 hi with rfl | hiT
      · exact wedgeVec_self _ _
      · rw [wedgeVec_comm, (ih i).1 hiT, map_zero, neg_zero]
    · have hia : i ≠ a := fun h => hi (h ▸ Finset.mem_insert_self a T)
      have hiT : i ∉ T := fun h => hi (Finset.mem_insert_of_mem h)
      rcases lt_or_gt_of_ne hia with h | h
      · have hall : ∀ x ∈ insert a T, i < x := by
          intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact h
          · exact h.trans (hmin x hx)
        rw [genProd_insert_min φ hall, genProd_insert_min φ hmin, sgn_of_lt_all hall, one_smul]
      · have hall : ∀ x ∈ insert i T, a < x := by
          intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact h
          · exact hmin x hx
        rw [Finset.insert_comm, genProd_insert_min φ hall, (ih i).2 hiT, map_smul, wedgeVec_comm,
          sgn_insert_of_lt haT h, smul_neg, neg_smul]

theorem wedge_single (i : Fin m) (S : Finset (Fin m)) :
    wedge i (Pi.single S (1 : ℂ)) = if i ∈ S then 0 else sgn i S • Pi.single (insert i S) 1 := by
  funext T
  by_cases hS : i ∈ S
  · simp only [hS, if_true, wedge, Pi.zero_apply]
    split_ifs with hT
    · rw [Pi.single_apply, if_neg, mul_zero]
      intro e; exact Finset.notMem_erase i T (e ▸ hS)
    · rfl
  · simp only [hS, if_false, wedge, Pi.smul_apply, smul_eq_mul]
    split_ifs with hT
    · by_cases e : T = insert i S
      · subst e; simp [Finset.erase_insert hS, sgn_insert]
      · have e' : T.erase i ≠ S := fun h => e (by rw [← h, Finset.insert_erase hT])
        simp [Pi.single_apply, e, e']
    · have e : T ≠ insert i S := fun h => hT (h ▸ Finset.mem_insert_self i S)
      simp [Pi.single_apply, e]

theorem extMap_single (φ : Matrix (Fin m) (Fin m) ℂ) (S : Finset (Fin m)) :
    extMap φ (Pi.single S 1) = genProd φ S := by
  rw [extMap_apply, Finset.sum_eq_single S]
  · simp
  · intro T _ hT; simp [Pi.single_apply, hT]
  · simp

theorem extMap_wedge (φ : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) (w : Ext m) :
    extMap φ (wedge i w) = wedgeVec (φ i) (extMap φ w) := by
  have h : (extMap φ).toLinearMap ∘ₗ wedgeLin i = wedgeVec (φ i) ∘ₗ (extMap φ).toLinearMap := by
    refine (Pi.basisFun ℂ (Finset (Fin m))).ext fun S => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Pi.basisFun_apply, ContinuousLinearMap.coe_coe]
    rw [show wedgeLin i (Pi.single S 1) = wedge i (Pi.single S 1) from rfl, wedge_single, extMap_single]
    by_cases hS : i ∈ S
    · rw [if_pos hS, map_zero, (key φ S i).1 hS]
    · rw [if_neg hS, map_smul, extMap_single, (key φ S i).2 hS, smul_smul, sgn_mul_self, one_smul]
  exact LinearMap.congr_fun h w

theorem extMap_wedgeVec (φ ψ : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (x : Ext m) :
    extMap φ (wedgeVec (ψ a) x) = wedgeVec ((ψ * φ) a) (extMap φ x) := by
  rw [wedgeVec_apply, map_sum]
  simp_rw [map_smul, extMap_wedge, wedgeVec_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_smul]

theorem extMap_genProd (φ ψ : Matrix (Fin m) (Fin m) ℂ) (S : Finset (Fin m)) :
    extMap φ (genProd ψ S) = genProd (ψ * φ) S := by
  refine Finset.induction_on_min S ?_ ?_
  · rw [genProd_empty, genProd_empty, extMap_single, genProd_empty]
  · intro a T hmin ih
    rw [genProd_insert_min ψ hmin, genProd_insert_min (ψ * φ) hmin, extMap_wedgeVec, ih]

theorem extMap_comp {m : ℕ} (φ ψ : Matrix (Fin m) (Fin m) ℂ) :
    extMap φ ∘L extMap ψ = extMap (ψ * φ) := by
  ext1 w
  rw [ContinuousLinearMap.comp_apply, extMap_apply ψ, map_sum, extMap_apply]
  simp_rw [map_smul, extMap_genProd]
