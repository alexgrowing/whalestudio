import Mathlib
import GroundTheory.LocalFields.BrauerInductionInduced
import GroundTheory.TateCohomology.DoubleCosetSum
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise

namespace GroundTheory.Global.Artin

open GroundTheory.LocalField

variable {G : Type*} [Group G]

section ExtendByZero

theorem mem_conj_smul_iff (H : Subgroup G) (a g : G) :
    g ∈ (MulAut.conj a • H : Subgroup G) ↔ a⁻¹ * g * a ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def, MulAut.conj_apply,
    inv_inv]

theorem mem_conj_inv_smul_iff (H : Subgroup G) (x g : G) :
    g ∈ (MulAut.conj x⁻¹ • H : Subgroup G) ↔ x * g * x⁻¹ ∈ H := by
  rw [mem_conj_smul_iff, inv_inv]

open Classical in

def extendByZero (H : Subgroup G) (f : H → ℂ) (g : G) : ℂ :=
  if h : g ∈ H then f ⟨g, h⟩ else 0

theorem extendByZero_of_mem (H : Subgroup G) (f : H → ℂ) {g : G} (hg : g ∈ H) :
    extendByZero H f g = f ⟨g, hg⟩ := by
  unfold extendByZero
  rw [dif_pos hg]

theorem extendByZero_of_notMem (H : Subgroup G) (f : H → ℂ) {g : G} (hg : g ∉ H) :
    extendByZero H f g = 0 := by
  unfold extendByZero
  rw [dif_neg hg]

@[simp]
theorem extendByZero_coe (H : Subgroup G) (f : H → ℂ) (h : H) : extendByZero H f h = f h :=
  extendByZero_of_mem H f h.2

theorem extendByZero_conj {H : Subgroup G} {f : H → ℂ} (hf : IsClassFun f) {h : G} (hh : h ∈ H)
    (g : G) : extendByZero H f (h * g * h⁻¹) = extendByZero H f g := by
  by_cases hg : g ∈ H
  · have hm : h * g * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hg) (H.inv_mem hh)
    rw [extendByZero_of_mem H f hm, extendByZero_of_mem H f hg, ← hf ⟨g, hg⟩ ⟨h, hh⟩]
    rfl
  · have hm : h * g * h⁻¹ ∉ H := fun hm ↦ hg (by
      have := H.mul_mem (H.mul_mem (H.inv_mem hh) hm) hh
      simpa [mul_assoc] using this)
    rw [extendByZero_of_notMem H f hm, extendByZero_of_notMem H f hg]

theorem indFun_subtype_apply [Fintype G] (H : Subgroup G) [Fintype H] (f : H → ℂ) (s : G) :
    indFun H.subtype f s = (Nat.card H : ℂ)⁻¹ * ∑ t : G, extendByZero H f (t⁻¹ * s * t) := by
  classical
  rw [indFun_apply]
  congr 1
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  by_cases hm : t⁻¹ * s * t ∈ H
  · rw [extendByZero_of_mem H f hm, Finset.sum_eq_single ⟨_, hm⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hb'
      exact hb (Subtype.ext hb')
    · simp
  · rw [extendByZero_of_notMem H f hm]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    rw [if_neg]
    intro hb'
    exact hm (hb' ▸ b.2)

end ExtendByZero

section Count

variable [Fintype G]

open Classical in

theorem sum_mul_mul_eq (H D : Subgroup G) [Fintype H] [Fintype D] (x : G) (F : G → ℂ) :
    ∑ h : H, ∑ e : D, F (h * x * e) =
      (Nat.card ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D) : ℂ) *
        ∑ u ∈ Finset.univ.filter (fun u ↦ DoubleCoset.mk H D u = DoubleCoset.mk H D x), F u := by
  classical
  set E : Subgroup D := (MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D with hEdef
  have hE : ∀ c : D, c ∈ E ↔ x * c * x⁻¹ ∈ H := fun c ↦ by
    rw [hEdef, Subgroup.mem_subgroupOf, mem_conj_inv_smul_iff]
  have hfib : ∀ u : G, (Finset.univ.filter (fun p : H × D ↦ (p.1 : G) * x * p.2 = u)).card =
      if DoubleCoset.mk H D u = DoubleCoset.mk H D x then Nat.card E else 0 := by
    intro u
    split_ifs with hu
    · obtain ⟨h0, hh0, e0, he0, rfl⟩ := (DoubleCoset.eq H D x u).1 hu.symm
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
      refine Finset.card_bij' (fun p _ ↦ ⟨⟨e0 * (p.2 : G)⁻¹, D.mul_mem he0 (D.inv_mem p.2.2)⟩, ?_⟩)
        (fun c _ ↦ (⟨h0 * (x * ((c : D) : G) * x⁻¹), H.mul_mem hh0 ((hE c).1 c.2)⟩,
          ⟨((c : D) : G)⁻¹ * e0, D.mul_mem (D.inv_mem (c : D).2) he0⟩)) ?_ ?_ ?_ ?_
      · rename_i p hp
        rw [Finset.mem_filter] at hp
        rw [hE]
        have hp1 : (p.1 : G) = h0 * x * e0 * (p.2 : G)⁻¹ * x⁻¹ := by
          rw [← hp.2]
          group
        have : x * (e0 * (p.2 : G)⁻¹) * x⁻¹ = h0⁻¹ * p.1 := by
          rw [hp1]
          group
        rw [show ((⟨e0 * (p.2 : G)⁻¹, D.mul_mem he0 (D.inv_mem p.2.2)⟩ : D) : G) =
          e0 * (p.2 : G)⁻¹ from rfl, this]
        exact H.mul_mem (H.inv_mem hh0) p.1.2
      · intro p _
        exact Finset.mem_univ _
      · intro c _
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        group
      · intro p hp
        rw [Finset.mem_filter] at hp
        ext
        · change h0 * (x * (e0 * (p.2 : G)⁻¹) * x⁻¹) = p.1
          have hp1 : (p.1 : G) = h0 * x * e0 * (p.2 : G)⁻¹ * x⁻¹ := by
            rw [← hp.2]
            group
          rw [hp1]
          group
        · change (e0 * (p.2 : G)⁻¹)⁻¹ * e0 = p.2
          group
      · intro c _
        ext
        change e0 * (((c : D) : G)⁻¹ * e0)⁻¹ = ((c : D) : G)
        group
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p _ hp
      apply hu
      exact ((DoubleCoset.eq H D x u).2 ⟨p.1, p.1.2, p.2, p.2.2, hp.symm⟩).symm
  calc ∑ h : H, ∑ e : D, F (h * x * e)
      = ∑ p : H × D, F ((p.1 : G) * x * p.2) := (Fintype.sum_prod_type' _).symm
    _ = ∑ u : G, ∑ p ∈ Finset.univ.filter (fun p : H × D ↦ (p.1 : G) * x * p.2 = u),
          F ((p.1 : G) * x * p.2) :=
        (Finset.sum_fiberwise Finset.univ (fun p : H × D ↦ (p.1 : G) * x * p.2) _).symm
    _ = ∑ u : G, (if DoubleCoset.mk H D u = DoubleCoset.mk H D x then (Nat.card E : ℂ) else 0) *
          F u := by
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [Finset.sum_congr rfl fun p hp ↦ by rw [(Finset.mem_filter.1 hp).2], Finset.sum_const,
          nsmul_eq_mul, hfib u]
        split_ifs <;> simp
    _ = (Nat.card E : ℂ) *
          ∑ u ∈ Finset.univ.filter (fun u ↦ DoubleCoset.mk H D u = DoubleCoset.mk H D x), F u := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        split_ifs <;> simp

end Count

section Mackey

def conjFun (H D : Subgroup G) (x : G) (f : H → ℂ) :
    (MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D → ℂ :=
  fun d ↦ f ⟨x * ((d : D) : G) * x⁻¹,
    (mem_conj_inv_smul_iff H x _).1 (Subgroup.mem_subgroupOf.1 d.2)⟩

theorem extendByZero_conjFun (H D : Subgroup G) (x : G) (f : H → ℂ) (y : D) :
    extendByZero _ (conjFun H D x f) y = extendByZero H f (x * y * x⁻¹) := by
  by_cases hy : y ∈ (MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D
  · rw [extendByZero_of_mem _ _ hy, extendByZero_of_mem H f
      ((mem_conj_inv_smul_iff H x _).1 (Subgroup.mem_subgroupOf.1 hy))]
    rfl
  · have hy' : x * (y : G) * x⁻¹ ∉ H := fun h ↦
      hy (Subgroup.mem_subgroupOf.2 ((mem_conj_inv_smul_iff H x _).2 h))
    rw [extendByZero_of_notMem _ _ hy, extendByZero_of_notMem H f hy']

variable [Fintype G]

open Classical in

theorem indFun_comp_subtype_eq_sum (H D : Subgroup G) [Fintype H] [Fintype D] {f : H → ℂ}
    (hf : IsClassFun f) (x : DoubleCoset.Quotient (H : Set G) D → G)
    (hx : ∀ q, DoubleCoset.mk H D (x q) = q) :
    indFun H.subtype f ∘ D.subtype =
      ∑ q, indFun ((MulAut.conj (x q)⁻¹ • H : Subgroup G).subgroupOf D).subtype
        (conjFun H D (x q) f) := by
  classical
  funext d
  rw [Function.comp_apply, Finset.sum_apply, indFun_subtype_apply]
  simp_rw [indFun_subtype_apply, extendByZero_conjFun]
  have h1 : ∑ t : G, extendByZero H f (t⁻¹ * D.subtype d * t) =
      ∑ u : G, extendByZero H f (u * d * u⁻¹) :=
    Fintype.sum_equiv (Equiv.inv G) _ _ (fun t ↦ by simp)
  rw [h1, ← Finset.sum_fiberwise Finset.univ (DoubleCoset.mk H D), Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have key := sum_mul_mul_eq H D (x q) (fun u ↦ extendByZero H f (u * d * u⁻¹))
  rw [hx q] at key
  set E : Subgroup D := (MulAut.conj (x q)⁻¹ • H : Subgroup G).subgroupOf D
  have hE0 : (Nat.card E : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hH0 : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h2 : ∀ (h : H) (e : D), extendByZero H f ((h * x q * e) * d * (h * x q * e)⁻¹) =
      extendByZero H f (x q * ((e * d * e⁻¹ : D) : G) * (x q)⁻¹) := by
    intro h e
    rw [← extendByZero_conj hf h.2 (x q * ((e * d * e⁻¹ : D) : G) * (x q)⁻¹)]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have h3 : ∑ h : H, ∑ e : D, extendByZero H f ((h * x q * e) * d * (h * x q * e)⁻¹) =
      Nat.card H * ∑ t : D, extendByZero H f (x q * ((t⁻¹ * d * t : D) : G) * (x q)⁻¹) := by
    simp_rw [h2]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    congr 1
    exact Fintype.sum_equiv (Equiv.inv D) _ _ (fun e ↦ by simp)
  rw [h3] at key
  have hS : ∑ u ∈ Finset.univ.filter (fun u ↦ DoubleCoset.mk H D u = q),
      extendByZero H f (u * d * u⁻¹) = (Nat.card E : ℂ)⁻¹ *
        (Nat.card H * ∑ t : D, extendByZero H f (x q * ((t⁻¹ * d * t : D) : G) * (x q)⁻¹)) := by
    rw [key, inv_mul_cancel_left₀ hE0]
  rw [hS, mul_left_comm, inv_mul_cancel_left₀ hH0]

end Mackey

end GroundTheory.Global.Artin
