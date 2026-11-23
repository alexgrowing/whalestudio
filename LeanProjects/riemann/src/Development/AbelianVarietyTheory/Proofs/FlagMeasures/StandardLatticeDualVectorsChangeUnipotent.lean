import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc

noncomputable section

namespace GlobalTheory.SwapStd

open Formalism.MainNotions.S.LocNG Formalism.MainNotions.KappaEndpoints

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

theorem hR_add (x y z : V) : H.h x (y + z) = H.h x y + H.h x z := by
  rw [H.h_herm (y + z) x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

theorem hR_smul (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem hL_neg (x y : V) : H.h (-x) y = - H.h x y := by
  have := H.h_add_left x (-x) y
  rw [add_neg_cancel, H.h_zero_left] at this
  linear_combination -this

theorem hL_sub (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  rw [sub_eq_add_neg, H.h_add_left, hL_neg]; ring

theorem hL_sum {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, c i • v i) y = ∑ i ∈ s, c i * H.h (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [H.h_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]

theorem h_symm_zero {x y : V} (h : H.h y x = 0) : H.h x y = 0 := by
  rw [H.h_herm y x, h, map_zero]

variable (A B : FrameD H r)

theorem perp_of {k : V} (h : ∀ a : Fin r, H.h k (A.e a) = 0) : k ∈ H.perp (H.X A.f) := by
  intro x hx
  unfold HermSp.X at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
  | zero => exact h_symm_zero (H.h_zero_left k)
  | add x y _ _ hx hy => rw [hR_add, hx, hy, add_zero]
  | smul c x _ hx => rw [hR_smul, hx, mul_zero]

theorem e_mem_X (a : Fin r) : A.e a ∈ H.X A.f := Submodule.subset_span ⟨a, rfl⟩

theorem h_X_e {ξ : V} (hξ : ξ ∈ H.X A.f) (b : Fin r) : H.h ξ (A.e b) = 0 := by
  unfold HermSp.X at hξ
  induction hξ using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact A.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)
  | zero => exact H.h_zero_left _
  | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]

theorem X_le_perp {ξ : V} (hξ : ξ ∈ H.X A.f) : ξ ∈ H.perp (H.X A.f) := perp_of A (h_X_e A hξ)

theorem hX_perp {ξ w : V} (hξ : ξ ∈ H.X A.f) (hw : w ∈ H.perp (H.X A.f)) : H.h ξ w = 0 :=
  h_symm_zero (hw ξ hξ)

theorem prF_mem_perp' (y : V) : A.prF y ∈ H.perp (H.X A.f) :=
  perp_of A (fun a => ng_prF_e (Fr := A) y a)

theorem prF_add (x y : V) : A.prF (x + y) = A.prF x + A.prF y := by
  unfold FrameD.prF
  simp only [H.h_add_left, add_smul, Finset.sum_add_distrib]; abel

theorem prF_smul (c : E) (x : V) : A.prF (c • x) = c • A.prF x := by
  unfold FrameD.prF
  simp only [H.h_smul_left, mul_smul, ← Finset.smul_sum, smul_sub]

theorem prF_sub (x y : V) : A.prF (x - y) = A.prF x - A.prF y := by
  unfold FrameD.prF
  simp only [hL_sub, sub_smul, Finset.sum_sub_distrib]; abel

def swapFun (x : V) : V :=
  ∑ a, H.h x (A.es a) • A.e a + A.prF x + ∑ a, H.h x (A.e a) • B.es a -
    ∑ a, H.h (A.prF x) (B.es a) • A.e a

def swapMap : V →ₗ[E] V where
  toFun := swapFun A B
  map_add' x y := by
    unfold swapFun
    simp only [H.h_add_left, prF_add, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c x := by
    unfold swapFun
    simp only [H.h_smul_left, prF_smul, mul_smul, ← Finset.smul_sum, smul_sub, smul_add, RingHom.id_apply]

theorem swapMap_apply (x : V) : swapMap A B x = swapFun A B x := rfl

section Pair

variable (hf : B.f = A.f)
include hf

theorem e_eq (a : Fin r) : B.e a = A.e a := by
  show B.f a.castSucc = A.f a.castSucc; rw [hf]

theorem h_e_esB (a b : Fin r) : H.h (A.e a) (B.es b) = if a = b then 1 else 0 := by
  rw [← e_eq A B hf]; exact B.h_es a b

theorem h_esB_e (a b : Fin r) : H.h (B.es a) (A.e b) = if b = a then 1 else 0 := by
  rw [← e_eq A B hf]; exact ng_h_es_e (Fr := B) a b

theorem swap_es (x : V) (b : Fin r) : H.h (swapMap A B x) (B.es b) = H.h x (A.es b) := by
  rw [swapMap_apply]
  unfold swapFun
  rw [hL_sub, H.h_add_left, H.h_add_left, hL_sum, hL_sum, hL_sum]
  simp only [h_e_esB A B hf, B.h_ss, mul_zero, Finset.sum_const_zero, add_zero, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem swap_e (x : V) (b : Fin r) : H.h (swapMap A B x) (A.e b) = H.h x (A.e b) := by
  rw [swapMap_apply]
  unfold swapFun
  rw [hL_sub, H.h_add_left, H.h_add_left, hL_sum, hL_sum, hL_sum]
  have hee : ∀ a, H.h (A.e a) (A.e b) = 0 := fun a => A.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)
  simp only [hee, ng_prF_e, h_esB_e A B hf, mul_zero, Finset.sum_const_zero, add_zero, zero_add, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_zero]

theorem swap_prF (x : V) : B.prF (swapMap A B x) - A.prF x = - ∑ a, H.h (A.prF x) (B.es a) • A.e a := by
  have e1 : B.prF (swapMap A B x) = swapMap A B x - ∑ a, H.h x (A.es a) • A.e a -
      ∑ a, H.h x (A.e a) • B.es a := by
    unfold FrameD.prF
    simp only [swap_es A B hf, e_eq A B hf, swap_e A B hf]
  rw [e1, swapMap_apply]
  unfold swapFun
  abel

theorem swap_prF_mem (x : V) : B.prF (swapMap A B x) - A.prF x ∈ H.X A.f := by
  rw [swap_prF A B hf]
  exact Submodule.neg_mem _ (Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (e_mem_X A a)))

theorem swap_unit (x y : V) : H.h (swapMap A B x) (swapMap A B y) = H.h x y := by
  have k1 : ∀ a, H.h (A.e a) (swapMap A B y) = H.h (A.e a) y := fun a => by
    rw [H.h_herm (swapMap A B y) (A.e a), swap_e A B hf, ← H.h_herm]
  have k2 : ∀ a, H.h (B.es a) (swapMap A B y) = H.h (A.es a) y := fun a => by
    rw [H.h_herm (swapMap A B y) (B.es a), swap_es A B hf, ← H.h_herm]
  have k3 : H.h (B.prF (swapMap A B x)) (B.prF (swapMap A B y)) = H.h (A.prF x) (A.prF y) := by
    have hx := swap_prF_mem A B hf x
    have hy := swap_prF_mem A B hf y
    set ξ := B.prF (swapMap A B x) - A.prF x
    set η := B.prF (swapMap A B y) - A.prF y
    rw [show B.prF (swapMap A B x) = A.prF x + ξ by simp [ξ],
      show B.prF (swapMap A B y) = A.prF y + η by simp [η],
      H.h_add_left, hR_add, hR_add, hX_perp A hx (prF_mem_perp' A y), hX_perp A hx (X_le_perp A hy),
      h_symm_zero (hX_perp A hy (prF_mem_perp' A x))]
    ring
  rw [ng_expand (Fr := B) (swapMap A B x) (swapMap A B y), ng_prF_prF (Fr := B) (swapMap A B x) (swapMap A B y),
    ng_expand (Fr := A) x y, ng_prF_prF (Fr := A) x y, k3]
  simp only [e_eq A B hf, swap_es A B hf, swap_e A B hf, k1, k2]

theorem swap_fix (b : Fin (r + 1)) : swapMap A B (A.f b) = A.f b := by
  rw [swapMap_apply]
  unfold swapFun
  rcases Fin.eq_castSucc_or_eq_last b with ⟨a, rfl⟩ | rfl
  · have hpr : A.prF (A.f a.castSucc) = 0 := by
      have := ng_prF_e (Fr := A) (A.f a.castSucc)
      unfold FrameD.prF
      have hs : ∑ c, H.h (A.f a.castSucc) (A.es c) • A.e c = A.e a := by
        simp only [A.h_es, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have hz : ∑ c, H.h (A.f a.castSucc) (A.e c) • A.es c = 0 :=
        Finset.sum_eq_zero (fun c _ => by
          rw [show H.h (A.f a.castSucc) (A.e c) = 0 from A.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne), zero_smul])
      rw [hs, hz]; show A.f a.castSucc - A.f a.castSucc - 0 = 0; simp
    have hs : ∑ c, H.h (A.f a.castSucc) (A.es c) • A.e c = A.f a.castSucc := by
      simp only [A.h_es, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]; rfl
    have hz : ∑ c, H.h (A.f a.castSucc) (A.e c) • B.es c = 0 :=
      Finset.sum_eq_zero (fun c _ => by
        rw [show H.h (A.f a.castSucc) (A.e c) = 0 from A.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne), zero_smul])
    rw [hs, hz, hpr]
    simp [H.h_zero_left]
  · have hzes : ∀ c, H.h (A.f (Fin.last r)) (A.es c) = 0 := fun c => h_symm_zero (A.h_sz c)
    have hze : ∀ c, H.h (A.f (Fin.last r)) (A.e c) = 0 := fun c =>
      A.h_iso _ _ (Or.inr (Fin.castSucc_lt_last c).ne)
    have hpr : A.prF (A.f (Fin.last r)) = A.f (Fin.last r) := by
      unfold FrameD.prF
      simp [hzes, hze]
    have hzB : ∀ c, H.h (A.f (Fin.last r)) (B.es c) = 0 := fun c => by
      rw [← hf]; exact h_symm_zero (B.h_sz c)
    simp [hzes, hze, hpr, hzB]

end Pair

theorem eq_zero_of (v : V) (h1 : ∀ a, H.h v (A.es a) = 0) (h2 : ∀ a, H.h v (A.e a) = 0)
    (h3 : A.prF v ∈ H.X A.f) : v = 0 := by
  apply H.nondeg v
  intro y
  rw [ng_expand (Fr := A) v y, ng_prF_prF (Fr := A) v y]
  simp only [h1, h2, zero_mul, Finset.sum_const_zero, zero_add, add_zero]
  exact hX_perp A h3 (prF_mem_perp' A y)

theorem swap_inv (hf : B.f = A.f) (x : V) : swapMap B A (swapMap A B x) = x := by
  have hf' : A.f = B.f := hf.symm
  rw [← sub_eq_zero]
  apply eq_zero_of A
  · intro b
    rw [hL_sub, swap_es B A hf', swap_es A B hf, sub_self]
  · intro b
    have h1 := swap_e B A hf' (swapMap A B x) b
    rw [← e_eq B A hf'] at h1
    rw [hL_sub, h1, swap_e A B hf, sub_self]
  · have h1 := swap_prF_mem B A hf' (swapMap A B x)
    have h2 := swap_prF_mem A B hf x
    rw [hf'] at h2
    rw [prF_sub, show A.prF (swapMap B A (swapMap A B x)) - A.prF x =
      (A.prF (swapMap B A (swapMap A B x)) - B.prF (swapMap A B x)) + (B.prF (swapMap A B x) - A.prF x) by abel]
    rw [hf']
    exact Submodule.add_mem _ h1 h2

def swapEquiv (hf : B.f = A.f) : V ≃ₗ[E] V :=
  LinearEquiv.ofLinear (swapMap A B) (swapMap B A)
    (LinearMap.ext fun x => swap_inv B A hf.symm x) (LinearMap.ext fun x => swap_inv A B hf x)

theorem swapEquiv_apply (hf : B.f = A.f) (x : V) : swapEquiv A B hf x = swapMap A B x := rfl

theorem swap_mem_N (hf : B.f = A.f) : swapEquiv A B hf ∈ A.N := by
  apply Subgroup.subset_closure
  refine ⟨fun x y => swap_unit A B hf x y, ?_, ?_⟩
  · intro j _ v hv
    have hfix : swapEquiv A B hf v = v := by
      unfold FrameD.Fj at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, -, rfl⟩ := hx
        exact swap_fix A B hf a.castSucc
      | zero => exact map_zero _
      | add x y _ _ hx hy => rw [map_add, hx, hy]
      | smul c x _ hx => rw [map_smul, hx]
    rw [hfix, sub_self]; exact Submodule.zero_mem _
  · intro v hv
    have h0 : ∀ a, H.h v (A.e a) = 0 := fun a => hv _ (e_mem_X A a)
    have e : swapEquiv A B hf v - v = - ∑ a, H.h (A.prF v) (B.es a) • A.e a := by
      rw [swapEquiv_apply, swapMap_apply]
      unfold swapFun
      have hv' : v = ∑ a, H.h v (A.es a) • A.e a + A.prF v := by
        unfold FrameD.prF
        simp only [h0, zero_smul, Finset.sum_const_zero, sub_zero]; abel
      simp only [h0, zero_smul, Finset.sum_const_zero, add_zero]
      rw [show ∀ u : V, u - v = u - (∑ a, H.h v (A.es a) • A.e a + A.prF v) from fun u => by rw [← hv']]
      abel
    rw [e]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (e_mem_X A a)))

theorem lamStd_swap : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : LocNG.FrameD H r) (es₂ : Fin r → V) (h1 : ∀ i j, H.h (es₂ i) (es₂ j) = 0) (h2 : ∀ i j : Fin r, H.h (Fr.f i.castSucc) (es₂ j) = if i = j then 1 else 0) (h3 : ∀ i, H.h (es₂ i) (Fr.f (Fin.last r)) = 0), Fr.T ≠ 0 → ∀ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L → ∃ m ∈ Fr.N, (∀ b, m (Fr.f b) = Fr.f b) ∧ (⟨Fr.f, es₂, Fr.T, Fr.h_iso, Fr.h_zz, h1, h2, h3⟩ : LocNG.FrameD H r).LamStd L = LocNG.img m (Fr.LamStd L) := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r Fr es₂ h1 h2 h3 _ L _
  set B : FrameD H r := ⟨Fr.f, es₂, Fr.T, Fr.h_iso, Fr.h_zz, h1, h2, h3⟩ with hB
  have hf : B.f = Fr.f := rfl
  refine ⟨swapEquiv Fr B hf, swap_mem_N Fr B hf, fun b => swap_fix Fr B hf b, ?_⟩

  have key : ∀ x : V, ((∀ a, H.h x (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h x (Fr.e a) ∈ M.L.O) ∧
      ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF x ∧ H.mkW Fr.f w ∈ L) ↔
      ((∀ a, H.h (swapMap Fr B x) (B.es a) ∈ M.L.O) ∧ (∀ a, H.h (swapMap Fr B x) (B.e a) ∈ M.L.O) ∧
      ∃ w : ↥(H.perp (H.X B.f)), (w : V) = B.prF (swapMap Fr B x) ∧ H.mkW B.f w ∈ L) := by
    intro x
    have hmem := swap_prF_mem Fr B hf x
    have hcls : ∀ (w w' : ↥(H.perp (H.X Fr.f))), (w : V) = Fr.prF x → (w' : V) = B.prF (swapMap Fr B x) →
        H.mkW Fr.f w = H.mkW Fr.f w' := by
      intro w w' hw hw'
      unfold HermSp.mkW
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      show (w : V) - w' ∈ H.X Fr.f
      rw [hw, hw', ← neg_sub]
      exact Submodule.neg_mem _ hmem
    simp only [swap_es Fr B hf, e_eq Fr B hf, swap_e Fr B hf]
    refine and_congr Iff.rfl (and_congr Iff.rfl ⟨?_, ?_⟩)
    · rintro ⟨w, hw, hwL⟩
      refine ⟨⟨B.prF (swapMap Fr B x), prF_mem_perp' B _⟩, rfl, ?_⟩
      rw [← hcls w _ hw rfl]; exact hwL
    · rintro ⟨w', hw', hwL⟩
      refine ⟨⟨Fr.prF x, prF_mem_perp' Fr _⟩, rfl, ?_⟩
      rw [hcls _ w' rfl hw']; exact hwL
  unfold FrameD.LamStd img
  rw [Submodule.map_span]
  congr 1
  ext v
  constructor
  · intro hv
    refine ⟨swapMap B Fr v, (key _).2 ?_, ?_⟩
    · rw [swap_inv B Fr hf.symm v]; exact hv
    · exact swap_inv B Fr hf.symm v
  · rintro ⟨x, hx, rfl⟩
    exact (key x).1 hx

end GlobalTheory.SwapStd
