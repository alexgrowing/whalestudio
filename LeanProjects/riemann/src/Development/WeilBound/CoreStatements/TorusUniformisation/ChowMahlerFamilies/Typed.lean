import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData

open GlobalTheory.CompanionTheory.Ar.Num
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

theorem typed {O C : Type} [CommRing O] [Field C] [Algebra O C] (RC : Subalgebra O C) (v : Valuation C NNReal)
    (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) (p w : C) (hw0 : w ≠ 0) (hw1 : v w < 1) (hpw : v p ≤ v w * v w) (c P : RC)
    (hc : v (c : C) = v w) (hP : (P : C) = p)
    {I : Type} [Fintype I] [DecidableEq I] {g n r s : ℕ} (AF : Submodule RC (I → RC))
    (Hm : Matrix (Fin g) I RC) (Eg Ei : Matrix I I RC) (hEi : Ei * Eg = 1)
    (h0 : ∀ l, c • l ∈ AF) (h1 : ∀ k, Hm k ∈ AF) (h2 : ∀ y, y ᵥ* Eg ∈ AF → ∃ u, Hm *ᵥ y = c • u)
    (h3 : ∀ u : Fin g → RC, ∃ (y : I → RC) (u' : Fin g → RC), y ᵥ* Eg ∈ AF ∧ Hm *ᵥ y = c • u + P • u')
    (h4 : ∀ u : Fin g → RC, ∃ x : I → C, (∀ l ∈ AF, v (∑ j, algebraMap RC C (l j) * x j) ≤ 1) ∧
      Hm.map (algebraMap RC C) *ᵥ x = fun k => algebraMap RC C (u k))
    (Pm : Matrix (Fin n) I RC) (Jm : Matrix I (Fin n) RC) (hPJ : Pm * Jm = 1)
    (hst : ∀ l ∈ AF, l ᵥ* (Jm * Pm) ∈ AF) (hh : AddSubgroup (Fin n → C))
    (hhh : ∀ u, u ∈ hh ↔ ∀ l ∈ AF, (∑ j, (l j : C) * (Jm.map (algebraMap RC C)).mulVec u j) ∈ RC)
    (evs : Fin s → ((Fin g → C) →ₗ[C] C)) (evr : Fin r → ((Fin g → C) →ₗ[C] C))
    (om : AddSubgroup (Fin s → C)) (lie W : AddSubgroup (Fin r → C))
    (hom : ∀ z, z ∈ om ↔ ∃ u : Fin g → RC, ∀ k, z k = evs k fun j => (u j : C))
    (hlie : ∀ a, a ∈ lie ↔ ∀ u : Fin g → RC, ∑ k, a k * evr k (fun j => (u j : C)) ∈ RC)
    (hlW : lie ≤ W) (hWl : ∀ a ∈ W, w • a ∈ lie)
    (q : (Fin n → C) →ₗ[C] (Fin s → C))
    (hq : ∀ m, ∃ u : Fin g → RC, ∀ k,
      evs k (fun j => (Hm j m : C)) - q (fun i => (Pm i m : C)) k = p * evs k fun j => (u j : C))
    (i' hb : (Fin r → C) →ₗ[C] (Fin n → C))
    (hdual : ∀ a ∈ W, ∀ m, v (∑ m', (Eg m m' : C) * (Jm.map (algebraMap RC C) *ᵥ i' a) m' +
      ∑ k, a k * evr k fun j => (Hm j m : C)) ≤ v w)
    (hW : (stdLat RC _).comap hb.toAddMonoidHom = W) (hcl : ∀ a ∈ W, hb a - i' a ∈ mulLat w (stdLat RC _)) :
    hh.map q.toAddMonoidHom = om ∧ hh.comap hb.toAddMonoidHom = divLat w lie := by
  have hvw : v w ≠ 0 := (Valuation.ne_zero_iff v).2 hw0
  have hvw' : 0 < v w := pos_iff_ne_zero.2 hvw
  have hle : ∀ a : RC, v (a : C) ≤ 1 := fun a => (hv _).1 a.2
  have htw : v (p / w) ≤ v w := by rw [map_div₀, div_le_iff₀ hvw']; exact hpw
  let t : RC := ⟨p / w, (hv _).2 (htw.trans hw1.le)⟩
  have hint : ∀ x : I → C, (∀ l ∈ AF, v (∑ j, (l j : C) * x j) ≤ 1) → ∀ m, w * x m ∈ RC := fun x hx m => by
    have := hx _ (h0 (Pi.single m 1))
    rw [Finset.sum_eq_single m (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)] at this
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, map_mul, hc] at this
    rw [hv, map_mul]
    exact this
  have hev : ∀ (f : (Fin g → C) →ₗ[C] C) (x : I → C),
      f (Hm.map (algebraMap RC C) *ᵥ x) = ∑ m, x m * f fun j => (Hm j m : C) := fun f x => by
    have : Hm.map (algebraMap RC C) *ᵥ x = ∑ m, x m • fun j => (Hm j m : C) := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.map_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [this, map_sum]
    simp only [map_smul, smul_eq_mul]
  have key : ∀ x : I → C, (∀ m, w * x m ∈ RC) → ∃ u : Fin g → RC, ∀ k,
      q (Pm.map (algebraMap RC C) *ᵥ x) k = evs k (Hm.map (algebraMap RC C) *ᵥ x) - (t : C) * evs k fun j => (u j : C) := by
    intro x hx
    choose U hU using hq
    refine ⟨∑ m, (⟨_, hx m⟩ : RC) • U m, fun k => ?_⟩
    have e1 : Pm.map (algebraMap RC C) *ᵥ x = ∑ m, x m • fun i => (Pm i m : C) := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.map_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have e2 : (fun j => (((∑ m, (⟨_, hx m⟩ : RC) • U m) j : RC) : C)) = ∑ m, (w * x m) • fun j => (U m j : C) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul]
    rw [hev, e1, e2, map_sum, map_sum, Finset.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    have e3 : (t : C) * w = p := div_mul_cancel₀ p hw0
    linear_combination (-x m) * hU m k + (x m * evs k fun j => (U m j : C)) * e3
  have hPJ' : ∀ u : Fin n → C, Pm.map (algebraMap RC C) *ᵥ (Jm.map (algebraMap RC C) *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hPJ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  have hdot : ∀ {K : Type} [Fintype K] (l : I → RC) (M : Matrix I K RC) (x : K → C),
      ∑ j, (l j : C) * (M.map (algebraMap RC C) *ᵥ x) j = ∑ j, ((l ᵥ* M) j : C) * x j := fun l M x => by
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul,
      Finset.mul_sum, Finset.sum_mul, Matrix.map_apply, mul_assoc]
    exact Finset.sum_comm
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · rintro _ ⟨u₀, hu₀, rfl⟩
    have hu := (hhh u₀).1 hu₀
    obtain ⟨u, e⟩ := key _ (hint _ fun l hl => (hv _).1 (hu l hl))
    rw [hPJ'] at e
    refine (hom _).2 ⟨(fun j => ⟨_, hu _ (h1 j)⟩) - t • u, fun k => (e k).trans ?_⟩
    rw [← smul_eq_mul, ← map_smul, ← map_sub]
    rfl
  · let N : Submodule RC (Fin g → RC) :=
      { carrier := {u | ∃ x ∈ hh, ∀ k, q x k = evs k fun j => (u j : C)}
        add_mem' := by
          rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
          refine ⟨x + y, hh.add_mem hx hy, fun k => ?_⟩
          rw [map_add, Pi.add_apply, ha, hb, ← map_add]
          rfl
        zero_mem' := ⟨0, hh.zero_mem, fun k => by rw [map_zero]; exact (map_zero (evs k)).symm⟩
        smul_mem' := by
          rintro a b ⟨x, hx, hb⟩
          refine ⟨(a : C) • x, (hhh _).2 fun l hl => ?_, fun k => ?_⟩
          · convert RC.mul_mem a.2 ((hhh _).1 hx l hl) using 1
            simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]
          · rw [map_smul, Pi.smul_apply, hb, ← map_smul]
            rfl }
    have hjac : Ideal.span {t} ≤ (⊥ : Ideal RC).jacobson := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_jacobson_bot]
      intro y
      have h1 : v ((t * y + 1 : RC) : C) = 1 := by
        rw [add_comm]
        refine v.map_one_add_of_lt ?_
        change v ((t : C) * y) < 1
        rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (htw.trans_lt hw1) (hle y)
      have h0 : ((t * y + 1 : RC) : C) ≠ 0 := fun h => by rw [h, map_zero] at h1; exact zero_ne_one h1
      refine IsUnit.of_mul_eq_one ⟨((t * y + 1 : RC) : C)⁻¹, (hv _).2 (by rw [map_inv₀, h1, inv_one])⟩ ?_
      exact Subtype.ext (mul_inv_cancel₀ h0)
    have hN : (⊤ : Submodule RC (Fin g → RC)) ≤ N := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hjac fun u _ => ?_
      obtain ⟨x, hx, hxu⟩ := h4 u
      obtain ⟨u', e⟩ := key x (hint x hx)
      refine Submodule.mem_sup.2 ⟨u - t • u', ⟨Pm.map (algebraMap RC C) *ᵥ x, (hhh _).2 fun l hl => ?_, fun k => ?_⟩,
        t • u', Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) Submodule.mem_top, sub_add_cancel _ _⟩
      · rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hdot]
        exact (hv _).2 (hx _ (hst l hl))
      · rw [e, hxu, ← smul_eq_mul, ← map_smul, ← map_sub]
        rfl
    intro z hz
    obtain ⟨u, hu⟩ := (hom z).1 hz
    obtain ⟨x, hx, e⟩ := hN (Submodule.mem_top (x := u))
    exact ⟨x, hx, funext fun k => (e k).trans (hu k).symm⟩
  · have est : ∀ a : Fin r → C, w • a ∈ W → ∀ y : I → RC,
        (∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ hb a) j ∈ RC ↔
          v (∑ k, (w • a) k * evr k fun j => ((Hm *ᵥ y) j : C)) ≤ v w) := by
      intro a ha y
      obtain ⟨z, hz, e⟩ := hcl _ ha
      have hz' : ∀ k, z k ∈ RC := fun k => hz k (Set.mem_univ k)
      have e1 : w • hb a = i' (w • a) + w • z := by
        rw [← map_smul hb, ← sub_eq_iff_eq_add', ← e]; rfl
      have e2 : w * ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ hb a) j =
          ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) j +
            w * ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ z) j := by
        have := congrArg (fun x => ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ x) j) e1
        simpa only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
          Finset.sum_add_distrib, mul_left_comm _ w, ← Finset.mul_sum] using this
      have e3 : v (w * ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ z) j) ≤ v w := by
        rw [map_mul]
        refine mul_le_of_le_one_right zero_le ((hv _).1 ?_)
        rw [hdot]
        exact RC.sum_mem fun j _ => RC.mul_mem (Subtype.prop _) (hz' j)
      have e4 : ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) j +
          ∑ k, (w • a) k * evr k (fun j => ((Hm *ᵥ y) j : C)) =
          ∑ m, (y m : C) * (∑ m', (Eg m m' : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) m' +
            ∑ k, (w • a) k * evr k fun j => (Hm j m : C)) := by
        have : (fun j => ((Hm *ᵥ y) j : C)) = Hm.map (algebraMap RC C) *ᵥ fun m => (y m : C) := by
          funext j
          simp only [Matrix.mulVec, dotProduct, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, Matrix.map_apply]
          rfl
        rw [this, ← hdot]
        simp only [hev, mul_add, Finset.sum_add_distrib]
        congr 1
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        simp only [mul_left_comm]
      have e5 : v (∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) j +
          ∑ k, (w • a) k * evr k (fun j => ((Hm *ᵥ y) j : C))) ≤ v w := by
        rw [e4]
        refine v.map_sum_le fun m _ => ?_
        rw [map_mul]
        exact (mul_le_of_le_one_left zero_le (hle _)).trans (hdual _ ha m)
      have e6 := v.map_add_le e5 e3
      rw [add_right_comm, ← e2] at e6
      rw [hv, ← mul_le_mul_iff_right₀ hvw', mul_one, ← map_mul]
      constructor
      · intro h
        simpa using v.map_sub_le e6 h
      · intro h
        simpa using v.map_sub_le e6 h
    have hlin : ∀ (a : Fin r → C) (b : RC) (u : Fin g → RC), ∑ k, a k * evr k (fun j => ((b • u) j : C)) =
        (b : C) * ∑ k, a k * evr k (fun j => (u j : C)) := fun a b u => by
      have : (fun j => ((b • u) j : C)) = (b : C) • fun j => (u j : C) := rfl
      simp only [this, map_smul, smul_eq_mul, Finset.mul_sum, mul_left_comm]
    ext a
    change hb a ∈ hh ↔ w • a ∈ lie
    rw [hhh]
    constructor
    · intro h
      have ha : w • a ∈ W := by
        rw [← hW]
        intro k _
        have h5 := (hv _).1 (h _ (h0 (Pm k)))
        have h6 : ∑ j, ((c • Pm k) j : C) * (Jm.map (algebraMap RC C) *ᵥ hb a) j = (c : C) * hb a k := by
          conv_rhs => rw [← hPJ' (hb a)]
          generalize Jm.map (algebraMap RC C) *ᵥ hb a = x
          simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, MulMemClass.coe_mul, Finset.mul_sum,
            mul_assoc, Matrix.map_apply]
          rfl
        rw [h6, map_mul, hc, ← map_mul] at h5
        change hb (w • a) k ∈ RC
        rw [map_smul]
        exact (hv _).2 h5
      refine (hlie _).2 fun u => ?_
      obtain ⟨y, u', hy, e⟩ := h3 u
      have h5 := (est a ha y).1 (h _ hy)
      have h6 : ∑ k, (w • a) k * evr k (fun j => ((Hm *ᵥ y) j : C)) =
          (c : C) * ∑ k, (w • a) k * evr k (fun j => (u j : C)) +
            (p / w) * ∑ k, (w • w • a) k * evr k (fun j => (u' j : C)) := by
        have : (fun j => ((c • u + P • u') j : C)) = (fun j => ((c • u) j : C)) + fun j => ((P • u') j : C) := rfl
        rw [e, this]
        simp only [map_add, mul_add, Finset.sum_add_distrib, hlin, hP]
        congr 1
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc w, ← Finset.mul_sum]
        field_simp
      have h7 : v ((p / w) * ∑ k, (w • w • a) k * evr k (fun j => (u' j : C))) ≤ v w := by
        rw [map_mul]
        exact (mul_le_of_le_one_right zero_le ((hv _).1 ((hlie _).1 (hWl _ ha) u'))).trans htw
      rw [h6] at h5
      have h8 := v.map_sub_le h5 h7
      rw [add_sub_cancel_right, map_mul, hc] at h8
      rw [hv]
      exact (mul_le_iff_le_one_right hvw').1 h8
    · intro h l hl
      have hl' : (l ᵥ* Ei) ᵥ* Eg = l := by rw [Matrix.vecMul_vecMul, hEi, Matrix.vecMul_one]
      rw [← hl'] at hl ⊢
      obtain ⟨u, e⟩ := h2 _ hl
      rw [est a (hlW h), e, hlin, map_mul, hc]
      exact mul_le_of_le_one_right zero_le ((hv _).1 ((hlie _).1 h u))

end PositivityTheory.Xgn.TestGroupPoint
