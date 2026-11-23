import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.AnisoPeelAlt

open Finset Module

namespace DensInertW.Sub

variable {L : Type} [Field L]

theorem q_ne_zero_of_inv {q : ℕ} (hinv : ∀ a : L, (a ^ q) ^ q = a) : q ≠ 0 := by
  intro hq
  subst hq
  have h := hinv 0
  simp at h

def sig (q : ℕ) (hq : q ≠ 0) (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) : L →+* L where
  toFun a := a ^ q
  map_one' := one_pow q
  map_mul' a b := mul_pow a b q
  map_zero' := zero_pow hq
  map_add' := hadd

theorem sig_apply (q : ℕ) (hq : q ≠ 0) (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (a : L) :
    sig q hq hadd a = a ^ q := rfl

section
variable {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}

theorem hf_add_left (x x' y : Fin n → L) : hf q M (x + x') y = hf q M x y + hf q M x' y := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hf_smul_left (c : L) (x y : Fin n → L) : hf q M (c • x) y = c * hf q M x y := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem hf_zero_left (y : Fin n → L) : hf q M 0 y = 0 := by
  simp [hf]

theorem hf_sub_left (x x' y : Fin n → L) : hf q M (x - x') y = hf q M x y - hf q M x' y := by
  simp only [hf, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

def hfL (q : ℕ) (M : Matrix (Fin n) (Fin n) L) (y : Fin n → L) : (Fin n → L) →ₗ[L] L where
  toFun x := hf q M x y
  map_add' x x' := hf_add_left x x' y
  map_smul' c x := by simp only [hf_smul_left, smul_eq_mul, RingHom.id_apply]

theorem hfL_apply (y x : Fin n → L) : hfL q M y x = hf q M x y := rfl

theorem hf_add_right (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (x y y' : Fin n → L) :
    hf q M x (y + y') = hf q M x y + hf q M x y' := by
  simp only [hf, Pi.add_apply, hadd, mul_add, Finset.sum_add_distrib]

theorem hf_smul_right (x : Fin n → L) (c : L) (y : Fin n → L) :
    hf q M x (c • y) = c ^ q * hf q M x y := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, mul_pow]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem hf_sub_right (hq : q ≠ 0) (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q)
    (x y y' : Fin n → L) : hf q M x (y - y') = hf q M x y - hf q M x y' := by
  have hs : ∀ a b : L, (a - b) ^ q = a ^ q - b ^ q := fun a b => by
    have h := hadd (a - b) b
    rw [sub_add_cancel] at h
    rw [h]
    ring
  simp only [hf, Pi.sub_apply, hs, mul_sub, Finset.sum_sub_distrib]

theorem hf_zero_right (hq : q ≠ 0) (x : Fin n → L) : hf q M x 0 = 0 := by
  simp [hf, zero_pow hq]

theorem hf_symm (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (hinv : ∀ a : L, (a ^ q) ^ q = a)
    (hM : ∀ k l, M l k = M k l ^ q) (x y : Fin n → L) : hf q M y x = (hf q M x y) ^ q := by
  have hq := q_ne_zero_of_inv hinv
  have e : (hf q M x y) ^ q = sig q hq hadd (hf q M x y) := rfl
  rw [e]
  simp only [hf, map_sum, map_mul, map_pow, sig_apply, hinv]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hM]
  ring

end

section geom
variable {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}

theorem hf_eq_zero_of_diag (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q)
    (hinv : ∀ a : L, (a ^ q) ^ q = a) (hM : ∀ k l, M l k = M k l ^ q)
    (htr : ∀ z : L, z ≠ 0 → ∃ c : L, c * z + (c * z) ^ q ≠ 0)
    (W : Submodule L (Fin n → L)) (h0 : ∀ v ∈ W, hf q M v v = 0) :
    ∀ x ∈ W, ∀ y ∈ W, hf q M x y = 0 := by
  intro x hx y hy
  have key : ∀ c : L, c * hf q M x y + (c * hf q M x y) ^ q = 0 := by
    intro c
    have h1 := h0 (c • x + y) (W.add_mem (W.smul_mem c hx) hy)
    rw [hf_add_left, hf_add_right hadd, hf_add_right hadd, h0 _ (W.smul_mem c hx), h0 y hy,
      hf_symm hadd hinv hM (c • x) y, hf_smul_left] at h1
    linear_combination h1
  by_contra hz
  obtain ⟨c, hc⟩ := htr _ hz
  exact hc (key c)

theorem finrank_inf_ker_add_one (W : Submodule L (Fin n → L)) (f : (Fin n → L) →ₗ[L] L)
    (u : Fin n → L) (hu : u ∈ W) (hfu : f u ≠ 0) :
    finrank L ↥(W ⊓ LinearMap.ker f) + 1 = finrank L ↥W := by
  have hsurj : LinearMap.range f = ⊤ := by
    refine LinearMap.range_eq_top.mpr fun a => ⟨(a / f u) • u, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfu]
  have hr : finrank L (LinearMap.range f) = 1 := by
    rw [hsurj, finrank_top, Module.finrank_self]
  have hk := LinearMap.finrank_range_add_finrank_ker f
  rw [hr, Module.finrank_fin_fun] at hk
  have hsup : W ⊔ LinearMap.ker f = ⊤ := by
    refine eq_top_iff.mpr fun v _ => Submodule.mem_sup.mpr
      ⟨(f v / f u) • u, W.smul_mem _ hu, v - (f v / f u) • u, ?_, by abel⟩
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfu, sub_self]
  have h := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker f)
  rw [hsup, finrank_top, Module.finrank_fin_fun] at h
  omega

theorem finrank_perp_aniso (W : Submodule L (Fin n → L)) (e : Fin n → L) (he : e ∈ W)
    (hee : hf q M e e ≠ 0) :
    finrank L ↥(W ⊓ LinearMap.ker (hfL q M e)) + 1 = finrank L ↥W :=
  finrank_inf_ker_add_one W _ e he hee

theorem sub_mem_perp (W : Submodule L (Fin n → L)) (e : Fin n → L) (he : e ∈ W)
    (hee : hf q M e e ≠ 0) (w : Fin n → L) (hw : w ∈ W) :
    w - (hf q M w e / hf q M e e) • e ∈ W ⊓ LinearMap.ker (hfL q M e) := by
  refine Submodule.mem_inf.2 ⟨W.sub_mem hw (W.smul_mem _ he), ?_⟩
  rw [LinearMap.mem_ker, hfL_apply, hf_sub_left, hf_smul_left, div_mul_cancel₀ _ hee, sub_self]

theorem nondeg_perp_aniso (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q)
    (W : Submodule L (Fin n → L)) (hW : NonDeg q M W) (e : Fin n → L) (he : e ∈ W)
    (hee : hf q M e e ≠ 0) : NonDeg q M (W ⊓ LinearMap.ker (hfL q M e)) := by
  intro w hw hperp
  have hw' := Submodule.mem_inf.1 hw
  have hwe : hf q M w e = 0 := LinearMap.mem_ker.1 hw'.2
  apply hW w hw'.1
  intro v hv
  have h1 := hperp _ (sub_mem_perp W e he hee v hv)
  have hsplit : v = (v - (hf q M v e / hf q M e e) • e) + (hf q M v e / hf q M e e) • e :=
    (sub_add_cancel _ _).symm
  rw [hsplit, hf_add_right hadd, h1, hf_smul_right, hwe]
  ring

theorem not_mem_perp_aniso (W : Submodule L (Fin n → L)) (e : Fin n → L)
    (hee : hf q M e e ≠ 0) : e ∉ W ⊓ LinearMap.ker (hfL q M e) :=
  fun h => hee (LinearMap.mem_ker.1 (Submodule.mem_inf.1 h).2)

theorem hyperbolic (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q)
    (hinv : ∀ a : L, (a ^ q) ^ q = a) (hM : ∀ k l, M l k = M k l ^ q)
    (htrs : ∀ s : L, s ^ q = s → ∃ t : L, t + t ^ q = s)
    (W : Submodule L (Fin n → L)) (hW : NonDeg q M W) (x : Fin n → L) (hx : x ∈ W)
    (hx0 : x ≠ 0) (hxx : hf q M x x = 0) :
    ∃ y ∈ W, hf q M x y = 1 ∧ hf q M y y = 0 ∧
      finrank L ↥(W ⊓ LinearMap.ker (hfL q M x) ⊓ LinearMap.ker (hfL q M y)) + 2 =
        finrank L ↥W ∧
      NonDeg q M (W ⊓ LinearMap.ker (hfL q M x) ⊓ LinearMap.ker (hfL q M y)) := by
  have hq := q_ne_zero_of_inv hinv
  obtain ⟨v, hv, hz⟩ : ∃ v ∈ W, hf q M x v ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx0 (hW x hx hc)
  set y1 := ((hf q M x v)⁻¹) ^ q • v with hy1
  have hy1W : y1 ∈ W := W.smul_mem _ hv
  have hxy1 : hf q M x y1 = 1 := by
    rw [hy1, hf_smul_right, hinv, inv_mul_cancel₀ hz]
  clear_value y1
  have hy1x : hf q M y1 x = 1 := by
    rw [hf_symm hadd hinv hM x y1, hxy1, one_pow]
  have hs : (hf q M y1 y1) ^ q = hf q M y1 y1 := (hf_symm hadd hinv hM y1 y1).symm
  have hneg : (-hf q M y1 y1) ^ q = -hf q M y1 y1 := by
    have h := hadd (hf q M y1 y1) (-hf q M y1 y1)
    rw [add_neg_cancel, zero_pow hq] at h
    linear_combination -h - hs
  obtain ⟨t, ht⟩ := htrs _ hneg
  set y := y1 + t • x with hy
  have hyW : y ∈ W := W.add_mem hy1W (W.smul_mem _ hx)
  clear_value y
  have hxy : hf q M x y = 1 := by
    rw [hy, hf_add_right hadd, hf_smul_right, hxx, mul_zero, add_zero, hxy1]
  have hyy : hf q M y y = 0 := by
    rw [hy, hf_add_left, hf_add_right hadd, hf_add_right hadd, hf_smul_left, hf_smul_left,
      hf_smul_right, hf_smul_right, hxx, hy1x, hxy1]
    linear_combination ht
  have hyx : hf q M y x = 1 := by
    rw [hf_symm hadd hinv hM x y, hxy, one_pow]
  refine ⟨y, hyW, hxy, hyy, ?_, ?_⟩
  · have h1 := finrank_inf_ker_add_one W (hfL q M y) x hx
      (by rw [hfL_apply, hxy]; exact one_ne_zero)
    have h2 := finrank_inf_ker_add_one (W ⊓ LinearMap.ker (hfL q M y)) (hfL q M x) y
      (Submodule.mem_inf.2 ⟨hyW, by rw [LinearMap.mem_ker, hfL_apply, hyy]⟩)
      (by rw [hfL_apply, hyx]; exact one_ne_zero)
    rw [inf_right_comm]
    omega
  · intro w hw hperp
    have hw' := Submodule.mem_inf.1 hw
    have hw'' := Submodule.mem_inf.1 hw'.1
    have hwx : hf q M w x = 0 := LinearMap.mem_ker.1 hw''.2
    have hwy : hf q M w y = 0 := LinearMap.mem_ker.1 hw'.2
    apply hW w hw''.1
    intro u hu
    have hu' : u - hf q M u y • x - hf q M u x • y ∈
        W ⊓ LinearMap.ker (hfL q M x) ⊓ LinearMap.ker (hfL q M y) := by
      refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2
        ⟨W.sub_mem (W.sub_mem hu (W.smul_mem _ hx)) (W.smul_mem _ hyW), ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, hfL_apply, hf_sub_left, hf_sub_left, hf_smul_left, hf_smul_left,
          hxx, hyx]
        ring
      · rw [LinearMap.mem_ker, hfL_apply, hf_sub_left, hf_sub_left, hf_smul_left, hf_smul_left,
          hxy, hyy]
        ring
    have h0 := hperp _ hu'
    have hsplit : u = (u - hf q M u y • x - hf q M u x • y) + hf q M u y • x + hf q M u x • y := by
      abel
    rw [hsplit, hf_add_right hadd, hf_add_right hadd, h0, hf_smul_right, hf_smul_right, hwx, hwy]
    ring

end geom

end DensInertW.Sub
