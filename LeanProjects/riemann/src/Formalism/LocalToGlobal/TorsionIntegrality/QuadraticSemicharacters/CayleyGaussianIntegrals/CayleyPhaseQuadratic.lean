import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.UnitaryConstant
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section Phi

variable {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ}
  {δ Ae : V ≃ₗ[ℂ] V}

theorem ud_isom_symm (h : UnitaryData H Λ α δ Ae) (x y : V) : H (δ.symm x) (δ.symm y) = H x y := by
  simpa using (h.isom (δ.symm x) (δ.symm y)).symm

theorem ud_adj (h : UnitaryData H Λ α δ Ae) (x y : V) :
    H (Ae.symm x) y + H x (Ae.symm y) = H x y := by
  obtain ⟨a, rfl⟩ : ∃ a, Ae a = x := ⟨Ae.symm x, Ae.apply_symm_apply x⟩
  obtain ⟨b, rfl⟩ : ∃ b, Ae b = y := ⟨Ae.symm y, Ae.apply_symm_apply y⟩
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  simp only [h.cay, map_sub, LinearMap.sub_apply, ud_isom_symm h]
  ring

theorem ud_skew (h : UnitaryData H Λ α δ Ae) (x y : V) : H (cayC Ae x) y = -H x (cayC Ae y) := by
  have h1 := ud_adj h x y
  have hc : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 :=
    Complex.conj_eq_iff_real.mpr ⟨1 / 2, by first | norm_num | simp | (push_cast; ring)⟩
  simp only [cayC, map_sub, map_smul, map_smulₛₗ, RingHom.id_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hc]
  linear_combination h1

theorem ud_re (h : UnitaryData H Λ α δ Ae) (x : V) : (H (cayC Ae x) x).re = 0 := by
  have h1 := ud_skew h x x
  rw [h.herm (cayC Ae x) x] at h1
  have h2 := congrArg Complex.re h1
  simp only [Complex.neg_re, Complex.conj_re] at h2
  linarith

theorem ud_int (h : UnitaryData H Λ α δ Ae) {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    ∃ m : ℤ, altE H x y = (m : ℝ) := by
  obtain ⟨hpm, hmul⟩ := h.semi
  have hsq : ∀ z ∈ Λ, α z ^ 2 = 1 := by
    intro z hz
    rcases hpm z hz with h' | h' <;> rw [h'] <;> norm_num
  have e := congrArg (· ^ 2) (hmul x hx y hy)
  simp only [mul_pow, hsq x hx, hsq y hy, hsq _ (Λ.add_mem hx hy), one_mul] at e
  rw [sq, ← Complex.exp_add] at e
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp e.symm
  refine ⟨n, ?_⟩
  have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  have h3 : ((altE H x y : ℝ) : ℂ) = ((n : ℤ) : ℂ) := by
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hpi)
    linear_combination hn
  exact_mod_cast h3

theorem ud_norm (h : UnitaryData H Λ α δ Ae) {x : V} (hx : x ∈ Λ) : ‖phiC H α Ae x‖ = 1 := by
  unfold phiC
  rw [norm_mul, Complex.norm_exp]
  have hre : (-(Real.pi : ℂ) * H (cayC Ae x) x).re = 0 := by
    simp [Complex.mul_re, ud_re h x]
  rw [hre, Real.exp_zero, mul_one]
  rcases h.semi.1 x hx with h' | h' <;> simp [h']

theorem altE_cayC (x y : V) :
    altE H (cayC Ae x) y = altE H (Ae.symm x) y - altE H x y / 2 := by
  have key : ∀ z : ℂ, ((1 / 2 : ℂ) * z).im = z.im / 2 := by
    intro z
    have e : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by first | norm_num | simp | (push_cast; ring)
    rw [e, Complex.im_ofReal_mul]
    ring
  simp only [altE, cayC, map_sub, map_smul, map_smulₛₗ, RingHom.id_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, Complex.sub_im, key]

theorem cayC_add (x y : V) : cayC Ae (x + y) = cayC Ae x + cayC Ae y := by
  simp only [cayC, map_add, smul_add]
  abel

theorem ud_phi_add (h : UnitaryData H Λ α δ Ae) {x x' : V} (hx : x ∈ Λ) (hx' : x' ∈ Λ) :
    phiC H α Ae (x + x') = phiC H α Ae x * phiC H α Ae x' * bC H Ae x x' := by
  obtain ⟨m, hm⟩ := ud_int h hx hx'
  have h1 : H (cayC Ae x') x = -conj (H (cayC Ae x) x') := by
    rw [ud_skew h x' x, h.herm (cayC Ae x) x']
  have h2 : H (cayC Ae x) x' - conj (H (cayC Ae x) x')
      = 2 * Complex.I * (altE H (cayC Ae x) x' : ℂ) := by
    rw [← h.herm (cayC Ae x) x']
    exact herm_sub_swap H h.herm _ _
  have h3 : (altE H (cayC Ae x) x' : ℂ)
      = (altE H (Ae.symm x) x' : ℂ) - (altE H x x' : ℂ) / 2 := by
    rw [altE_cayC]; push_cast; rfl
  have h4 : (altE H x x' : ℂ) = (m : ℂ) := by rw [hm]; push_cast; rfl
  have key : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x x' : ℂ))
        * Complex.exp (-(Real.pi : ℂ) * H (cayC Ae (x + x')) (x + x'))
      = Complex.exp (-(Real.pi : ℂ) * H (cayC Ae x) x) * Complex.exp (-(Real.pi : ℂ) * H (cayC Ae x') x')
        * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H (Ae.symm x) x' : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨m, ?_⟩
    simp only [cayC_add, map_add, LinearMap.add_apply]
    linear_combination (-(Real.pi : ℂ)) * h1 + (-(Real.pi : ℂ)) * h2
      + (-(2 * (Real.pi : ℂ) * Complex.I)) * h3 + (2 * (Real.pi : ℂ) * Complex.I) * h4
  simp only [phiC, bC]
  rw [h.semi.2 x hx x' hx']
  linear_combination (α x * α x') * key

theorem ud_b_symm (h : UnitaryData H Λ α δ Ae) {x x' : V} (hx : x ∈ Λ) (hx' : x' ∈ Λ) :
    bC H Ae x x' = bC H Ae x' x := by
  unfold bC
  obtain ⟨m, hm⟩ := ud_int h hx hx'
  have h1 := congrArg Complex.im (ud_adj h x x')
  rw [Complex.add_im, h.herm (Ae.symm x') x, Complex.conj_im] at h1
  have h2 : altE H (Ae.symm x) x' = altE H (Ae.symm x') x + m := by
    unfold altE
    rw [← hm]
    unfold altE
    linarith
  rw [h2, Complex.ofReal_add, mul_add, Complex.exp_add]
  have h3 : Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (((m : ℤ) : ℝ) : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨-m, by push_cast; ring⟩
  rw [h3, mul_one]

theorem bC_add_left (x x' x'' : V) : bC H Ae (x + x') x'' = bC H Ae x x'' * bC H Ae x' x'' := by
  unfold bC
  rw [← Complex.exp_add]
  congr 1
  simp only [altE, map_add, LinearMap.add_apply, Complex.add_im, Complex.ofReal_add]
  ring

theorem mem_latA {x : V} : x ∈ latA Λ δ Ae ↔ ∃ w ∈ Λ, δ w ∈ Λ ∧ Ae (δ w) = x := by
  simp only [latA, imgLat, AddSubgroup.mem_map, AddSubgroup.mem_inf]
  constructor
  · rintro ⟨z, ⟨hz, w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, hz, rfl⟩
  · rintro ⟨w, hw, hδ, rfl⟩
    exact ⟨δ w, ⟨hδ, w, hw, rfl⟩, rfl⟩

theorem ud_latA_le (h : UnitaryData H Λ α δ Ae) : latA Λ δ Ae ≤ Λ := by
  intro x hx
  obtain ⟨w, hw, hδ, rfl⟩ := mem_latA.mp hx
  rw [h.cay, LinearEquiv.symm_apply_apply]
  exact Λ.sub_mem hδ hw

theorem ud_radical_of_mem (h : UnitaryData H Λ α δ Ae) {x : V} (hx : x ∈ latA Λ δ Ae) {x' : V}
    (hx' : x' ∈ Λ) : bC H Ae x x' = 1 := by
  obtain ⟨w, hw, hδ, rfl⟩ := mem_latA.mp hx
  obtain ⟨m, hm⟩ := ud_int h hδ hx'
  unfold bC
  rw [LinearEquiv.symm_apply_apply, hm, Complex.exp_eq_one_iff]
  exact ⟨-m, by push_cast; ring⟩

theorem ud_radical (h : UnitaryData H Λ α δ Ae) {x : V} (hx : x ∈ Λ)
    (hb : ∀ x' ∈ Λ, bC H Ae x x' = 1) : x ∈ latA Λ δ Ae := by
  have hz : Ae.symm x ∈ Λ := by
    have hd : Ae.symm x ∈ dualLat H Λ := by
      show ∀ y ∈ Λ, ∃ m : ℤ, altE H (Ae.symm x) y = (m : ℝ)
      intro y hy
      have e := hb y hy
      unfold bC at e
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp e
      refine ⟨-n, ?_⟩
      have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
      have h3 : ((altE H (Ae.symm x) y : ℝ) : ℂ) = ((-n : ℤ) : ℂ) := by
        apply mul_left_cancel₀ hpi
        push_cast
        linear_combination -hn
      exact_mod_cast h3
    have hsd : dualLat H Λ = Λ := h.selfDual
    rw [hsd] at hd
    exact hd
  have hc := h.cay (Ae.symm x)
  rw [LinearEquiv.apply_symm_apply] at hc
  have hw : δ.symm (Ae.symm x) ∈ Λ := by
    have e : δ.symm (Ae.symm x) = Ae.symm x - x :=
      calc δ.symm (Ae.symm x) = Ae.symm x - (Ae.symm x - δ.symm (Ae.symm x)) := by abel
        _ = Ae.symm x - x := by rw [← hc]
    rw [e]
    exact Λ.sub_mem hz hx
  exact mem_latA.mpr ⟨δ.symm (Ae.symm x), hw, by rw [LinearEquiv.apply_symm_apply]; exact hz,
    by rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]⟩

theorem ud_phi_latA (h : UnitaryData H Λ α δ Ae) {w : V} (hw : w ∈ Λ) (hy : δ w ∈ Λ) :
    phiC H α Ae (Ae (δ w)) = 1 := by
  have hyd : Ae (δ w) = δ w - w := by rw [h.cay, LinearEquiv.symm_apply_apply]
  have hyΛ : δ w - w ∈ Λ := Λ.sub_mem hy hw
  have h0 : (H w w).im = 0 := by
    have hh := congrArg Complex.im (h.herm w w)
    simp only [Complex.conj_im] at hh
    linarith
  have hcy : cayC Ae (Ae (δ w)) = (1 / 2 : ℂ) • (δ w + w) := by
    rw [cayC, LinearEquiv.symm_apply_apply, hyd]
    module
  have hH : H (cayC Ae (Ae (δ w))) (Ae (δ w)) = Complex.I * (altE H w (δ w) : ℂ) := by
    rw [hcy, hyd]
    simp only [map_smul, map_add, map_sub, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
    have i1 : H (δ w) (δ w) = H w w := h.isom w w
    have i2 : H (δ w) w = (starRingEnd ℂ) (H w (δ w)) := h.herm w (δ w)
    rw [i1, i2]
    have hs := Complex.sub_conj (H w (δ w))
    push_cast at hs
    unfold altE
    linear_combination (1 / 2 : ℂ) * hs
  have hαy : α (Ae (δ w)) = Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H w (δ w) : ℂ)) := by
    have e1 := h.semi.2 _ hyΛ w hw
    rw [sub_add_cancel, h.inv w hw] at e1
    have hE : altE H (δ w - w) w = -altE H w (δ w) := by
      have i2 := congrArg Complex.im (h.herm w (δ w))
      simp only [altE, map_sub, LinearMap.sub_apply, Complex.sub_im, h0, sub_zero]
      simp only [Complex.conj_im] at i2
      exact i2
    rw [hE] at e1
    have hα : α w ^ 2 = 1 := by
      rcases h.semi.1 w hw with h' | h' <;> rw [h'] <;> norm_num
    have hexp : Complex.exp ((Real.pi : ℂ) * Complex.I * ((-altE H w (δ w) : ℝ) : ℂ)) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H w (δ w) : ℂ)) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]
      congr 1
      push_cast
      ring
    rw [hyd]
    linear_combination (-(α w * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H w (δ w) : ℂ)))) * e1 +
      (Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H w (δ w) : ℂ)) - α (δ w - w)) * hα -
      (α (δ w - w) * α w ^ 2) * hexp
  unfold phiC
  rw [hαy, hH, ← Complex.exp_add, ← Complex.exp_zero]
  congr 1
  ring

theorem ud_phi_wd (h : UnitaryData H Λ α δ Ae) {x y : V} (hx : x ∈ Λ) (hy : y ∈ latA Λ δ Ae) :
    phiC H α Ae (x + y) = phiC H α Ae x := by
  have hyΛ := ud_latA_le h hy
  rw [ud_phi_add h hx hyΛ, ud_b_symm h hx hyΛ, ud_radical_of_mem h hy hx]
  obtain ⟨w, hw, hδ, rfl⟩ := mem_latA.mp hy
  rw [ud_phi_latA h hw hδ, mul_one, mul_one]

theorem ud_alpha_nsmul (h : UnitaryData H Λ α δ Ae) {x : V} (hx : x ∈ Λ) (k : ℕ) :
    α (k • x) = α x ^ k := by
  have h0 : (H x x).im = 0 := by
    have hh := congrArg Complex.im (h.herm x x)
    simp only [Complex.conj_im] at hh
    linarith
  induction k with
  | zero =>
    simp only [zero_smul, pow_zero]
    have e := h.semi.2 0 Λ.zero_mem 0 Λ.zero_mem
    rcases h.semi.1 0 Λ.zero_mem with h' | h'
    · exact h'
    · norm_num [altE, h'] at e
  | succ k ih =>
    have hkx : k • x ∈ Λ := Λ.nsmul_mem hx k
    have him : altE H (k • x) x = 0 := by simp [altE, h0]
    rw [succ_nsmul, h.semi.2 _ hkx _ hx, ih, pow_succ, him]
    simp

theorem ud_phi_nsmul (h : UnitaryData H Λ α δ Ae) {x : V} (hx : x ∈ Λ) (k : ℕ) :
    phiC H α Ae (k • x) = phiC H α Ae x ^ (k ^ 2) := by
  have hαsq : α x ^ 2 = 1 := by
    rcases h.semi.1 x hx with h' | h' <;> rw [h'] <;> norm_num
  have h0 : altE H x x = 0 := by
    have hh := congrArg Complex.im (h.herm x x)
    simp only [Complex.conj_im] at hh
    unfold altE
    linarith
  have hHc : H (cayC Ae x) x = Complex.I * (altE H (Ae.symm x) x : ℂ) := by
    apply Complex.ext
    · simp [ud_re h x]
    · have e := altE_cayC (H := H) (Ae := Ae) x x
      rw [h0] at e
      simp only [altE] at e
      simp [e, altE]
  have hsq : phiC H α Ae x ^ 2 = bC H Ae x x := by
    unfold phiC bC
    rw [mul_pow, hαsq, one_mul, ← Complex.exp_nat_mul, hHc]
    congr 1
    push_cast
    ring
  have hbk : ∀ k : ℕ, bC H Ae (k • x) x = bC H Ae x x ^ k := by
    intro k
    induction k with
    | zero => simp [bC, altE]
    | succ k ih => rw [succ_nsmul, bC_add_left, ih, pow_succ]
  induction k with
  | zero =>
    have e := ud_alpha_nsmul h hx 0
    simp only [zero_smul, pow_zero] at e
    simp [phiC, e]
  | succ k ih =>
    have hkx : k • x ∈ Λ := Λ.nsmul_mem hx k
    rw [succ_nsmul, ud_phi_add h hkx hx, ih, hbk k, ← hsq]
    ring

def phiQ (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ) (δ Ae : V ≃ₗ[ℂ] V)
    (c : Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ) : ℂ :=
  phiC H α Ae ((Quotient.out c : Λ) : V)

def bQ (H : Sesq V) (Λ : AddSubgroup V) (δ Ae : V ≃ₗ[ℂ] V)
    (c d : Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ) : ℂ :=
  bC H Ae ((Quotient.out c : Λ) : V) ((Quotient.out d : Λ) : V)

theorem out_mk_latA (x : Λ) : ∃ k ∈ latA Λ δ Ae,
    ((Quotient.out (QuotientAddGroup.mk x : Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ) : Λ) : V)
      = (x : V) + k := by
  have e : -(Quotient.out (QuotientAddGroup.mk x : Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ)) + x ∈
      (latA Λ δ Ae).addSubgroupOf Λ := by
    first
    | (rw [← QuotientAddGroup.eq]; exact Quotient.out_eq _)
    | exact (QuotientAddGroup.eq).mp (Quotient.out_eq (QuotientAddGroup.mk x : Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ))
    | (rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq'])
  refine ⟨-(((-(Quotient.out (QuotientAddGroup.mk x : Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ)) + x : Λ)) : V),
    ?_, ?_⟩
  · exact (latA Λ δ Ae).neg_mem (AddSubgroup.mem_addSubgroupOf.mp e)
  · push_cast
    abel

theorem phiQ_mk (h : UnitaryData H Λ α δ Ae) (x : Λ) :
    phiQ H Λ α δ Ae (QuotientAddGroup.mk x) = phiC H α Ae x := by
  unfold phiQ
  obtain ⟨k, hk, he⟩ := out_mk_latA (δ := δ) (Ae := Ae) x
  rw [he]
  exact ud_phi_wd h x.2 hk

theorem bQ_mk (h : UnitaryData H Λ α δ Ae) (x y : Λ) :
    bQ H Λ δ Ae (QuotientAddGroup.mk x) (QuotientAddGroup.mk y) = bC H Ae x y := by
  unfold bQ
  obtain ⟨k, hk, hek⟩ := out_mk_latA (δ := δ) (Ae := Ae) x
  obtain ⟨k', hk', hek'⟩ := out_mk_latA (δ := δ) (Ae := Ae) y
  rw [hek, hek']
  have hk'Λ := ud_latA_le h hk'
  have hyk : (y : V) + k' ∈ Λ := Λ.add_mem y.2 hk'Λ
  rw [bC_add_left, ud_radical_of_mem h hk hyk, mul_one, ud_b_symm h x.2 hyk, bC_add_left,
    ud_radical_of_mem h hk' x.2, mul_one, ud_b_symm h y.2 x.2]

theorem ud_isQuadFn (h : UnitaryData H Λ α δ Ae) : IsQuadFn (phiQ H Λ α δ Ae) (bQ H Λ δ Ae) where
  add := by
    intro c d
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      induction d using QuotientAddGroup.induction_on with
      | H y =>
        rw [← QuotientAddGroup.mk_add, phiQ_mk h, phiQ_mk h, phiQ_mk h, bQ_mk h]
        exact ud_phi_add h x.2 y.2
  left := by
    intro c d e
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      induction d using QuotientAddGroup.induction_on with
      | H y =>
        induction e using QuotientAddGroup.induction_on with
        | H z =>
          rw [← QuotientAddGroup.mk_add, bQ_mk h, bQ_mk h, bQ_mk h]
          exact bC_add_left _ _ _
  sq := by
    intro k c
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      rw [← QuotientAddGroup.mk_nsmul, phiQ_mk h, phiQ_mk h]
      exact ud_phi_nsmul h x.2 k
  ne := by
    intro c
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      rw [phiQ_mk h]
      intro h0
      have := ud_norm h x.2
      rw [h0, norm_zero] at this
      exact zero_ne_one this
  nondeg := by
    intro c hc
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      refine ud_radical h x.2 fun x' hx' => ?_
      have := hc (QuotientAddGroup.mk (⟨x', hx'⟩ : Λ))
      rwa [bQ_mk h] at this

end Phi

theorem cayleyPhaseBasic : PhiBasic := by
  intro V _ _ H Λ α δ Ae h
  exact ⟨ud_skew h, ud_re h, fun x hx => ud_norm h hx, fun x hx y hy => ud_phi_wd h hx hy⟩

theorem UnitaryGauss_of (hG : GaussEighth) : UnitaryGauss := by
  intro V _ _ H Λ α δ Ae h S hS
  obtain ⟨hSΛ, hSinj, hSsurj⟩ := hS
  let f : S → Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ :=
    fun x => QuotientAddGroup.mk (⟨x.1, hSΛ x.1 x.2⟩ : Λ)
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply hSinj a.1 a.2 b.1 b.2
      have h1 : -(⟨a.1, hSΛ a.1 a.2⟩ : Λ) + ⟨b.1, hSΛ b.1 b.2⟩ ∈ (latA Λ δ Ae).addSubgroupOf Λ :=
        QuotientAddGroup.eq.mp hab
      have h2 := (latA Λ δ Ae).neg_mem (AddSubgroup.mem_addSubgroupOf.mp h1)
      have e : (a.1 : V) - b.1 = -(((-(⟨a.1, hSΛ a.1 a.2⟩ : Λ) + ⟨b.1, hSΛ b.1 b.2⟩ : Λ)) : V) := by
        push_cast
        abel
      rw [e]
      exact h2
    · intro q
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨x, hx, hyx⟩ := hSsurj y.1 y.2
      refine ⟨⟨x, hx⟩, ?_⟩
      apply QuotientAddGroup.eq.mpr
      apply AddSubgroup.mem_addSubgroupOf.mpr
      have e : ((-(⟨x, hSΛ x hx⟩ : Λ) + y : Λ) : V) = (y : V) - x := by
        push_cast
        abel
      have h3 : ((-(⟨x, hSΛ x hx⟩ : Λ) + y : Λ) : V) ∈ latA Λ δ Ae := by
        rw [e]
        exact hyx
      exact h3
  letI : Fintype (Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ) := Fintype.ofBijective f hf
  have hsum : ∑ x ∈ S, phiC H α Ae x = ∑ q : Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ, phiQ H Λ α δ Ae q := by
    rw [← Finset.sum_coe_sort S]
    exact Fintype.sum_bijective f hf _ _ (fun x => (phiQ_mk h (⟨x.1, hSΛ x.1 x.2⟩ : Λ)).symm)
  have hcard : Fintype.card (Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ) = S.card := by
    rw [← Fintype.card_coe S]
    exact (Fintype.card_of_bijective hf).symm
  have hq := hG (Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ) (phiQ H Λ α δ Ae) (bQ H Λ δ Ae) (ud_isQuadFn h)
  have hpos : (0 : ℝ) < S.card := by
    obtain ⟨x, hx, _⟩ := hSsurj 0 Λ.zero_mem
    exact_mod_cast Finset.card_pos.mpr ⟨x, hx⟩
  have hs : ((Real.sqrt S.card : ℝ) : ℂ) ^ 8 = (S.card : ℂ) ^ 4 := by
    rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, ← Complex.ofReal_pow, Real.sq_sqrt hpos.le]
    first | norm_num | (push_cast; ring) | simp
  unfold gaussC
  rw [mul_pow, hsum, hq, hcard, inv_pow, hs]
  have hne : (S.card : ℂ) ^ 4 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hpos.ne')
  exact inv_mul_cancel₀ hne

end Formalism.L2.Th1.H
