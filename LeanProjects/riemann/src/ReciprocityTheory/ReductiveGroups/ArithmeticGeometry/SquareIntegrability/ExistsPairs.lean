import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PerpSurj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContinuousRl

namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex Module

noncomputable section

namespace DimC

variable {ι : Type} [Fintype ι]

theorem Hf_inner (v w : EuclideanSpace ℂ ι) : Hf v w = inner ℂ w v := by
  simp only [Hf, PiLp.inner_apply, RCLike.inner_apply]
  all_goals (refine Finset.sum_congr rfl fun i _ => ?_; ring)

theorem Hf_add_l (v v' w : EuclideanSpace ℂ ι) : Hf (v + v') w = Hf v w + Hf v' w := by
  simp only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]

theorem Hf_add_r (v w w' : EuclideanSpace ℂ ι) : Hf v (w + w') = Hf v w + Hf v w' := by
  simp only [Hf, PiLp.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem Hf_smul_l (a : ℂ) (v w : EuclideanSpace ℂ ι) : Hf (a • v) w = a * Hf v w := by
  simp only [Hf, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem Hf_smul_r (a : ℂ) (v w : EuclideanSpace ℂ ι) : Hf v (a • w) = (starRingEnd ℂ) a * Hf v w := by
  simp only [Hf, PiLp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem Hf_swap (v w : EuclideanSpace ℂ ι) : Hf w v = (starRingEnd ℂ) (Hf v w) := by
  simp only [Hf, map_sum, map_mul, Complex.conj_conj]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem Hf_self (v : EuclideanSpace ℂ ι) : Hf v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [Hf_inner]
  first
    | exact_mod_cast inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v
    | (rw [inner_self_eq_norm_sq_to_K]; simp)
    | (rw [inner_self_eq_norm_sq_to_K]; norm_cast)

theorem Hf_self_im (v : EuclideanSpace ℂ ι) : (Hf v v).im = 0 := by
  rw [Hf_self, Complex.ofReal_im]

theorem Hf_sum_l {k : ℕ} (a : Fin k → ℂ) (v : Fin k → EuclideanSpace ℂ ι) (w : EuclideanSpace ℂ ι) :
    Hf (∑ i, a i • v i) w = ∑ i, a i * Hf (v i) w := by
  have h := map_sum (AddMonoidHom.mk' (fun x => Hf x w) (fun x x' => Hf_add_l x x' w))
    (fun i => a i • v i) Finset.univ
  simp only [AddMonoidHom.mk'_apply, Hf_smul_l] at h
  exact h

theorem Hf_sum_r {k : ℕ} (a : Fin k → ℂ) (v : EuclideanSpace ℂ ι) (w : Fin k → EuclideanSpace ℂ ι) :
    Hf v (∑ l, a l • w l) = ∑ l, (starRingEnd ℂ) (a l) * Hf v (w l) := by
  have h := map_sum (AddMonoidHom.mk' (fun x => Hf v x) (fun x x' => Hf_add_r v x x'))
    (fun i => a i • w i) Finset.univ
  simp only [AddMonoidHom.mk'_apply, Hf_smul_r] at h
  exact h

theorem Hf_zsmul_l (c : ℤ) (v w : EuclideanSpace ℂ ι) : (Hf (c • v) w).im = c * (Hf v w).im := by
  rw [← Int.cast_smul_eq_zsmul ℂ, Hf_smul_l]
  simp

theorem Hf_zsmul_r (c : ℤ) (v w : EuclideanSpace ℂ ι) : (Hf v (c • w)).im = c * (Hf v w).im := by
  rw [← Int.cast_smul_eq_zsmul ℂ, Hf_smul_r]
  simp

variable (Y : GT ι)

def nz (x y : EuclideanSpace ℂ ι) : ℤ := ⌊(Hf x y).im⌋

theorem nz_eq {x y : EuclideanSpace ℂ ι} (hx : x ∈ lat Y.b) (hy : y ∈ lat Y.b) :
    (nz x y : ℝ) = (Hf x y).im := by
  obtain ⟨k, hk⟩ := Y.integral x y hx hy
  rw [nz, hk, Int.floor_intCast]

def Bz : lat Y.b →ₗ[ℤ] lat Y.b →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun x y => nz (x : EuclideanSpace ℂ ι) y)
    (fun x x' y => by
      apply Int.cast_injective (α := ℝ)
      rw [Int.cast_add, nz_eq Y (x + x').2 y.2, nz_eq Y x.2 y.2, nz_eq Y x'.2 y.2, Submodule.coe_add,
        Hf_add_l, Complex.add_im])
    (fun c x y => by
      apply Int.cast_injective (α := ℝ)
      rw [smul_eq_mul, Int.cast_mul, nz_eq Y (c • x).2 y.2, nz_eq Y x.2 y.2, Submodule.coe_smul, Hf_zsmul_l])
    (fun x y y' => by
      apply Int.cast_injective (α := ℝ)
      rw [Int.cast_add, nz_eq Y x.2 (y + y').2, nz_eq Y x.2 y.2, nz_eq Y x.2 y'.2, Submodule.coe_add,
        Hf_add_r, Complex.add_im])
    (fun c x y => by
      apply Int.cast_injective (α := ℝ)
      rw [smul_eq_mul, Int.cast_mul, nz_eq Y x.2 (c • y).2, nz_eq Y x.2 y.2, Submodule.coe_smul, Hf_zsmul_r])

theorem Bz_apply (x y : lat Y.b) : ((Bz Y x y : ℤ) : ℝ) = (Hf (x : EuclideanSpace ℂ ι) y).im := by
  simp only [Bz, LinearMap.mk₂_apply]
  exact nz_eq Y x.2 y.2

theorem Bz_alt (x : lat Y.b) : Bz Y x x = 0 := by
  apply Int.cast_injective (α := ℝ)
  rw [Bz_apply, Int.cast_zero, Hf_self_im]

theorem Bz_surj (φ : lat Y.b →ₗ[ℤ] ℤ) : ∃ x, Bz Y x = φ := by
  obtain ⟨x, hx, h⟩ := Y.perfect φ.toAddMonoidHom
  refine ⟨⟨x, hx⟩, LinearMap.ext fun y => ?_⟩
  apply Int.cast_injective (α := ℝ)
  rw [Bz_apply]
  have h' := h y
  rw [LinearMap.toAddMonoidHom_coe] at h'
  exact h'.symm

theorem rank_lat : finrank ℤ (lat Y.b) = 2 * Fintype.card ι := by
  rw [Module.finrank_eq_card_basis (Y.b.restrictScalars ℤ), Fintype.card_fin]

theorem exists_pairs : ∃ e f : Fin (Fintype.card ι) → EuclideanSpace ℂ ι,
    (∀ i, e i ∈ lat Y.b) ∧ (∀ j, f j ∈ lat Y.b) ∧ (∀ i j, (Hf (e i) (e j)).im = 0) ∧
    (∀ i j, (Hf (e i) (f j)).im = if i = j then 1 else 0) := by
  obtain ⟨k, hk, e, f, hee, hef⟩ := DimA.sympl _ (lat Y.b) rfl (Bz Y) (Bz_alt Y) (Bz_surj Y)
  rw [rank_lat] at hk
  obtain rfl : k = Fintype.card ι := by omega
  refine ⟨fun i => e i, fun j => f j, fun i => (e i).2, fun j => (f j).2, fun i j => ?_, fun i j => ?_⟩
  · rw [← Bz_apply, hee]; simp
  · rw [← Bz_apply, hef]; split_ifs <;> simp

section Core

variable {Y} (e f : Fin (Fintype.card ι) → EuclideanSpace ℂ ι)
  (hee : ∀ i j, (Hf (e i) (e j)).im = 0)
  (hef : ∀ i j, (Hf (e i) (f j)).im = if i = j then 1 else 0)

include hee hef in
theorem e_li : LinearIndependent ℂ e := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hS : ∀ i l, (Hf (e i) (e l)).im = 0 := hee
  have h0 : ∀ y, ∑ i, c i * Hf (e i) y = 0 := by
    intro y
    rw [← Hf_sum_l, hc]
    simp [Hf]
  have hre : ∀ l, ∑ i, (c i).re * (Hf (e i) (e l)).re = 0 := by
    intro l
    have h := congrArg Complex.re (h0 (e l))
    simpa [Complex.re_sum, Complex.mul_re, hS] using h
  have him : ∀ l, ∑ i, (c i).im * (Hf (e i) (e l)).re = 0 := by
    intro l
    have h := congrArg Complex.im (h0 (e l))
    simpa [Complex.im_sum, Complex.mul_im, hS] using h
  have hzero : ∀ r : Fin (Fintype.card ι) → ℝ, (∀ l, ∑ i, r i * (Hf (e i) (e l)).re = 0) →
      ∑ i, ((r i : ℂ)) • e i = 0 := by
    intro r hr
    have hcol : ∀ l, ∑ i, (r i : ℂ) * Hf (e i) (e l) = 0 := by
      intro l
      apply Complex.ext
      · simpa [Complex.re_sum, hS] using hr l
      · simp [Complex.im_sum, hS]
    have hH : Hf (∑ i, ((r i : ℂ)) • e i) (∑ l, ((r l : ℂ)) • e l) = 0 := by
      rw [Hf_sum_l]
      simp only [Hf_sum_r, Complex.conj_ofReal, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun l _ => ?_
      calc ∑ i, (r i : ℂ) * ((r l : ℂ) * Hf (e i) (e l))
          = (r l : ℂ) * ∑ i, (r i : ℂ) * Hf (e i) (e l) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [hcol l, mul_zero]
    rw [Hf_self] at hH
    have h2 : ‖∑ i, ((r i : ℂ)) • e i‖ ^ 2 = 0 := by exact_mod_cast hH
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
  have hcoef : ∀ r : Fin (Fintype.card ι) → ℝ, ∑ i, ((r i : ℂ)) • e i = 0 → r j = 0 := by
    intro r hr0
    have h1 : (Hf (∑ i, ((r i : ℂ)) • e i) (f j)).im = r j := by
      rw [Hf_sum_l]
      simp [Complex.im_sum, hef]
    rw [hr0] at h1
    simpa [Hf] using h1.symm
  apply Complex.ext
  · simpa using hcoef (fun i => (c i).re) (hzero _ hre)
  · simpa using hcoef (fun i => (c i).im) (hzero _ him)

def eb : Module.Basis (Fin (Fintype.card ι)) ℂ (EuclideanSpace ℂ ι) :=
  Module.Basis.mk (e_li e f hee hef)
    ((e_li e f hee hef).span_eq_top_of_card_eq_finrank' (by simp)).ge

theorem eb_apply (i) : eb e f hee hef i = e i := by
  first
    | exact Module.Basis.mk_apply _ _ _
    | simp [eb]

end Core

section Gauge

variable {Y} (e f : Fin (Fintype.card ι) → EuclideanSpace ℂ ι)
  (hee : ∀ i j, (Hf (e i) (e j)).im = 0)
  (hef : ∀ i j, (Hf (e i) (f j)).im = if i = j then 1 else 0)

def Phi (z : Fin (Fintype.card ι) → ℂ) : EuclideanSpace ℂ ι := ∑ i, z i • e i

def tau (j : Fin (Fintype.card ι)) : Fin (Fintype.card ι) → ℂ := fun l => (eb e f hee hef).repr (f j) l

def S (i l : Fin (Fintype.card ι)) : ℂ := Hf (e i) (e l)

def Qf (z : Fin (Fintype.card ι) → ℂ) : ℂ := ∑ i, ∑ l, z i * z l * S e i l

theorem Phi_add (z w : Fin (Fintype.card ι) → ℂ) : Phi e (z + w) = Phi e z + Phi e w := by
  simp only [Phi, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem Phi_single (l : Fin (Fintype.card ι)) : Phi e (Pi.single l 1) = e l := by
  simp [Phi, Pi.single_apply]

theorem Phi_tau (j : Fin (Fintype.card ι)) : Phi e (tau e f hee hef j) = f j := by
  simp only [Phi, tau]
  conv_rhs => rw [← (eb e f hee hef).sum_repr (f j)]
  simp only [eb_apply]

include hee in
theorem S_symm (i l : Fin (Fintype.card ι)) : S e l i = S e i l := by
  simp only [S]
  rw [Hf_swap]
  exact Complex.conj_eq_iff_im.2 (hee i l)

include hee in
theorem Qf_add (z w : Fin (Fintype.card ι) → ℂ) :
    Qf e (z + w) = Qf e z + Qf e w + 2 * ∑ i, ∑ l, z i * w l * S e i l := by
  have h : ∑ i, ∑ l, w i * z l * S e i l = ∑ i, ∑ l, z i * w l * S e i l := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [S_symm e hee i l]
    ring
  have expand : ∀ i l, (z i + w i) * (z l + w l) * S e i l =
      z i * z l * S e i l + w i * w l * S e i l + z i * w l * S e i l + w i * z l * S e i l := by
    intro i l
    ring
  simp only [Qf, Pi.add_apply, expand, Finset.sum_add_distrib, h]
  ring

include hee hef in
theorem key (z : Fin (Fintype.card ι) → ℂ) (j : Fin (Fintype.card ι)) :
    Hf (Phi e z) (f j) = (∑ i, ∑ l, z i * tau e f hee hef j l * S e i l) + 2 * I * z j := by
  have hS : ∀ i l, (S e i l).im = 0 := fun i l => hee i l
  have hi : ∀ i, Hf (e i) (f j) =
      ∑ l, tau e f hee hef j l * S e i l + 2 * I * (if i = j then 1 else 0) := by
    intro i
    have h1 : Hf (e i) (f j) = ∑ l, (starRingEnd ℂ) (tau e f hee hef j l) * S e i l := by
      conv_lhs => rw [← Phi_tau e f hee hef j]
      simp only [Phi, Hf_sum_r]
      rfl
    have him := hef i j
    rw [h1] at him ⊢
    split_ifs at him ⊢ with hij
    · apply Complex.ext
      · simp [Complex.re_sum, hS]
      · simp [Complex.im_sum, hS] at him ⊢
        linarith
    · apply Complex.ext
      · simp [Complex.re_sum, hS]
      · simp [Complex.im_sum, hS] at him ⊢
        linarith
  simp only [Phi, Hf_sum_l, hi, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  · rw [Finset.sum_eq_single j]
    · simp
      ring
    · intro b _ hb
      simp [hb]
    · simp

end Gauge

section Final

variable (e f : Fin (Fintype.card ι) → EuclideanSpace ℂ ι)
  (hee : ∀ i j, (Hf (e i) (e j)).im = 0)
  (hef : ∀ i j, (Hf (e i) (f j)).im = if i = j then 1 else 0)

def Lk (l : Fin (Fintype.card ι)) : ℂ := Complex.log (Y.ka (e l))

def hF (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) (z : Fin (Fintype.card ι) → ℂ) : ℂ :=
  F (Phi e z) * cexp (-((q : ℂ) * Real.pi / 2) * Qf e z - ∑ l, Lk Y e l * z l)

include hee in
theorem hF_per (he : ∀ i, e i ∈ lat Y.b) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) (hFs : F ∈ Y.Sec q)
    (l : Fin (Fintype.card ι)) (z : Fin (Fintype.card ι) → ℂ) :
    hF Y e q F (z + Pi.single l 1) = hF Y e q F z := by
  have hmain : ∀ Fv a b c L : ℂ, L + a + b = c → cexp L * cexp a * Fv * cexp b = Fv * cexp c := by
    intro Fv a b c L h
    rw [← h, Complex.exp_add, Complex.exp_add]
    ring
  have hka : Y.ka (e l) = cexp (Lk Y e l) := by
    rw [Lk, Complex.exp_log]
    intro h0
    have h1 := Y.ka_abs (e l) (he l)
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hPhi : Phi e (z + Pi.single l 1) = Phi e z + e l := by
    rw [Phi_add, Phi_single]
  have hsec := hFs.2 (e l) (he l) (Phi e z)
  have hX : Hf (Phi e z) (e l) = ∑ i, z i * Hf (e i) (e l) := by
    simp only [Phi, Hf_sum_l]
  have hQs : Qf e (Pi.single l 1) = Hf (e l) (e l) := by
    simp [Qf, S, Pi.single_apply]
  have hsum2 : ∑ i, ∑ m, z i * (Pi.single l (1 : ℂ) : Fin (Fintype.card ι) → ℂ) m * S e i m =
      ∑ i, z i * Hf (e i) (e l) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [S, Pi.single_apply]
  have hQ : Qf e (z + Pi.single l 1) = Qf e z + Hf (e l) (e l) + 2 * ∑ i, z i * Hf (e i) (e l) := by
    rw [Qf_add e hee, hQs, hsum2]
  have hL : ∑ m, Lk Y e m * ((z + Pi.single l 1 : Fin (Fintype.card ι) → ℂ) m) = ∑ m, Lk Y e m * z m + Lk Y e l := by
    simp [mul_add, Finset.sum_add_distrib, Pi.single_apply]
  simp only [hF]
  rw [hPhi, hsec, hka]
  refine hmain _ _ _ _ _ ?_
  rw [hX, hQ, hL]
  ring

include hee hef in
theorem hF_qp (hf : ∀ j, f j ∈ lat Y.b) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) (hFs : F ∈ Y.Sec q)
    (j : Fin (Fintype.card ι)) (z : Fin (Fintype.card ι) → ℂ) :
    hF Y e q F (z + tau e f hee hef j) =
      (Y.ka (f j) * cexp ((q : ℂ) * Real.pi * Hf (f j) (f j) / 2 -
        (q : ℂ) * Real.pi / 2 * Qf e (tau e f hee hef j) - ∑ l, Lk Y e l * tau e f hee hef j l)) *
      cexp (2 * Real.pi * I * q * z j) * hF Y e q F z := by
  have hmain : ∀ κ Fv a b c d g : ℂ, a + b = c + d + g →
      κ * cexp a * Fv * cexp b = κ * cexp c * cexp d * (Fv * cexp g) := by
    intro κ Fv a b c d g h
    have hb : b = c + d + g - a := by linear_combination h
    rw [hb, Complex.exp_sub, Complex.exp_add, Complex.exp_add]
    field_simp [Complex.exp_ne_zero]
    all_goals ring
  have hPhi : Phi e (z + tau e f hee hef j) = Phi e z + f j := by
    rw [Phi_add, Phi_tau]
  have hsec := hFs.2 (f j) (hf j) (Phi e z)
  have hK := key e f hee hef z j
  have hQ := Qf_add e hee z (tau e f hee hef j)
  have hL : ∑ m, Lk Y e m * (z + tau e f hee hef j) m =
      ∑ m, Lk Y e m * z m + ∑ m, Lk Y e m * tau e f hee hef j m := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  simp only [hF]
  rw [hPhi, hsec]
  refine hmain _ _ _ _ _ _ _ ?_
  rw [hK, hQ, hL]
  ring

theorem hF_diff (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) (hd : Differentiable ℂ F) :
    Differentiable ℂ (hF Y e q F) := by
  have hPhi : Differentiable ℂ (Phi e) := by
    unfold Phi
    first
      | fun_prop
      | exact Differentiable.sum fun i _ => (differentiable_apply i).smul_const (e i)
  have hQ : Differentiable ℂ (Qf e) := by
    unfold Qf
    first
      | fun_prop
      | exact Differentiable.sum fun i _ => Differentiable.sum fun l _ =>
          ((differentiable_apply i).mul (differentiable_apply l)).mul_const _
  have hL : Differentiable ℂ (fun z : Fin (Fintype.card ι) → ℂ => ∑ l, Lk Y e l * z l) := by
    first
      | fun_prop
      | exact Differentiable.sum fun l _ => (differentiable_apply l).const_mul _
  unfold hF
  exact (hd.comp hPhi).mul (((differentiable_const _).mul hQ).sub hL).cexp

end Final

section Count

theorem av_int {k : ℕ} (Ψ : (Fin k → ℂ) → ℂ) (hc : Continuous Ψ) (w : Fin k → ℂ) :
    MeasureTheory.IntegrableOn (fun x => Ψ (DimB.rl x + w)) (DimB.ubox k) := by
  have hrl : Continuous fun x : Fin k → ℝ => DimB.rl x := by
    unfold DimB.rl
    fun_prop
  have hcont : Continuous fun x : Fin k → ℝ => Ψ (DimB.rl x + w) :=
    hc.comp (hrl.add continuous_const)
  refine (hcont.integrableOn_Icc (a := 0) (b := 1)).mono_set ?_
  intro x hx
  refine Set.mem_Icc.2 ⟨Pi.le_def.2 fun i => ?_, Pi.le_def.2 fun i => ?_⟩
  · have h := hx i
    simp only [Set.mem_Ioc, Pi.zero_apply, zero_add] at h
    exact h.1.le
  · have h := hx i
    simp only [Set.mem_Ioc, Pi.zero_apply, zero_add] at h
    exact h.2

theorem Av_add {k : ℕ} (Ψ Ψ' : (Fin k → ℂ) → ℂ) (hc : Continuous Ψ) (hc' : Continuous Ψ')
    (w : Fin k → ℂ) : DimB.Av (fun z => Ψ z + Ψ' z) w = DimB.Av Ψ w + DimB.Av Ψ' w := by
  simp only [DimB.Av]
  exact MeasureTheory.integral_add (av_int Ψ hc w) (av_int Ψ' hc' w)

theorem Av_smul {k : ℕ} (Ψ : (Fin k → ℂ) → ℂ) (c : ℂ) (w : Fin k → ℂ) :
    DimB.Av (fun z => c * Ψ z) w = c * DimB.Av Ψ w := by
  simp only [DimB.Av]
  first
    | exact MeasureTheory.integral_const_mul c _
    | exact MeasureTheory.integral_mul_left c _

variable (e f : Fin (Fintype.card ι) → EuclideanSpace ℂ ι)
  (hee : ∀ i j, (Hf (e i) (e j)).im = 0)
  (hef : ∀ i j, (Hf (e i) (f j)).im = if i = j then 1 else 0)

def T (q : ℕ) : Y.Sec q →ₗ[ℂ] ((Fin (Fintype.card ι) → Fin q) → ℂ) where
  toFun F := fun r => DimB.Av (DimB.Pm (hF Y e q F.1) (fun l => ((r l : ℕ) : ℤ))) 0
  map_add' F G := by
    funext r
    have h1 : DimB.Pm (hF Y e q (F + G).1) (fun l => ((r l : ℕ) : ℤ)) =
        fun z => DimB.Pm (hF Y e q F.1) (fun l => ((r l : ℕ) : ℤ)) z +
          DimB.Pm (hF Y e q G.1) (fun l => ((r l : ℕ) : ℤ)) z := by
      funext z; simp only [DimB.Pm, hF, Submodule.coe_add, Pi.add_apply]; ring
    rw [Pi.add_apply, h1, Av_add]
    · exact (DimB.Pm_diff _ (hF_diff Y e q F.1 F.2.1) _).continuous
    · exact (DimB.Pm_diff _ (hF_diff Y e q G.1 G.2.1) _).continuous
  map_smul' c F := by
    funext r
    have h1 : DimB.Pm (hF Y e q (c • F).1) (fun l => ((r l : ℕ) : ℤ)) =
        fun z => c * DimB.Pm (hF Y e q F.1) (fun l => ((r l : ℕ) : ℤ)) z := by
      funext z; simp only [DimB.Pm, hF, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring
    rw [Pi.smul_apply, h1, Av_smul, RingHom.id_apply, smul_eq_mul]

theorem T_apply (q : ℕ) (F : Y.Sec q) (r : Fin (Fintype.card ι) → Fin q) :
    T Y e q F r = DimB.Av (DimB.Pm (hF Y e q F.1) (fun l => ((r l : ℕ) : ℤ))) 0 := rfl

include hee hef in
theorem T_inj (he : ∀ i, e i ∈ lat Y.b) (hf : ∀ j, f j ∈ lat Y.b) (q : ℕ) (hq : 1 ≤ q) :
    Function.Injective (T Y e q) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro F hT
  have hall : ∀ m : Fin (Fintype.card ι) → ℤ, (∀ l, 0 ≤ m l ∧ m l < q) →
      DimB.Av (DimB.Pm (hF Y e q F.1) m) 0 = 0 := by
    intro m hm
    set r : Fin (Fintype.card ι) → Fin q := fun l => ⟨(m l).toNat, by have := hm l; omega⟩
    have hm' : (fun l => ((r l : ℕ) : ℤ)) = m := by
      funext l; simp only [r]; have := hm l; omega
    have := congrFun hT r
    rw [T_apply, hm', Pi.zero_apply] at this
    exact this
  have h0 := DimB.four_zero (by omega : 0 < q) (hF Y e q F.1) (hF_diff Y e q F.1 F.2.1)
    (hF_per Y e hee he q F.1 F.2) (tau e f hee hef) _ (hF_qp Y e f hee hef hf q F.1 F.2) hall
  apply Subtype.ext
  funext v
  have hv : v = Phi e (fun i => (eb e f hee hef).repr v i) := by
    rw [Phi]
    conv_lhs => rw [← (eb e f hee hef).sum_repr v]
    simp [eb_apply]
  have := congrFun h0 (fun i => (eb e f hee hef).repr v i)
  simp only [hF, Pi.zero_apply, mul_eq_zero, Complex.exp_ne_zero, or_false] at this
  rw [hv, this]; rfl

theorem dim_core (q : ℕ) (hq : 1 ≤ q) :
    FiniteDimensional ℂ (Y.Sec q) ∧ finrank ℂ (Y.Sec q) ≤ q ^ Fintype.card ι := by
  obtain ⟨e, f, he, hf, hee, hef⟩ := exists_pairs Y
  have hinj := T_inj Y e f hee hef he hf q hq
  haveI hfin : FiniteDimensional ℂ (Y.Sec q) := Module.Finite.of_injective (T Y e q) hinj
  refine ⟨hfin, ?_⟩
  calc finrank ℂ (Y.Sec q) ≤ finrank ℂ ((Fin (Fintype.card ι) → Fin q) → ℂ) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = q ^ Fintype.card ι := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

end Count

end DimC

end

end ReciprocityTheory.ChartRestriction.G.I2
