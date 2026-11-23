import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThIndep
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
import Formalism.GL3MeanSquares.HookFormulaTorsion.SquareEqDiagOfQuadraticEven

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Classical

variable {D : D7} {N N' : ℕ}

theorem Hf_add_left (T : Tor D) (x x' y : VC D N N') :
    Hf D T (x + x') y = Hf D T x y + Hf D T x' y := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem Hf_herm (T : Tor D) (x y : VC D N N') :
    Hf D T y x = starRingEnd ℂ (Hf D T x y) := by
  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

def cf (T : Tor D) (x y : VC D N N') : ℂ :=
  Complex.exp (-((Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)))

theorem U_U (T : Tor D) (x y : VC D N N') (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (U D T y G) z = cf T x y * U D T (x + y) G z :=
  Formalism.HermitianLattices.WeilRepresentation.heisenberg_cocycle _ (Hf D T) (Hf_add_left T) (Hf_herm T) G x y z

theorem U_smul (T : Tor D) (x : VC D N N') (c : ℂ) (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (fun w => c * G w) z = c * U D T x G z := by
  simp only [U]; ring

theorem U_zero_fn (T : Tor D) (x : VC D N N') (z : VC D N N') :
    U D T x (fun _ => (0 : ℂ)) z = 0 := by
  simp only [U, zero_mul]

def SemiChar (T : Tor D) (La' : AddSubgroup (VC D N N')) : Prop :=
  ∀ x ∈ La', ∀ y ∈ La', al D T (x + y) = al D T x * al D T y * cf T x y

theorem fix_eq (T : Tor D) {La' : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T La') {y : VC D N N'} (hy : y ∈ La') :
    (fun w => al D T y * U D T y G w) = G :=
  funext (hG.2 y hy)

theorem two_step (T : Tor D) {La' : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T La') {y : VC D N N'} (hy : y ∈ La') (x z : VC D N N') :
    al D T x * U D T x G z = al D T x * al D T y * cf T x y * U D T (x + y) G z := by
  conv_lhs => rw [← fix_eq T hG hy]
  rw [U_smul, U_U]; ring

theorem semiChar_of_ne_zero (T : Tor D) {La' : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T La') (hne : ∃ z, G z ≠ 0) : SemiChar T La' := by
  intro x hx y hy
  obtain ⟨z0, hz0⟩ := hne
  have h1 := hG.2 x hx (z0 - (x + y))
  rw [two_step T hG hy] at h1
  have h2 := hG.2 (x + y) (La'.add_mem hx hy) (z0 - (x + y))
  have hU : U D T (x + y) G (z0 - (x + y)) ≠ 0 := by
    simp only [U, sub_add_cancel]
    exact mul_ne_zero hz0 (Complex.exp_ne_zero _)
  exact (mul_right_cancel₀ hU (h2.trans h1.symm))

theorem rep_shift (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} (hS : SemiChar T La₂)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T La₁) {x y : VC D N N'} (hx : x ∈ La₂)
    (hy₁ : y ∈ La₁) (hy₂ : y ∈ La₂) (z : VC D N N') :
    al D T (x + y) * U D T (x + y) G z = al D T x * U D T x G z := by
  rw [two_step T hG hy₁ x z, hS x hx y hy₂]

theorem term_indep (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} (hS : SemiChar T La₂)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T La₁) (a b : La₂)
    (hab : (a : La₂ ⧸ La₁.addSubgroupOf La₂) = (b : La₂ ⧸ La₁.addSubgroupOf La₂))
    (z : VC D N N') :
    al D T (b : VC D N N') * U D T (b : VC D N N') G z =
      al D T (a : VC D N N') * U D T (a : VC D N N') G z := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hab
  have hb : (b : VC D N N') = (a : VC D N N') + ((-a + b : La₂) : VC D N N') := by
    simp
  rw [hb]
  exact rep_shift T hS hG a.2 hab (-a + b).2 z

theorem term_out (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} (hS : SemiChar T La₂)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T La₁) (a : La₂) (z : VC D N N') :
    al D T ((Quotient.out (a : La₂ ⧸ La₁.addSubgroupOf La₂) : La₂) : VC D N N') *
        U D T ((Quotient.out (a : La₂ ⧸ La₁.addSubgroupOf La₂) : La₂) : VC D N N') G z =
      al D T (a : VC D N N') * U D T (a : VC D N N') G z :=
  term_indep T hS hG a _ (QuotientAddGroup.out_eq' _).symm z

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Classical

variable {D : D7} {N N' : ℕ}

theorem Hf_diff (T : Tor D) (x : VC D N N') :
    Differentiable ℂ (fun z : VC D N N' => Hf D T z x) := by
  unfold Hf
  fun_prop

theorem U_diff (T : Tor D) (x : VC D N N') {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (U D T x G) := by
  have h1 : Differentiable ℂ (fun z : VC D N N' => G (z + x)) :=
    hG.comp (differentiable_id.add_const x)
  exact h1.mul (((Hf_diff T x).const_mul (-(Real.pi : ℂ))).sub_const _).cexp

theorem U_sum (T : Tor D) {Q : Type*} [Fintype Q] (x : VC D N N') (F : Q → VC D N N' → ℂ)
    (z : VC D N N') : U D T x (fun w => ∑ q, F q w) z = ∑ q, U D T x (F q) z := by
  simp only [U, Finset.sum_mul]

theorem Iop_mem_ThSp (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} (hS : SemiChar T La₂)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T La₁) : Iop D T La₁ La₂ G ∈ ThSp D T La₂ := by
  by_cases hfin : Finite (La₂ ⧸ La₁.addSubgroupOf La₂)
  swap
  · have hinf : Infinite (La₂ ⧸ La₁.addSubgroupOf La₂) := not_finite_iff_infinite.mp hfin
    have h0 : (La₁.addSubgroupOf La₂).index = 0 :=
      AddSubgroup.index_eq_zero_iff_infinite.mpr hinf
    have hI : Iop D T La₁ La₂ G = fun _ => 0 := by
      funext z
      simp only [Iop, h0, Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero, inv_zero, zero_mul]
    rw [hI]
    exact ⟨differentiable_const 0, fun x _ z => by rw [U_zero_fn, mul_zero]⟩
  haveI := Fintype.ofFinite (La₂ ⧸ La₁.addSubgroupOf La₂)
  set c : ℂ := ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) with hc
  set f : La₂ ⧸ La₁.addSubgroupOf La₂ → VC D N N' → ℂ := fun q w =>
    al D T ((Quotient.out q : La₂) : VC D N N') * U D T ((Quotient.out q : La₂) : VC D N N') G w
    with hf
  have hI : Iop D T La₁ La₂ G = fun w => c * ∑ q, f q w := by
    funext w
    simp only [Iop, finsum_eq_sum_of_fintype]
    rfl
  rw [hI]
  refine ⟨?_, ?_⟩
  · apply Differentiable.const_mul
    exact Differentiable.fun_sum fun q _ => (U_diff T _ hG.1).const_mul _
  · intro x hx z
    rw [U_smul, U_sum]
    show al D T x * (c * ∑ q, U D T x (f q) z) = c * ∑ q, f q z
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    have key : ∀ q, al D T x * U D T x (f q) z =
        f ((⟨x, hx⟩ : La₂) + q) z := by
      intro q
      simp only [hf]
      rw [U_smul, U_U, term_indep T hS hG (⟨x, hx⟩ + Quotient.out q)]
      · rw [AddSubgroup.coe_add, hS x hx _ (Quotient.out q).2]
        ring
      · rw [QuotientAddGroup.out_eq', QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
    simp_rw [key]
    exact Fintype.sum_equiv (Equiv.addLeft ((⟨x, hx⟩ : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂)) _ _
      (fun q => rfl)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Classical

variable {D : D7} {N N' : ℕ}

theorem Iop_of_le (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} (hle : La₂ ≤ La₁)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T La₁) : Iop D T La₁ La₂ G = G := by
  have htop : La₁.addSubgroupOf La₂ = ⊤ := AddSubgroup.addSubgroupOf_eq_top.mpr hle
  have hidx : (La₁.addSubgroupOf La₂).index = 1 := AddSubgroup.index_eq_one.mpr htop
  have hsub : Subsingleton (La₂ ⧸ La₁.addSubgroupOf La₂) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientAddGroup.induction_on with | H a => ?_
    induction b using QuotientAddGroup.induction_on with | H b => ?_
    rw [QuotientAddGroup.eq, htop]
    exact AddSubgroup.mem_top _
  letI : Unique (La₂ ⧸ La₁.addSubgroupOf La₂) := { default := 0, uniq := fun a => Subsingleton.elim a 0 }
  funext z
  simp only [Iop, hidx, Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul]
  rw [finsum_unique]
  exact hG.2 _ (hle (Quotient.out (default : La₂ ⧸ La₁.addSubgroupOf La₂)).2) z

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Classical

variable {D : D7} {N N' : ℕ}

def HfInt (T : Tor D) (La' : AddSubgroup (VC D N N')) : Prop :=
  ∀ x ∈ La', ∀ y ∈ La', ∃ a b : ℤ, Even (a - b) ∧
    Hf D T x y = (((a : ℝ) / Real.sqrt D.host.d : ℝ) : ℂ) + (b : ℂ) * Complex.I

theorem sqrt_d_pos (D : D7) : 0 < Real.sqrt D.host.d :=
  Real.sqrt_pos.mpr (by exact_mod_cast D.host.hyp.2.1.pos)

theorem Hf_add_right (T : Tor D) (x y y' : VC D N N') :
    Hf D T x (y + y') = Hf D T x y + Hf D T x y' := by
  rw [Hf_herm T (y + y') x, Hf_add_left, map_add, ← Hf_herm, ← Hf_herm]

theorem Hf_self_im (T : Tor D) (x : VC D N N') : (Hf D T x x).im = 0 := by
  have h := congrArg Complex.im (Hf_herm T x x)
  rw [Complex.conj_im] at h
  linarith

theorem Hf_re_swap (T : Tor D) (x y : VC D N N') : (Hf D T y x).re = (Hf D T x y).re := by
  rw [Hf_herm T x y, Complex.conj_re]

theorem self_int (T : Tor D) {La' : AddSubgroup (VC D N N')} (hI : HfInt T La')
    {x : VC D N N'} (hx : x ∈ La') :
    ∃ m : ℤ, (Hf D T x x).re = 2 * m / Real.sqrt D.host.d ∧
      round (Real.sqrt D.host.d / 2 * (Hf D T x x).re) = m := by
  obtain ⟨a, b, hab, h⟩ := hI x hx x hx
  have hs := sqrt_d_pos D
  have hb : (b : ℝ) = 0 := by
    have := Hf_self_im T x
    rw [h] at this
    simpa using this
  have hb' : b = 0 := by exact_mod_cast hb
  rw [hb', sub_zero] at hab
  obtain ⟨m, hm⟩ := hab
  have hre : (Hf D T x x).re = 2 * m / Real.sqrt D.host.d := by
    rw [h, hm]; simp [hb']; ring
  refine ⟨m, hre, ?_⟩
  rw [hre]
  have : Real.sqrt D.host.d / 2 * (2 * (m : ℝ) / Real.sqrt D.host.d) = m := by
    field_simp
  rw [this, round_intCast]

theorem neg_one_zpow_congr {n m : ℤ} (h : Even (n - m)) : (-1 : ℂ) ^ n = (-1 : ℂ) ^ m := by
  have : n = m + (n - m) := by ring
  rw [this, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), h.neg_one_zpow, mul_one]

theorem cf_int (T : Tor D) (x y : VC D N N') (b : ℤ) (hb : (Hf D T x y).im = b) :
    cf T x y = (-1 : ℂ) ^ (-b) := by
  rw [cf, hb, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem semiChar_of_HfInt (T : Tor D) {La' : AddSubgroup (VC D N N')} (hI : HfInt T La') :
    SemiChar T La' := by
  intro x hx y hy
  have hs := sqrt_d_pos D
  obtain ⟨mx, hxre, hxr⟩ := self_int T hI hx
  obtain ⟨my, hyre, hyr⟩ := self_int T hI hy
  obtain ⟨ms, hsre, hsr⟩ := self_int T hI (La'.add_mem hx hy)
  obtain ⟨a, b, hab, h⟩ := hI x hx y hy
  have hre : (Hf D T x y).re = a / Real.sqrt D.host.d := by rw [h]; simp
  have him : (Hf D T x y).im = b := by rw [h]; simp
  have hexp : (Hf D T (x + y) (x + y)).re =
      (Hf D T x x).re + (Hf D T y y).re + 2 * (Hf D T x y).re := by
    rw [Hf_add_left, Hf_add_right, Hf_add_right, Complex.add_re, Complex.add_re, Complex.add_re,
      Hf_re_swap T x y]
    ring
  have hms : ms = mx + my + a := by
    rw [hsre, hxre, hyre, hre] at hexp
    have h2 : (2 * (ms : ℝ)) = 2 * mx + 2 * my + 2 * a := by
      field_simp at hexp; linarith
    exact_mod_cast (by linarith : (ms : ℝ) = mx + my + a)
  simp only [al]
  rw [hsr, hxr, hyr, cf_int T x y b him, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  apply neg_one_zpow_congr
  rw [hms]
  have : mx + my + a - (mx + my + -b) = (a - b) + 2 * b := by ring
  rw [this]
  exact hab.add (even_two_mul b)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Classical

theorem finite_quot_of_smul {V : Type*} [AddCommGroup V] (La₁ La₂ R : AddSubgroup V)
    [Module.Finite ℤ R] (hle : La₂ ≤ R) (k : ℤ) (hk : k ≠ 0) (hkR : ∀ z ∈ R, k • z ∈ La₁) :
    Finite (La₂ ⧸ La₁.addSubgroupOf La₂) := by
  have hinj : Function.Injective (AddSubgroup.inclusion hle).toIntLinearMap :=
    AddSubgroup.inclusion_injective hle
  haveI : Module.Finite ℤ La₂ := Module.Finite.of_injective _ hinj
  haveI : Module.Finite ℤ (La₂ ⧸ La₁.addSubgroupOf La₂) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' (La₁.addSubgroupOf La₂)).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  apply Module.finite_of_fg_torsion
  intro q
  induction q using QuotientAddGroup.induction_on with | H a => ?_
  refine ⟨⟨k, mem_nonZeroDivisors_of_ne_zero hk⟩, ?_⟩
  change k • (a : La₂ ⧸ La₁.addSubgroupOf La₂) = 0
  rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.coe_zsmul]
  exact hkR _ (hle a.2)

variable {D : D7}

theorem Phi_smul_eq {N N' : ℕ} (δ : ℂ) (M : ℤ) (hM : M ≠ 0) (n : ℕ)
    (A : Fin N' → Fin N → 𝓞 D.host.E) :
    ((n : ℤ) * M) • FL.Phi D (N := N) (N' := N') (δ / M) A =
      ∑ i0 : Fin N', ∑ j0 : Fin N,
        FL.ins D i0 j0 (fun τ => δ * n * embT D τ ((A i0 j0 : 𝓞 D.host.E) : D.host.E)) := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  funext τ i j
  simp only [Finset.sum_apply, Pi.smul_apply, FL.Phi, FL.ins, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp only [and_self, if_true, zsmul_eq_mul]
    push_cast
    field_simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ j) h
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro c _
    simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem La_index_finite (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ) {N N' : ℕ}
    (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (h₁ : admitted D N N' L₁ L₁') (h₂ : admitted D N N' L₂ L₂') :
    Finite (La D (tor0 D cc δ) L₂ L₂' ⧸
      (La D (tor0 D cc δ) L₁ L₁').addSubgroupOf (La D (tor0 D cc δ) L₂ L₂')) := by
  obtain ⟨M, hM, hup⟩ := FL.La_upper D L₂ L₂' h₂ cc δ
  obtain ⟨n, hn, hlow⟩ := FL.La_lower D L₁ L₁' h₁ cc hcc δ
  haveI : Module.Finite ℤ (FL.Phi D (N := N) (N' := N') (δ / M)).range :=
    Module.Finite.of_surjective (FL.Phi D (N := N) (N' := N') (δ / M)).rangeRestrict.toIntLinearMap
      (AddMonoidHom.rangeRestrict_surjective _)
  refine finite_quot_of_smul _ _ _ hup ((n : ℤ) * M)
    (mul_ne_zero (by exact_mod_cast hn) hM) ?_
  rintro z ⟨A, rfl⟩
  rw [Phi_smul_eq δ M hM n A]
  exact AddSubgroup.sum_mem _ fun i0 _ => AddSubgroup.sum_mem _ fun j0 _ => hlow i0 j0 (A i0 j0)

theorem La_index_ne_zero (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ) {N N' : ℕ}
    (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (h₁ : admitted D N N' L₁ L₁') (h₂ : admitted D N N' L₂ L₂') :
    ((La D (tor0 D cc δ) L₁ L₁').addSubgroupOf (La D (tor0 D cc δ) L₂ L₂')).index ≠ 0 := by
  haveI := La_index_finite cc hcc δ L₁ L₂ L₁' L₂' h₁ h₂
  exact AddSubgroup.index_ne_zero_of_finite

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

end
