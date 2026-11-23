import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

noncomputable section

open CongruenceSubgroup UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm Manifold Real

namespace UpperTheory.V.Af

def heckeOne (k p : ℕ) (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  (p : ℂ) ^ (k - 1) * f (ofComplex (p * (z : ℂ))) +
    (p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (ofComplex (((z : ℂ) + b) / p))

private theorem im_mul_pos {p : ℕ} (hp : 0 < p) {z : ℂ} (hz : 0 < z.im) : 0 < ((p : ℂ) * z).im := by
  have : (0 : ℝ) < p := by exact_mod_cast hp
  simpa using mul_pos this hz

private theorem im_div_pos {p : ℕ} (hp : 0 < p) {z : ℂ} (hz : 0 < z.im) (b : ℕ) : 0 < ((z + b) / (p : ℂ)).im := by
  have : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Complex.div_natCast_im]
  simpa using div_pos hz this

theorem heckeOne_mdiff (k : ℕ) {p : ℕ} (hp : 0 < p) {f : ℍ → ℂ} (hf : MDiff f) : MDiff (heckeOne k p f) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have h : DifferentiableOn ℂ (fun z : ℂ => (p : ℂ) ^ (k - 1) * (f ∘ ofComplex) (p * z) +
      (p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, (f ∘ ofComplex) ((z + b) / p)) {z : ℂ | 0 < z.im} := by
    refine DifferentiableOn.add (DifferentiableOn.const_mul ?_ _) (DifferentiableOn.const_mul ?_ _)
    · exact hf.comp (f := fun z : ℂ => (p : ℂ) * z) (by fun_prop) fun z hz => im_mul_pos hp hz
    · refine DifferentiableOn.fun_sum fun b _ => ?_
      exact hf.comp (f := fun z : ℂ => (z + b) / (p : ℂ)) (by fun_prop) fun z hz => im_div_pos hp hz b
  refine h.congr fun z hz => ?_
  simp only [Function.comp, heckeOne, ofComplex_apply_of_im_pos hz]

private theorem sum_range_qParam_add_div_pow_eq_ite_dvd (p : ℕ) (hp : 0 < p) (τ : ℂ) (m : ℕ) :
    ∑ b ∈ Finset.range p, Function.Periodic.qParam 1 ((τ + b) / p) ^ m =
      (p : ℂ) * (if p ∣ m then Function.Periodic.qParam 1 τ ^ (m / p) else 0) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hprim : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / p)) p :=
    Complex.isPrimitiveRoot_exp p hp.ne'
  have hterm : ∀ b : ℕ, Function.Periodic.qParam 1 ((τ + b) / p) ^ m =
      Complex.exp (2 * π * Complex.I * τ / p) ^ m *
        (Complex.exp (2 * π * Complex.I / p) ^ m) ^ b := by
    intro b
    rw [← pow_mul, mul_comm m b, pow_mul, ← mul_pow]
    congr 1
    rw [← Complex.exp_nat_mul, ← Complex.exp_add, Function.Periodic.qParam]
    congr 1
    push_cast
    field_simp
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    have h1 : Complex.exp (2 * π * Complex.I / p) ^ (p * j) = 1 := by
      rw [pow_mul, hprim.pow_eq_one, one_pow]
    rw [h1, Nat.mul_div_cancel_left j hp]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [mul_comm, pow_mul, ← Complex.exp_nat_mul, Function.Periodic.qParam]
    congr 2
    push_cast
    field_simp
  · have hne : Complex.exp (2 * π * Complex.I / p) ^ m ≠ 1 :=
      fun h' => h ((hprim.pow_eq_one_iff_dvd m).mp h')
    have h1 : (Complex.exp (2 * π * Complex.I / p) ^ m) ^ p = 1 := by
      rw [← pow_mul, mul_comm m p, pow_mul, hprim.pow_eq_one, one_pow]
    rw [geom_sum_eq hne, h1, sub_self, zero_div, mul_zero, mul_zero]

theorem hasSum_heckeOne (k : ℕ) {p : ℕ} (hp : 0 < p) {f : ℍ → ℂ} {a : ℕ → ℂ}
    (hf : ∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) (τ : ℍ) :
    HasSum (fun n => (a (p * n) + (p : ℂ) ^ (k - 1) * (if p ∣ n then a (n / p) else 0)) •
      Function.Periodic.qParam 1 τ ^ n) (heckeOne k p f τ) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpos : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hinj : Function.Injective (fun m : ℕ => p * m) :=
    fun x y hxy => Nat.eq_of_mul_eq_mul_left hp hxy
  have hB : HasSum (fun n => (p : ℂ) ^ (k - 1) * ((if p ∣ n then a (n / p) else 0) •
      Function.Periodic.qParam 1 (τ : ℂ) ^ n))
      ((p : ℂ) ^ (k - 1) * f (ofComplex ((p : ℂ) * (τ : ℂ)))) := by
    refine HasSum.mul_left _ ?_
    have him : 0 < ((p : ℂ) * τ).im := by simpa [Complex.mul_im] using mul_pos hpos τ.im_pos
    have h := hf (ofComplex ((p : ℂ) * (τ : ℂ)))
    rw [ofComplex_apply_of_im_pos him] at h ⊢
    refine (hinj.hasSum_iff ?_).mp ?_
    · intro x hx
      rw [if_neg, zero_smul]
      rintro ⟨j, rfl⟩
      exact hx ⟨j, rfl⟩
    · have e : ((fun n => (if p ∣ n then a (n / p) else 0) •
          Function.Periodic.qParam 1 (τ : ℂ) ^ n) ∘ fun m : ℕ => p * m) =
          fun m => a m • Function.Periodic.qParam 1 ((⟨(p : ℂ) * τ, him⟩ : ℍ) : ℂ) ^ m := by
        funext m
        simp only [Function.comp_apply]
        rw [if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m hp, pow_mul]
        congr 2
        simp only [UpperHalfPlane.coe_mk, Function.Periodic.qParam, ← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [e]
      exact h
  have hA : HasSum (fun n => a (p * n) • Function.Periodic.qParam 1 (τ : ℂ) ^ n)
      ((p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (ofComplex (((τ : ℂ) + b) / p))) := by
    have him : ∀ b : ℕ, 0 < (((τ : ℂ) + b) / p).im := fun b => by
      rw [Complex.div_natCast_im]
      simpa using div_pos τ.im_pos hpos
    have hs : HasSum (fun m => (p : ℂ)⁻¹ * ∑ b ∈ Finset.range p,
        a m • Function.Periodic.qParam 1 (((τ : ℂ) + b) / p) ^ m)
        ((p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (ofComplex (((τ : ℂ) + b) / p))) := by
      refine HasSum.mul_left _ (hasSum_sum fun b _ => ?_)
      have h := hf (ofComplex (((τ : ℂ) + b) / p))
      rw [ofComplex_apply_of_im_pos (him b)] at h ⊢
      simpa only [UpperHalfPlane.coe_mk] using h
    have heq : ∀ m, (p : ℂ)⁻¹ * ∑ b ∈ Finset.range p,
        a m • Function.Periodic.qParam 1 (((τ : ℂ) + b) / p) ^ m =
        a m • (if p ∣ m then Function.Periodic.qParam 1 (τ : ℂ) ^ (m / p) else 0) := by
      intro m
      simp only [smul_eq_mul]
      rw [← Finset.mul_sum, sum_range_qParam_add_div_pow_eq_ite_dvd p hp (τ : ℂ) m, mul_left_comm,
        inv_mul_cancel_left₀ hp0]
    simp only [heq] at hs
    have hz : ∀ x, x ∉ Set.range (fun m : ℕ => p * m) →
        a x • (if p ∣ x then Function.Periodic.qParam 1 (τ : ℂ) ^ (x / p) else 0) = 0 := by
      intro x hx
      rw [if_neg, smul_zero]
      rintro ⟨j, rfl⟩
      exact hx ⟨j, rfl⟩
    convert (hinj.hasSum_iff hz).mpr hs using 1
    funext n
    simp only [Function.comp_apply, if_pos (dvd_mul_right p n), Nat.mul_div_cancel_left n hp]
  convert hA.add hB using 1
  · funext n
    simp only [smul_eq_mul]
    ring
  · simp only [heckeOne]
    ring

private theorem apply_moeb {k : ℕ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[(k : ℤ)] γ = f) (a b c d : ℤ)
    (h : a * d - b * c = 1) {w w' : ℂ} (hw : 0 < w.im) (e : w' = (a * w + b) / (c * w + d)) :
    f (ofComplex w') = (c * w + d) ^ k * f (ofComplex w) := by
  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩
  have h1 := (slash_action_eq'_iff k f γ ⟨w, hw⟩).1 (by rw [hf γ])
  have h2 : ofComplex w' = γ • (⟨w, hw⟩ : ℍ) := by
    rw [← ofComplex_apply (γ • (⟨w, hw⟩ : ℍ)), specialLinearGroup_apply, e]
    simp [γ]
  rw [h2, h1, ofComplex_apply_of_im_pos hw]
  simp [γ]

theorem heckeOne_slash_S {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) {f : ℍ → ℂ}
    (hf : ∀ γ : SL(2, ℤ), f ∣[(k : ℤ)] γ = f) : heckeOne k p f ∣[(k : ℤ)] ModularGroup.S = heckeOne k p f := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  funext z
  have hz0 : (z : ℂ) ≠ 0 := z.ne_zero
  rw [slash_action_eq'_iff, modular_S_smul]
  let i : ℕ → ℕ := fun b => (-(b : ZMod p)⁻¹).val
  have hne : ∀ b ∈ (Finset.range p).erase 0, (b : ZMod p) ≠ 0 := fun b hb h => by
    rw [Finset.mem_erase, Finset.mem_range] at hb
    exact hb.1 (Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff b p).1 h) hb.2)
  have hi : ∀ b ∈ (Finset.range p).erase 0, i b ∈ (Finset.range p).erase 0 := fun b hb => by
    rw [Finset.mem_erase, Finset.mem_range]
    exact ⟨by simpa [i] using hne b hb, ZMod.val_lt _⟩
  have hii : ∀ b ∈ (Finset.range p).erase 0, i (i b) = b := fun b hb => by
    rw [Finset.mem_erase, Finset.mem_range] at hb
    simp [i, ZMod.val_natCast_of_lt hb.2]
  have hdvd : ∀ b ∈ (Finset.range p).erase 0, (p : ℤ) ∣ (b : ℤ) * (i b : ℤ) + 1 := fun b hb => by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [i, mul_inv_cancel₀ (hne b hb)]
  have e1 : f (ofComplex (p * (-(z : ℂ))⁻¹)) = ((z : ℂ) / p) ^ k * f (ofComplex (((z : ℂ) + (0 : ℕ)) / p)) := by
    rw [apply_moeb hf 0 (-1) 1 0 (by norm_num) (im_div_pos hp.pos z.2 0) (by simp; field_simp)]
    simp
  have e2 : f (ofComplex (((-(z : ℂ))⁻¹ + (0 : ℕ)) / p)) = (p * (z : ℂ)) ^ k * f (ofComplex (p * (z : ℂ))) := by
    rw [apply_moeb hf 0 (-1) 1 0 (by norm_num) (im_mul_pos hp.pos z.2) (by push_cast; field_simp; ring)]
    simp
  have e3 : ∀ b ∈ (Finset.range p).erase 0, f (ofComplex (((-(z : ℂ))⁻¹ + b) / p)) =
      (z : ℂ) ^ k * f (ofComplex (((z : ℂ) + i b) / p)) := fun b hb => by
    obtain ⟨c, hc⟩ := hdvd b hb
    have hc' : (b : ℂ) * (i b : ℂ) + 1 = p * c := by exact_mod_cast hc
    have hd : ((p : ℤ) : ℂ) * (((z : ℂ) + i b) / p) + ((-(i b : ℤ) : ℤ) : ℂ) = z := by push_cast; field_simp; ring
    rw [apply_moeb hf b (-c) p (-(i b : ℤ)) (by linear_combination -hc) (im_div_pos hp.pos z.2 (i b))
      (by rw [hd]; push_cast; field_simp; linear_combination -hc'), hd]
  have h0 : 0 ∈ Finset.range p := Finset.mem_range.2 hp.pos
  simp only [heckeOne]
  rw [← Finset.add_sum_erase _ _ h0, ← Finset.add_sum_erase _ _ h0, e1, e2, Finset.sum_congr rfl e3,
    ← Finset.mul_sum, Finset.sum_nbij' i i hi hi hii hii (g := fun b : ℕ => f (ofComplex (((z : ℂ) + b) / p)))
      fun _ _ => rfl]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [ModularGroup.S, Nat.add_sub_cancel, zpow_natCast]
  simp [div_pow, mul_pow]
  field_simp
  ring

theorem discriminant_eig {p : ℕ} (hp : p.Prime) (n : ℕ) :
    coef ModularForm.discriminant (p * n) +
        (p : ℂ) ^ (12 - 1) * (if p ∣ n then coef ModularForm.discriminant (n / p) else 0) =
      coef ModularForm.discriminant p * coef ModularForm.discriminant n := by
  have hs : ∀ γ : SL(2, ℤ), ModularForm.discriminant ∣[((12 : ℕ) : ℤ)] γ = ModularForm.discriminant :=
    SlashInvariantForm.slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant
  have hsum : ∀ τ : ℍ, HasSum (fun m => coef ModularForm.discriminant m • Function.Periodic.qParam 1 τ ^ m)
      (ModularForm.discriminant τ) := fun τ =>
    hasSum_qExpansion one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL)
      CuspForm.discriminant.holo' (ModularFormClass.bdd_at_infty CuspForm.discriminant) τ
  have hT := hasSum_heckeOne 12 hp.pos hsum
  have hinv : ∀ γ : SL(2, ℤ), heckeOne 12 p ModularForm.discriminant ∣[(12 : ℤ)] γ =
      heckeOne 12 p ModularForm.discriminant := by
    refine SlashInvariantForm.slash_action_generators_SL2Z (heckeOne_slash_S (k := 12) (by norm_num) hp hs) ?_
    funext z
    rw [slash_action_eq'_iff, modular_T_smul]
    have e : Function.Periodic.qParam 1 (((1 : ℝ) +ᵥ z : ℍ) : ℂ) = Function.Periodic.qParam 1 z := by
      simp [Function.Periodic.qParam, mul_add, Complex.exp_add]
    have h1 := hT ((1 : ℝ) +ᵥ z)
    rw [e] at h1
    simp [h1.unique (hT z), ModularGroup.T]
  let g : ModularForm 𝒮ℒ 12 :=
    { toFun := heckeOne 12 p ModularForm.discriminant
      slash_action_eq' := fun A hA => by
        obtain ⟨A, rfl⟩ := hA
        exact hinv A
      holo' := heckeOne_mdiff 12 hp.pos CuspForm.discriminant.holo'
      bdd_at_cusps' := fun {c} hc => by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [hinv γ]
        exact isBoundedAtImInfty_of_hasSum_qExpansion one_pos hT }
  have hq := ModularFormClass.qExpansion_coeff_unique (f := g) one_pos one_mem_strictPeriods_SL hT
  have h0 : coef ModularForm.discriminant 0 = 0 :=
    CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos one_mem_strictPeriods_SL
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve
    (toCuspForm g (by rw [← hq 0]; simp [h0]))
  have hc' : (g : ℍ → ℂ) = c • (CuspForm.discriminant : ℍ → ℂ) := (congrArg DFunLike.coe hc).symm
  rw [hc', ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c CuspForm.discriminant] at hq
  have h1 := hq 1
  have hp1 : ¬ p ∣ 1 := hp.not_dvd_one
  simp only [hp1, if_false, mul_one, mul_zero, add_zero, PowerSeries.coeff_smul, CuspForm.coe_discriminant,
    discriminant_qExpansion_coeff_one, smul_eq_mul] at h1
  rw [hq n, h1]
  rfl

def deltaNewform : Newform 12 where
  M := 1
  pos := one_pos
  f := CuspForm.discriminant.copy ModularForm.discriminant rfl (by
    have : Gamma1 1 = ⊤ := by
      ext A
      simp only [Gamma1_mem, Subgroup.mem_top, iff_true]
      exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    rw [this, MonoidHom.range_eq_map])
  χ := 1
  char := fun γ _ => by
    rw [MulChar.one_apply (isUnit_of_subsingleton _), one_smul]
    exact SlashInvariantForm.slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant γ
  one := discriminant_qExpansion_coeff_one
  eig := fun p hp _ n _ => by
    rw [MulChar.one_apply (isUnit_of_subsingleton _), one_mul]
    exact discriminant_eig hp n
  new := fun M' h1 h2 => absurd (Nat.dvd_one.1 h1) h2

instance : Nonempty (Newform 12) := ⟨deltaNewform⟩

end UpperTheory.V.Af
