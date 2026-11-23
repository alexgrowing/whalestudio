import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

noncomputable section
namespace GlobalTheory.Hk.UDia

def gam (a b c d : ℤ) (j j' q : ℕ) (Y : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![a*d - b*q*c - a*j*c, a*b + b*j'*c + a*Y; c*d - c^2*j - c*d*q, a*d + c*d*j' + c*Y]

theorem det_gam (a b c d : ℤ) (j j' q : ℕ) (Y : ℤ) (hdet : a*d - b*c = 1)
    (hY : b = a*j + j*j'*c - j'*d - q*Y) : (gam a b c d j j' q Y).det = 1 := by
  rw [gam, Matrix.det_fin_two_of]
  subst hY
  linear_combination (a*d - (a*j + j*j'*c - j'*d - q*Y)*c + 1) * hdet

theorem alg (a b c d Y t w z j j' q : ℂ) (hq : q ≠ 0) (hdet : a*d - b*c = 1)
    (hY : b = a*j + j*j'*c - j'*d - q*Y) (hwq : w*q = t + j)
    (hzq : z*q*(c*t+d) = a*t + b + j'*(c*t+d)) :
    a*w + b = (c*t+d) * ((a*d - b*q*c - a*j*c) * z + (a*b + b*j'*c + a*Y)) ∧
    c*w + d = (c*t+d) * ((c*d - c^2*j - c*d*q) * z + (a*d + c*d*j' + c*Y)) := by
  subst hY
  constructor
  · apply mul_left_cancel₀ hq
    linear_combination a*hwq - (a*d - (a*j + j*j'*c - j'*d - q*Y)*q*c - a*j*c)*hzq
      - (a*(t+j) + (a*j + j*j'*c - j'*d - q*Y)*q)*hdet
  · apply mul_left_cancel₀ hq
    linear_combination c*hwq - (c*d - c^2*j - c*d*q)*hzq - (c*(t+j) + d*q)*hdet

theorem key {N l q : ℕ} {k : ℤ} (f : ModularForm (GlobalTheory.Hk.lev N l) k) (ρ : SL(2, ℤ))
    (hcN : ((ρ 1 0 : ℤ) : ZMod (N * l)) = 0) (hq : 0 < q) (j j' : ℕ) (Y : ℤ)
    (hY : ρ 0 1 = ρ 0 0 * j + j * j' * ρ 1 0 - j' * ρ 1 1 - q * Y) (τ : ℍ) :
    (⇑f ∣[k] ρ) (ofComplex (((τ : ℂ) + j) / q)) =
      f (ofComplex ((((ρ • τ : ℍ) : ℂ) + j') / q)) * denom ρ τ ^ (-k) := by
  have hdetZ : ρ 0 0 * ρ 1 1 - ρ 0 1 * ρ 1 0 = 1 := by
    have := ρ.det_coe; rwa [Matrix.det_fin_two] at this
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set γ : SL(2, ℤ) := ⟨gam (ρ 0 0) (ρ 0 1) (ρ 1 0) (ρ 1 1) j j' q Y,
    det_gam _ _ _ _ _ _ _ _ hdetZ hY⟩ with hγdef
  have hdiv : ((N * l : ℕ) : ℤ) ∣ ρ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcN
  have hN : ((ρ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (dvd_trans (by push_cast; exact dvd_mul_right _ _) hdiv)
  have hl : ((ρ 1 0 : ℤ) : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (dvd_trans (by push_cast; exact dvd_mul_left _ _) hdiv)
  have hγ : γ ∈ GlobalTheory.Hk.lev N l := by
    refine Subgroup.mem_inf.mpr ⟨(Gamma1_mem _ _).mpr ⟨?_, ?_, ?_⟩, Gamma0_mem.mpr ?_⟩
    · have e : γ 0 0 = 1 + ρ 1 0 * (ρ 0 1 - ρ 0 1 * q - ρ 0 0 * j) := by
        simp only [hγdef, gam]; simp; linear_combination hdetZ
      rw [e]; push_cast; rw [hN]; ring
    · have e : γ 1 1 = 1 + ρ 1 0 * (ρ 0 1 + ρ 1 1 * j' + Y) := by
        simp only [hγdef, gam]; simp; linear_combination hdetZ
      rw [e]; push_cast; rw [hN]; ring
    · have e : γ 1 0 = ρ 1 0 * (ρ 1 1 - ρ 1 0 * j - ρ 1 1 * q) := by
        simp only [hγdef, gam]; simp; ring
      rw [e]; push_cast; rw [hN]; ring
    · have e : γ 1 0 = ρ 1 0 * (ρ 1 1 - ρ 1 0 * j - ρ 1 1 * q) := by
        simp only [hγdef, gam]; simp; ring
      rw [e]; push_cast; rw [hl]; ring
  have hpos : ∀ x : ℍ, ∀ n : ℕ, 0 < (((x : ℂ) + n) / q).im := by
    intro x n
    have := x.im_pos
    rw [Complex.div_natCast_im]; simp; positivity
  set w : ℍ := ofComplex (((τ : ℂ) + j) / q) with hwdef
  set z : ℍ := ofComplex ((((ρ • τ : ℍ) : ℂ) + j') / q) with hzdef
  have hwc : (w : ℂ) = ((τ : ℂ) + j) / q := by rw [hwdef, ofComplex_apply_of_im_pos (hpos τ j)]
  have hzc : (z : ℂ) = (((ρ • τ : ℍ) : ℂ) + j') / q := by
    rw [hzdef, ofComplex_apply_of_im_pos (hpos (ρ • τ) j')]
  have hu : ((ρ 1 0 : ℤ) : ℂ) * τ + ((ρ 1 1 : ℤ) : ℂ) ≠ 0 := by
    have := denom_ne_zero ρ τ; rwa [ModularGroup.denom_apply] at this
  have hρτ : ((ρ • τ : ℍ) : ℂ) = (((ρ 0 0 : ℤ) : ℂ) * τ + ((ρ 0 1 : ℤ) : ℂ)) /
      (((ρ 1 0 : ℤ) : ℂ) * τ + ((ρ 1 1 : ℤ) : ℂ)) := by
    rw [coe_specialLinearGroup_apply]; simp
  have hwq : (w : ℂ) * q = τ + j := by rw [hwc]; field_simp
  have hzq : (z : ℂ) * q * (((ρ 1 0 : ℤ) : ℂ) * τ + ((ρ 1 1 : ℤ) : ℂ)) =
      ((ρ 0 0 : ℤ) : ℂ) * τ + ((ρ 0 1 : ℤ) : ℂ) + (j' : ℂ) * (((ρ 1 0 : ℤ) : ℂ) * τ + ((ρ 1 1 : ℤ) : ℂ)) := by
    rw [hzc, div_mul_cancel₀ _ hqC, hρτ, add_mul, div_mul_cancel₀ _ hu]
  have hdetC : ((ρ 0 0 : ℤ) : ℂ) * ((ρ 1 1 : ℤ) : ℂ) - ((ρ 0 1 : ℤ) : ℂ) * ((ρ 1 0 : ℤ) : ℂ) = 1 := by
    exact_mod_cast hdetZ
  have hYC : ((ρ 0 1 : ℤ) : ℂ) = ((ρ 0 0 : ℤ) : ℂ) * (j : ℂ) + (j : ℂ) * (j' : ℂ) * ((ρ 1 0 : ℤ) : ℂ)
      - (j' : ℂ) * ((ρ 1 1 : ℤ) : ℂ) - (q : ℂ) * (Y : ℂ) := by exact_mod_cast hY
  obtain ⟨hA, hB⟩ := alg _ _ _ _ (Y : ℂ) (τ : ℂ) (w : ℂ) (z : ℂ) (j : ℂ) (j' : ℂ) (q : ℂ) hqC hdetC hYC hwq hzq
  have hγ10 : ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    have := denom_ne_zero γ z; rwa [ModularGroup.denom_apply] at this
  have hsm : ρ • w = γ • z := by
    apply UpperHalfPlane.ext
    rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
    simp only [hγdef, gam, algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
    simp only [Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    push_cast
    rw [hA, hB, mul_div_mul_left _ _ hu]
  have hden : denom ρ w = denom ρ τ * denom γ z := by
    rw [ModularGroup.denom_apply, ModularGroup.denom_apply, ModularGroup.denom_apply, hB]
    simp only [hγdef, gam]
    simp
  rw [ModularForm.SL_slash_apply, hsm, SlashInvariantForm.slash_action_eqn_SL'' f hγ z, hden, mul_zpow]
  have h1 := denom_ne_zero ρ τ
  have h2 := denom_ne_zero γ z
  rw [zpow_neg, zpow_neg]
  field_simp

theorem cast_toNat_emod {q : ℕ} (hq : 0 < q) (x : ℤ) :
    (((x % (q : ℤ)).toNat : ℕ) : ZMod q) = (x : ZMod q) := by
  have h0 : 0 ≤ x % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq.ne')
  rw [show (((x % (q : ℤ)).toNat : ℕ) : ZMod q) = (((x % (q : ℤ)).toNat : ℤ) : ZMod q) by
    push_cast; rfl, Int.toNat_of_nonneg h0, ZMod.intCast_mod]

theorem toNat_emod_lt {q : ℕ} (hq : 0 < q) (x : ℤ) : (x % (q : ℤ)).toNat < q := by
  have h1 : x % (q : ℤ) < q := Int.emod_lt_of_pos _ (by exact_mod_cast hq)
  omega

theorem eq_of_cast_eq {q : ℕ} {i i' : ℕ} (hi : i < q) (hi' : i' < q)
    (h : (i : ZMod q) = (i' : ZMod q)) : i = i' := by
  haveI : NeZero q := ⟨by omega⟩
  rw [← ZMod.val_cast_of_lt hi, ← ZMod.val_cast_of_lt hi', h]

end GlobalTheory.Hk.UDia

open GlobalTheory.Hk.UDia in

theorem GlobalTheory.Hk.uOp_dia_comm : ∀ (N l q : ℕ) (k d : ℤ) (ρ : SL(2, ℤ)), 0 < N → 0 < l → q.Prime →
    q ∣ N * l → GlobalTheory.Hk.IsDia N l d ρ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.uOp q (GlobalTheory.Hk.dia k ρ ⇑f) = GlobalTheory.Hk.dia k ρ (GlobalTheory.Hk.uOp q ⇑f) := by
  intro N l q k d ρ _ _ hqp hqNl hρ f
  have hq : 0 < q := hqp.pos
  have hcN := hρ.1
  have hdetZ : ρ 0 0 * ρ 1 1 - ρ 0 1 * ρ 1 0 = 1 := by
    have := ρ.det_coe; rwa [Matrix.det_fin_two] at this
  have hdiv : ((N * l : ℕ) : ℤ) ∣ ρ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcN
  have hcq : ((ρ 1 0 : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (dvd_trans (by exact_mod_cast hqNl) hdiv)
  have had : ((ρ 0 0 : ℤ) : ZMod q) * ((ρ 1 1 : ℤ) : ZMod q) = 1 := by
    have h := congrArg (fun x : ℤ => (x : ZMod q)) hdetZ
    push_cast at h; rw [hcq] at h; linear_combination h
  set a : ℤ := ρ 0 0
  set b : ℤ := ρ 0 1
  set dd : ℤ := ρ 1 1
  let φ : ℕ → ℕ := fun i => ((a * (a * i - b)) % (q : ℤ)).toNat
  let ψ : ℕ → ℕ := fun i => ((dd * (dd * i + b)) % (q : ℤ)).toNat
  funext τ
  simp only [GlobalTheory.Hk.dia]
  rw [ModularForm.SL_slash_apply]
  simp only [GlobalTheory.Hk.uOp]
  rw [mul_assoc]
  congr 1
  rw [Finset.sum_mul]
  have hterm : ∀ i ∈ Finset.range q, (⇑f ∣[k] ρ) (ofComplex (((τ : ℂ) + i) / q)) =
      f (ofComplex ((((ρ • τ : ℍ) : ℂ) + (φ i : ℕ)) / q)) * denom ρ τ ^ (-k) := by
    intro i _
    have hX : ((q : ℕ) : ℤ) ∣ a * i + i * (φ i) * ρ 1 0 - (φ i) * dd - b := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      rw [cast_toNat_emod hq, hcq]
      push_cast
      linear_combination (-(((a : ℤ) : ZMod q) * i - b)) * had
    obtain ⟨Y, hY⟩ := hX
    exact key f ρ hcN hq i (φ i) Y (by linear_combination -hY) τ
  rw [Finset.sum_congr rfl hterm]
  refine Finset.sum_nbij' φ ψ ?_ ?_ ?_ ?_ ?_
  · intro i _; simpa using toNat_emod_lt hq _
  · intro i _; simpa using toNat_emod_lt hq _
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_range] at hi
    apply eq_of_cast_eq (toNat_emod_lt hq _) hi
    simp only [ψ, φ]
    rw [cast_toNat_emod hq]; push_cast; rw [cast_toNat_emod hq]; push_cast
    linear_combination ((((a : ℤ) : ZMod q) * dd + 1) * i - dd * b) * had
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_range] at hi
    apply eq_of_cast_eq (toNat_emod_lt hq _) hi
    simp only [ψ, φ]
    rw [cast_toNat_emod hq]; push_cast; rw [cast_toNat_emod hq]; push_cast
    linear_combination ((((a : ℤ) : ZMod q) * dd + 1) * i + a * b) * had
  · intro i _; rfl
