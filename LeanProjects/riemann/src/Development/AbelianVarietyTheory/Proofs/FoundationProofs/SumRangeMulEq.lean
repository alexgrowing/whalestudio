import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiamondMatrixConjMemGamma1InterGamma0Level
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitCommDiamondOperatorOfMatriStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem sum_range_mul_eq (h : ℕ → ℂ) (q r : ℕ) :
    ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range q, h (j + q * i) = ∑ m ∈ Finset.range (q * r), h m := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.add_comm]

theorem im_div_pos (τ : ℍ) (j q : ℕ) (hq : 0 < q) : 0 < (((τ : ℂ) + j) / q).im := by
  rw [Complex.div_natCast_im]
  simp only [Complex.add_im, Complex.natCast_im, add_zero]
  exact div_pos τ.im_pos (by exact_mod_cast hq)

theorem uOp_uOp_eq (f : ℍ → ℂ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (τ : ℍ) :
    uOp a (uOp b f) τ =
      ((a : ℂ) * b)⁻¹ * ∑ m ∈ Finset.range (a * b), f (ofComplex (((τ : ℂ) + m) / ((a : ℂ) * b))) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  simp only [uOp]
  rw [← sum_range_mul_eq (fun m : ℕ => f (ofComplex (((τ : ℂ) + m) / ((a : ℂ) * b)))) a b]
  conv_rhs => rw [Finset.sum_comm]
  rw [mul_inv, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofComplex_apply_of_im_pos (im_div_pos τ j a ha)]
  congr 2
  push_cast
  field_simp
  ring

theorem uOp_comm (f : ℍ → ℂ) (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    uOp q (uOp r f) = uOp r (uOp q f) := by
  funext τ
  rw [uOp_uOp_eq f q r hq hr, uOp_uOp_eq f r q hr hq, mul_comm (r : ℂ), Nat.mul_comm r q]

theorem sum_mul_mod (G : ℕ → ℂ) (q r : ℕ) (hq : 0 < q) (hc : Nat.Coprime q r) :
    ∑ j ∈ Finset.range q, G (r * j % q) = ∑ j ∈ Finset.range q, G j := by
  have hinj : Set.InjOn (fun j => r * j % q) (Finset.range q : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h1 : a ≡ b [MOD q] := Nat.ModEq.cancel_left_of_coprime hc hab
    unfold Nat.ModEq at h1
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
  have himg : (Finset.range q).image (fun j => r * j % q) = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨a, _, rfl⟩ := hx
      exact Nat.mod_lt _ hq
    · rw [Finset.card_image_of_injOn hinj]
  rw [← Finset.sum_image hinj, himg]

theorem per_ofComplex (g : ℍ → ℂ) (hper : ∀ τ : ℍ, g ((1 : ℝ) +ᵥ τ) = g τ) (z : ℂ) (hz : 0 < z.im) :
    g (ofComplex (z + 1)) = g (ofComplex z) := by
  have hz1 : 0 < (z + 1).im := by simpa using hz
  have h1 : ofComplex (z + 1) = (1 : ℝ) +ᵥ ofComplex z := by
    apply UpperHalfPlane.ext
    rw [coe_vadd, ofComplex_apply_of_im_pos hz1, ofComplex_apply_of_im_pos hz]
    push_cast
    ring
  rw [h1, hper]

theorem uOp_vOp (g : ℍ → ℂ) (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (hc : Nat.Coprime q r)
    (hper : ∀ τ : ℍ, g ((1 : ℝ) +ᵥ τ) = g τ) :
    uOp q (vOp r g) = vOp r (uOp q g) := by
  funext τ
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hw : 0 < ((r : ℂ) * τ).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hr) τ.im_pos
  simp only [uOp, vOp]
  rw [ofComplex_apply_of_im_pos hw]
  congr 1
  set w : ℂ := (r : ℂ) * τ with hwdef
  set G : ℕ → ℂ := fun m => g (ofComplex ((w + m) / q)) with hG
  have hGq : ∀ m n : ℕ, G (m + q * n) = G m := by
    intro m n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih]
      simp only [hG]
      have hpos : 0 < ((w + ((m + q * n : ℕ) : ℂ)) / q).im := by
        rw [Complex.div_natCast_im]
        simp only [Complex.add_im, Complex.natCast_im, add_zero]
        exact div_pos hw (by exact_mod_cast hq)
      rw [← per_ofComplex g hper _ hpos]
      congr 2
      push_cast
      field_simp
      ring
  have hmod : ∀ m, G m = G (m % q) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m q]
    exact hGq _ _
  calc ∑ j ∈ Finset.range q, g (ofComplex ((r : ℂ) * ↑(ofComplex (((τ : ℂ) + j) / q))))
      = ∑ j ∈ Finset.range q, G (r * j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hG]
        rw [ofComplex_apply_of_im_pos (im_div_pos τ j q hq)]
        congr 2
        rw [hwdef]
        push_cast
        field_simp
    _ = ∑ j ∈ Finset.range q, G (r * j % q) := Finset.sum_congr rfl fun j _ => hmod _
    _ = ∑ j ∈ Finset.range q, G j := sum_mul_mod G q r hq hc
    _ = _ := rfl

theorem uOp_add (q : ℕ) (f g : ℍ → ℂ) : uOp q (f + g) = uOp q f + uOp q g := by
  funext τ
  simp [uOp, Finset.sum_add_distrib, mul_add]

theorem uOp_smul (q : ℕ) (c : ℂ) (f : ℍ → ℂ) : uOp q (c • f) = c • uOp q f := by
  funext τ
  simp [uOp, Finset.mul_sum, mul_left_comm]

theorem T_mem_lev (N l : ℕ) : ModularGroup.T ∈ lev N l := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    simp [ModularGroup.T]
  · rw [Gamma0_mem]
    simp [ModularGroup.T]

theorem uOp_heckeT_comm : ∀ (N l q r : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → 0 < l → q.Prime → q ∣ N * l →
    r.Prime → ¬ r ∣ N * l → GlobalTheory.Hk.IsDia N l r σ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.uOp q (GlobalTheory.Hk.heckeT k r σ ⇑f) = GlobalTheory.Hk.heckeT k r σ (GlobalTheory.Hk.uOp q ⇑f) := by
  intro N l q r k σ hN hl hq hqd hr hrd hσ f
  have hq0 : 0 < q := hq.pos
  have hr0 : 0 < r := hr.pos
  have hne : q ≠ r := fun h => hrd (h ▸ hqd)
  have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).2 hne
  have hinv : ∀ γ ∈ lev N l, (⇑f) ∣[k] γ = ⇑f := fun γ hγ => by
    rw [SL_slash]; exact f.slash_action_eq' _ ⟨γ, hγ, rfl⟩
  have hper : ∀ τ : ℍ, ((⇑f) ∣[k] σ) ((1 : ℝ) +ᵥ τ) = ((⇑f) ∣[k] σ) τ := by
    intro τ
    have h1 : ((⇑f) ∣[k] σ) ∣[k] ModularGroup.T = (⇑f) ∣[k] σ := by
      have e : σ * ModularGroup.T = (σ * ModularGroup.T * σ⁻¹) * σ := by group
      rw [← SlashAction.slash_mul, e, SlashAction.slash_mul,
        hinv _ (isDia_conj_mem_lev N l r σ _ hσ (T_mem_lev N l))]
    have h2 := congr_fun h1 τ
    have hden : denom (ModularGroup.T : GL (Fin 2) ℝ) τ = 1 := by
      rw [denom]; simp [ModularGroup.coe_T]
    rw [SL_slash_apply, modular_T_smul] at h2
    simpa [hden] using h2
  have hd := GlobalTheory.T.heckeUOperatorExplicit_comm_diamondOperatorOfMatrix N l q k r σ hN hl hq hqd hσ f
  unfold GlobalTheory.Hk.dia at hd
  simp only [GlobalTheory.Hk.heckeT]
  rw [uOp_add, uOp_smul, uOp_comm _ q r hq0 hr0, uOp_vOp _ q r hq0 hr0 hcop hper, hd]

end GlobalTheory.Hk
