import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefDualFreeRankOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.SelPerp

variable {l : ℕ} [Fact l.Prime]

def tau (c : Coef l) : c.O →ₗ[ℤ_[l]] ℤ_[l] := Classical.choose (coef_dual_free_rank_one l c)

theorem tau_spec (c : Coef l) : ∀ f : c.O →ₗ[ℤ_[l]] ℤ_[l], ∃! a : c.O, ∀ x, f x = tau c (a * x) :=
  Classical.choose_spec (coef_dual_free_rank_one l c)

theorem norm_unit (c : Coef l) (u : c.Oˣ) : ‖((u : c.O) : Qbar l)‖ = 1 := by
  have h1 := CupCob.norm_le_one_of_mem c (u : c.O).2
  have h2 := CupCob.norm_le_one_of_mem c ((u⁻¹ : c.Oˣ) : c.O).2
  have h3 : ((u : c.O) : Qbar l) * (((u⁻¹ : c.Oˣ) : c.O) : Qbar l) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
  have h4 := congrArg norm h3
  rw [norm_mul, norm_one] at h4
  nlinarith [norm_nonneg ((u : c.O) : Qbar l), norm_nonneg (((u⁻¹ : c.Oˣ) : c.O) : Qbar l)]

theorem norm_l_lt_one : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((l : ℕ) : ℚ_[l]) := by simp
  rw [e, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem dvd_of_mem_Ik (c : Coef l) (n : ℕ) {x : c.O} (hx : x ∈ Ik c n) : ∃ y : c.O, x = (l : c.O) ^ n * y := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hl0 : (l : c.O) ≠ 0 := by
    intro h
    have : ((l : c.O) : Qbar l) = 0 := by rw [h]; rfl
    rw [SubringClass.coe_natCast] at this
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have nl : ‖((l : c.O) : Qbar l)‖ = ‖((ϖ : c.O) : Qbar l)‖ ^ e := by
    rw [hw, Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]
  have nx : ‖((x : c.O) : Qbar l)‖ = ‖((ϖ : c.O) : Qbar l)‖ ^ k := by
    rw [hu, Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]
  have hlt : ‖((l : c.O) : Qbar l)‖ < 1 := by rw [SubringClass.coe_natCast]; exact norm_l_lt_one
  have hϖ1 : ‖((ϖ : c.O) : Qbar l)‖ ≤ 1 := CupCob.norm_le_one_of_mem c ϖ.2
  have he : e ≠ 0 := by
    rintro rfl
    rw [nl, pow_zero] at hlt
    exact lt_irrefl _ hlt
  have hϖlt : ‖((ϖ : c.O) : Qbar l)‖ < 1 := by
    rcases hϖ1.lt_or_eq with h | h
    · exact h
    · rw [nl, h, one_pow] at hlt; exact absurd hlt (lt_irrefl _)
  have hϖ0 : 0 < ‖((ϖ : c.O) : Qbar l)‖ := by
    rw [norm_pos_iff]
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hle : e * n ≤ k := by
    have h := (mem_Ik.1 hx)
    have e2 : ‖((l : ℕ) : Qbar l) ^ n‖ = ‖((ϖ : c.O) : Qbar l)‖ ^ (e * n) := by
      rw [norm_pow, ← SubringClass.coe_natCast c.O, nl, pow_mul]
    rw [nx, e2] at h
    exact (pow_le_pow_iff_right_of_lt_one₀ hϖ0 hϖlt).1 h
  refine ⟨(u : c.O) * ϖ ^ (k - e * n) * ((w⁻¹ : c.Oˣ) : c.O) ^ n, ?_⟩
  rw [hu, hw]
  have hk : k = e * n + (k - e * n) := by omega
  conv_lhs => rw [hk]
  calc (u : c.O) * ϖ ^ (e * n + (k - e * n))
      = (u : c.O) * ϖ ^ (k - e * n) * (((w : c.O) * ((w⁻¹ : c.Oˣ) : c.O)) ^ n * ϖ ^ (e * n)) := by
        rw [Units.mul_inv, one_pow, one_mul, pow_add]; ring
    _ = _ := by ring

theorem tau_red_zero (c : Coef l) (n : ℕ) {x : c.O} (hx : x ∈ Ik c n) :
    PadicInt.toZModPow n (tau c x) = 0 := by
  obtain ⟨y, rfl⟩ := dvd_of_mem_Ik c n hx
  have e : (l : c.O) ^ n * y = ((l : ℤ_[l]) ^ n) • y := by
    rw [Algebra.smul_def, map_pow, map_natCast]
  rw [e, map_smul, smul_eq_mul, map_mul, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

def lft (c : Coef l) (n : ℕ) : Qn c n → c.O := Function.surjInv (red_surjective c n)

theorem red_lft (c : Coef l) (n : ℕ) (b : Qn c n) : red c n (lft c n b) = b :=
  Function.surjInv_eq (red_surjective c n) b

theorem tau_congr (c : Coef l) (n : ℕ) {x y : c.O} (h : red c n x = red c n y) :
    PadicInt.toZModPow n (tau c x) = PadicInt.toZModPow n (tau c y) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub]
  refine tau_red_zero c n ?_
  rw [← red_eq_zero_iff_mem, map_sub, h, sub_self]

def tbA (c : Coef l) (n : ℕ) : Qn c n →+ ZMod (l ^ n) where
  toFun b := PadicInt.toZModPow n (tau c (lft c n b))
  map_zero' := by
    rw [← map_zero (red c n), tau_congr c n (red_lft c n _), map_zero, map_zero]
  map_add' a b := by
    obtain ⟨x, rfl⟩ := red_surjective c n a
    obtain ⟨y, rfl⟩ := red_surjective c n b
    rw [← map_add, tau_congr c n (red_lft c n _), tau_congr c n (red_lft c n _),
      tau_congr c n (red_lft c n _), map_add, map_add]

theorem tbA_red (c : Coef l) (n : ℕ) (x : c.O) : tbA c n (red c n x) = PadicInt.toZModPow n (tau c x) :=
  tau_congr c n (red_lft c n _)

def pairA (c : Coef l) (n : ℕ) (y : Mn c n) : Mn c n →+ ZMod (l ^ n) where
  toFun x := tbA c n (x 0 * y 1 - x 1 * y 0)
  map_zero' := by simp
  map_add' a b := by
    rw [← map_add]; congr 1; simp only [Pi.add_apply]; ring

def Phi (c : Coef l) (n : ℕ) : Mn c n →ₗ[ZMod (l ^ n)] TDual (ZMod (l ^ n)) (Mn c n) :=
  (AddMonoidHom.mk' (fun y => TDual.mk ((pairA c n y).toZModLinearMap (l ^ n))) (fun a b => by
    ext x
    show tbA c n _ = tbA c n _ + tbA c n _
    rw [← map_add]; congr 1; simp only [Pi.add_apply]; ring)).toZModLinearMap (l ^ n)

theorem Phi_apply (c : Coef l) (n : ℕ) (y x : Mn c n) : Phi c n y x = tbA c n (x 0 * y 1 - x 1 * y 0) := rfl

theorem red_mulVec (c : Coef l) (n : ℕ) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (hM : ∀ i j, M i j ∈ c.O)
    (v : Fin 2 → Qbar l) (hv : ∀ i, v i ∈ c.O) (i : Fin 2) :
    red c n ⟨(M *ᵥ v) i, CupCob.mulVec_mem c M v hM hv i⟩ =
      ((Matrix.of fun i j => red c n ⟨M i j, hM i j⟩) *ᵥ fun j => red c n ⟨v j, hv j⟩) i := by
  have e : (⟨(M *ᵥ v) i, CupCob.mulVec_mem c M v hM hv i⟩ : c.O) =
      (⟨M i 0, hM i 0⟩ : c.O) * ⟨v 0, hv 0⟩ + (⟨M i 1, hM i 1⟩ : c.O) * ⟨v 1, hv 1⟩ := by
    apply Subtype.ext
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Subalgebra.coe_add, Subalgebra.coe_mul]
  rw [e, map_add, map_mul, map_mul]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply]

def lftV (c : Coef l) (n : ℕ) (y : Mn c n) : Fin 2 → Qbar l := fun i => (lft c n (y i) : Qbar l)

theorem lftV_mem (c : Coef l) (n : ℕ) (y : Mn c n) (i : Fin 2) : lftV c n y i ∈ c.O := (lft c n (y i)).2

theorem red_lftV (c : Coef l) (n : ℕ) (y : Mn c n) (i : Fin 2) : red c n ⟨lftV c n y i, lftV_mem c n y i⟩ = y i :=
  red_lft c n (y i)

theorem cg_of_red {c : Coef l} {n : ℕ} {a b : Qbar l} (ha : a ∈ c.O) (hb : b ∈ c.O)
    (h : red c n ⟨a, ha⟩ = red c n ⟨b, hb⟩) : Cg n a b := (red_eq_iff ⟨a, ha⟩ ⟨b, hb⟩).1 h

theorem red_of_cg {c : Coef l} {n : ℕ} {a b : Qbar l} (ha : a ∈ c.O) (hb : b ∈ c.O)
    (h : Cg n a b) : red c n ⟨a, ha⟩ = red c n ⟨b, hb⟩ := (red_eq_iff ⟨a, ha⟩ ⟨b, hb⟩).2 h

end GlobalTheory.Ord2.SelPerp
