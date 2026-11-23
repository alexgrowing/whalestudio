import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd

noncomputable section
open scoped MatrixGroups
namespace GlobalTheory.ThAdd
open GlobalTheory.KZ GlobalTheory.Glue

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem theta_mul (s : ℚ) (x y : HahnSeries ℚ Ω) :
    theta s (x * y) = theta s x * y + x * theta s y := by
  ext a
  have hx : (theta s x).support ⊆ x.support := fun r hr h => hr (by simp [theta, h])
  have hy : (theta s y).support ⊆ y.support := fun r hr h => hr (by simp [theta, h])
  rw [HahnSeries.coeff_add, HahnSeries.coeff_mul_left' x.isPWO_support hx,
    HahnSeries.coeff_mul_right' y.isPWO_support hy]
  show algebraMap ℚ Ω (s * a) * (x * y).coeff a = _
  rw [HahnSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ij hij => ?_)
  rw [Finset.mem_addAntidiagonal] at hij
  obtain ⟨-, -, h⟩ := hij
  show algebraMap ℚ Ω (s * a) * (x.coeff ij.1 * y.coeff ij.2) =
    algebraMap ℚ Ω (s * ij.1) * x.coeff ij.1 * y.coeff ij.2 + x.coeff ij.1 * (algebraMap ℚ Ω (s * ij.2) * y.coeff ij.2)
  rw [← h, mul_add, map_add]; ring

def Ig (A : ValuationSubring Ω) (φ : HahnSeries ℚ Ω) : Prop := ∀ r, φ.coeff r ∈ A

def Dv (A : ValuationSubring Ω) (l n : ℕ) (φ : HahnSeries ℚ Ω) : Prop := ∀ r, ∃ z ∈ A, φ.coeff r = (l : Ω) ^ n * z

theorem Ig.mul {A : ValuationSubring Ω} {x y : HahnSeries ℚ Ω} (hx : Ig A x) (hy : Ig A y) : Ig A (x * y) := by
  intro r; rw [HahnSeries.coeff_mul]
  exact sum_mem (fun ij _ => mul_mem (hx _) (hy _))

theorem Dv.add {A : ValuationSubring Ω} {l n : ℕ} {x y : HahnSeries ℚ Ω} (hx : Dv A l n x) (hy : Dv A l n y) :
    Dv A l n (x + y) := by
  intro r; obtain ⟨z, hz, e⟩ := hx r; obtain ⟨z', hz', e'⟩ := hy r
  exact ⟨z + z', add_mem hz hz', by rw [HahnSeries.coeff_add, e, e', mul_add]⟩

theorem Dv.mul {A : ValuationSubring Ω} {l n : ℕ} {x y : HahnSeries ℚ Ω} (hx : Dv A l n x) (hy : Ig A y) :
    Dv A l n (x * y) := by
  intro r; rw [HahnSeries.coeff_mul]
  choose z hz e using hx
  refine ⟨∑ ij ∈ Finset.addAntidiagonal x.isPWO_support y.isPWO_support r, z ij.1 * y.coeff ij.2,
    sum_mem (fun ij _ => mul_mem (hz _) (hy _)), ?_⟩
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun ij _ => ?_); rw [e]; ring

theorem dv_iff {A : ValuationSubring Ω} {l n : ℕ} {x y : HahnSeries ℚ Ω} :
    (∀ r, CgA A l n (x.coeff r) (y.coeff r)) ↔ Dv A l n (x - y) := by
  simp [CgA, Dv]

end GlobalTheory.ThAdd

namespace GlobalTheory.ThAdd
open GlobalTheory.KZ GlobalTheory.Glue
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem unit_iff (A : ValuationSubring Ω) (x : Ω) (hx : x ∈ A) : (x ≠ 0 ∧ x⁻¹ ∈ A) ↔ A.valuation x = 1 := by
  constructor
  · rintro ⟨h0, hi⟩
    have h1 := (A.valuation_le_one_iff x).2 hx
    have h2 := (A.valuation_le_one_iff _).2 hi
    rw [map_inv₀] at h2
    have hv : A.valuation x ≠ 0 := by simpa using h0
    have : 1 ≤ A.valuation x := by
      by_contra hc; push_neg at hc
      have := one_lt_inv₀ (zero_lt_iff.2 hv) |>.2 hc
      exact absurd h2 (not_le.2 this)
    exact le_antisymm h1 this
  · intro h
    have h0 : x ≠ 0 := by rintro rfl; simp at h
    refine ⟨h0, (A.valuation_le_one_iff _).1 ?_⟩
    rw [map_inv₀, h, inv_one]

theorem prim_iff (A : ValuationSubring Ω) (φ : HahnSeries ℚ Ω) :
    Prim A φ ↔ (∀ r, A.valuation (φ.coeff r) ≤ 1) ∧ ∃ r, A.valuation (φ.coeff r) = 1 := by
  constructor
  · rintro ⟨h1, r, h2⟩
    exact ⟨fun r => (A.valuation_le_one_iff _).2 (h1 r), r, (unit_iff A _ (h1 r)).1 h2⟩
  · rintro ⟨h1, r, h2⟩
    have h1' : ∀ r, φ.coeff r ∈ A := fun r => (A.valuation_le_one_iff _).1 (h1 r)
    exact ⟨h1', r, (unit_iff A _ (h1' r)).2 h2⟩

theorem prim_mul {A : ValuationSubring Ω} {x y : HahnSeries ℚ Ω} (hx : Prim A x) (hy : Prim A y) : Prim A (x * y) := by
  rw [prim_iff] at hx hy ⊢
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  set v := A.valuation
  have sx : {r | v (x.coeff r) = 1} ⊆ x.support := fun r hr h => by simp [Set.mem_setOf_eq, h] at hr
  have sy : {r | v (y.coeff r) = 1} ⊆ y.support := fun r hr h => by simp [Set.mem_setOf_eq, h] at hr
  have wx := x.isPWO_support.isWF.mono sx
  have wy := y.isPWO_support.isWF.mono sy
  have nx : {r | v (x.coeff r) = 1}.Nonempty := hx2
  have ny : {r | v (y.coeff r) = 1}.Nonempty := hy2
  set r0 := wx.min nx
  set s0 := wy.min ny
  have hr0 : v (x.coeff r0) = 1 := wx.min_mem nx
  have hs0 : v (y.coeff s0) = 1 := wy.min_mem ny
  have ltx : ∀ r, r < r0 → v (x.coeff r) < 1 := fun r hr =>
    lt_of_le_of_ne (hx1 r) (fun h => wx.not_lt_min nx h hr)
  have lty : ∀ r, r < s0 → v (y.coeff r) < 1 := fun r hr =>
    lt_of_le_of_ne (hy1 r) (fun h => wy.not_lt_min ny h hr)
  have int : ∀ r, v ((x * y).coeff r) ≤ 1 := by
    intro r; rw [HahnSeries.coeff_mul]
    exact v.map_sum_le (fun ij _ => by rw [map_mul]; exact mul_le_one' (hx1 _) (hy1 _))
  refine ⟨int, r0 + s0, ?_⟩
  rw [HahnSeries.coeff_mul, ← Finset.add_sum_erase _ _ ((Finset.mem_addAntidiagonal (x := (r0, s0))).2 ⟨sx (show r0 ∈ {r | v (x.coeff r) = 1} from hr0), sy (show s0 ∈ {r | v (y.coeff r) = 1} from hs0), rfl⟩)]
  have hmain : v (x.coeff r0 * y.coeff s0) = 1 := by rw [map_mul, hr0, hs0, one_mul]
  rw [Valuation.map_add_eq_of_lt_left, hmain]
  rw [hmain]
  refine v.map_sum_lt one_ne_zero (fun ij hij => ?_)
  rw [Finset.mem_erase] at hij
  obtain ⟨hne, hij⟩ := hij
  obtain ⟨-, -, hsum⟩ := Finset.mem_addAntidiagonal.1 hij
  rw [map_mul]
  rcases lt_trichotomy ij.1 r0 with h | h | h
  · exact lt_of_le_of_lt (mul_le_of_le_one_right' (hy1 _)) (ltx _ h)
  · exfalso; apply hne; ext
    · exact h
    · simp only; rw [h] at hsum; exact add_left_cancel hsum
  · have : ij.2 < s0 := by
      by_contra hc; push_neg at hc
      have := add_lt_add_of_lt_of_le h hc
      rw [hsum] at this; exact lt_irrefl _ this
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hx1 _)) (lty _ this)

end GlobalTheory.ThAdd

namespace GlobalTheory.ThAdd
open GlobalTheory.KZ GlobalTheory.Glue
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem isDl_mul {X : Tower Ω ε} {A : ValuationSubring Ω} {l n : ℕ} {s : ℚ} {f f' : X.K} {φ φ' : HahnSeries ℚ Ω}
    (h : IsDl X A l n s f φ) (h' : IsDl X A l n s f' φ') : IsDl X A l n s (f * f') (φ + φ') := by
  obtain ⟨hφ, a, b, κ, hκ, e, pa, pb, c⟩ := h
  obtain ⟨hφ', a', b', κ', hκ', e', pa', pb', c'⟩ := h'
  refine ⟨fun r => by rw [HahnSeries.coeff_add]; exact add_mem (hφ r) (hφ' r),
    a * a', b * b', κ * κ', mul_ne_zero hκ hκ', ?_, ?_, ?_, ?_⟩
  · calc f * f' * (b * b') = (f * b) * (f' * b') := by ring
      _ = _ := by rw [e, e', map_mul]; ring
  · rw [map_mul]; exact prim_mul pa pa'
  · rw [map_mul]; exact prim_mul pb pb'
  · rw [dv_iff] at c c' ⊢
    rw [map_mul, map_mul, theta_mul, theta_mul]
    have key : (φ + φ') * (X.exp a * X.exp a') * (X.exp b * X.exp b') -
        ((theta s (X.exp a) * X.exp a' + X.exp a * theta s (X.exp a')) * (X.exp b * X.exp b') -
          X.exp a * X.exp a' * (theta s (X.exp b) * X.exp b' + X.exp b * theta s (X.exp b'))) =
        (φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) * (X.exp a' * X.exp b') +
        (φ' * X.exp a' * X.exp b' - (theta s (X.exp a') * X.exp b' - X.exp a' * theta s (X.exp b'))) * (X.exp a * X.exp b) := by
      ring
    rw [key]
    exact (c.mul (Ig.mul pa'.1 pb'.1)).add (c'.mul (Ig.mul pa.1 pb.1))

theorem isDl_one (X : Tower Ω ε) (A : ValuationSubring Ω) (l n : ℕ) (s : ℚ) : IsDl X A l n s 1 0 := by
  refine ⟨fun r => by simp, 1, 1, 1, one_ne_zero, by simp, ?_, ?_, ?_⟩
  · rw [map_one]; exact ⟨fun r => by rw [HahnSeries.coeff_one]; split_ifs <;> simp, 0, by simp⟩
  · rw [map_one]; exact ⟨fun r => by rw [HahnSeries.coeff_one]; split_ifs <;> simp, 0, by simp⟩
  · intro r
    refine ⟨0, zero_mem A, ?_⟩
    have : theta s (1 : HahnSeries ℚ Ω) = theta s 1 * 1 + 1 * theta s 1 := by
      rw [← theta_mul, mul_one]
    have h0 : theta s (1 : HahnSeries ℚ Ω) = 0 := by
      have : theta s (1 : HahnSeries ℚ Ω) + theta s 1 = theta s 1 + 0 := by
        rw [add_zero]; nth_rewrite 3 [this]; simp
      exact add_left_cancel this
    simp [h0]

theorem isDl_pow {X : Tower Ω ε} {A : ValuationSubring Ω} {l n : ℕ} {s : ℚ} {f : X.K} {φ : HahnSeries ℚ Ω}
    (h : IsDl X A l n s f φ) (k : ℕ) : IsDl X A l n s (f ^ k) ((k : Ω) • φ) := by
  induction k with
  | zero => simpa using isDl_one X A l n s
  | succ k ih =>
    rw [pow_succ, Nat.cast_succ, add_smul, one_smul]
    exact isDl_mul ih h

end GlobalTheory.ThAdd

namespace GlobalTheory.ThAdd
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem inv_mul {X : Tower Ω ε} {H : Subgroup SL(2, ℤ)} {f g : X.K} (hf : Inv X H f) (hg : Inv X H g) :
    Inv X H (f * g) := fun γ hγ => by rw [map_mul, hf γ hγ, hg γ hγ]

theorem inv_pow {X : Tower Ω ε} {H : Subgroup SL(2, ℤ)} {f : X.K} (hf : Inv X H f) (k : ℕ) :
    Inv X H (f ^ k) := fun γ hγ => by rw [map_pow, hf γ hγ]

theorem cls_comb (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (c c' : ℤ_[l]) (f f' : X.Kˣ) :
    c • X.cls l n f + c' • X.cls l n f' = X.cls l n (f ^ (c.appr n) * f' ^ (c'.appr n)) := by
  have red : ∀ (d : ℤ_[l]) (q : X.Kl l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Kl l)))),
      d • q = ((d.appr n : ℕ) : ℤ_[l]) • q := by
    intro d q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← sub_smul]
    apply Submodule.smul_mem_smul _ Submodule.mem_top
    rw [Ideal.span_singleton_pow]
    exact PadicInt.appr_spec n d
  rw [red c, red c']
  simp only [Tower.cls, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1
  rw [ofMul_mul, ofMul_pow, ofMul_pow, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
    Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem isThB_add : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w : ℕ) (b b' : X.Fn l), (l : Ω) ∈ A.nonunits → b ∈ X.B N l w → b' ∈ X.B N l w →
    ∀ (c c' : ℤ_[l]) (φ φ' : HahnSeries ℚ Ω),
  IsThB X A N l n b φ → IsThB X A N l n b' φ' →
    IsThB X A N l n (c • b + c' • b') (((c.appr n : ℕ) : Ω) • φ + ((c'.appr n : ℕ) : Ω) • φ') := by
  intro Ω _ _ _ ε X A N l _ n w b b' _ _ _ c c' φ φ' h h'
  obtain ⟨f, hfi, hfc, hfd, hfl⟩ := h
  obtain ⟨f', hfi', hfc', hfd', hfl'⟩ := h'
  refine ⟨f ^ (c.appr n) * f' ^ (c'.appr n), ?_, ?_, ?_, ?_⟩
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    exact inv_mul (inv_pow hfi _) (inv_pow hfi' _)
  · rw [← cls_comb, ← hfc, ← hfc', ← map_smul, ← map_smul, ← map_add]
    rfl
  · intro δ hδ hδ'
    obtain ⟨g, hgi, hg⟩ := hfd δ hδ hδ'
    obtain ⟨g', hgi', hg'⟩ := hfd' δ hδ hδ'
    refine ⟨g ^ (c.appr n) * g' ^ (c'.appr n), inv_mul (inv_pow hgi _) (inv_pow hgi' _), ?_⟩
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
    calc (f : X.K) ^ (c.appr n) * (f' : X.K) ^ (c'.appr n) *
          (X.sl (ofSL δ) f ^ (c.appr n) * X.sl (ofSL δ) f' ^ (c'.appr n))
        = ((f : X.K) * X.sl (ofSL δ) f) ^ (c.appr n) * ((f' : X.K) * X.sl (ofSL δ) f') ^ (c'.appr n) := by ring
      _ = _ := by rw [hg, hg']; ring
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    exact isDl_mul (isDl_pow hfl _) (isDl_pow hfl' _)

end GlobalTheory.ThAdd
