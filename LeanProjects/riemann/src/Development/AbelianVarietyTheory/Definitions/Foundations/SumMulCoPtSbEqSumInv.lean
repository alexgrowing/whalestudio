import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CoPtMu

noncomputable section

namespace GlobalTheory.LambdaValuationPowers

variable {K : Type*} [Field K] [CharZero K]

def coPtSb (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d a b : ℤ) (s : ℕ) : K :=
  (c : K) ^ 2 * (d : K) ^ 2 * GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ a b s
    - (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) ^ 2 * GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ (c * a) b s
    - (c : K) ^ 2 * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ a (d * b) s
    + (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) *
        GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ (c * a) (d * b) s

theorem coPtSb_one (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d x : ℤ) (s : ℕ) :
    coPtSb N p m k ψ c d x 1 s = GlobalTheory.KummerEisensteinGalois.coPtS N p m k ψ c d x s := by
  simp [coPtSb, GlobalTheory.KummerEisensteinGalois.coPtS]

def chiAvg (N p m k : ℕ) [NeZero N] (ψ : DirichletCharacter K (p ^ m)) (χ : ℕ → K) (c d x : ℤ) (s : ℕ) : K :=
  ∑ δ : (ZMod N)ˣ, (χ (δ : ZMod N).val)⁻¹ * coPtSb N p m k ψ c d (x * ((δ : ZMod N).val : ℤ)) ((δ : ZMod N).val : ℤ) s

omit [CharZero K] in

theorem ffMu_congr (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) {a a' : ℤ} (h : a ≡ a' [ZMOD N]) :
    GlobalTheory.KummerEisensteinGalois.ffMu N p m k ψ a = GlobalTheory.KummerEisensteinGalois.ffMu N p m k ψ a' := by
  funext s
  have h' : ∀ z : ℤ, z ≡ a [ZMOD N] ↔ z ≡ a' [ZMOD N] := fun z => ⟨fun hz => hz.trans h, fun hz => hz.trans h.symm⟩
  simp only [GlobalTheory.KummerEisensteinGalois.ffMu, h']

omit [CharZero K] in

theorem eeMu_congr (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) {b b' : ℤ} (h : b ≡ b' [ZMOD N]) :
    GlobalTheory.KummerEisensteinGalois.eeMu N p m ψ b = GlobalTheory.KummerEisensteinGalois.eeMu N p m ψ b' := by
  funext s
  have h' : ∀ z : ℤ, z ≡ b [ZMOD N] ↔ z ≡ b' [ZMOD N] := fun z => ⟨fun hz => hz.trans h, fun hz => hz.trans h.symm⟩
  simp only [GlobalTheory.KummerEisensteinGalois.eeMu, h']

omit [CharZero K] in

theorem coPtMu_congr (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) {a a' b b' : ℤ} (ha : a ≡ a' [ZMOD N])
    (hb : b ≡ b' [ZMOD N]) : GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ a b = GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ a' b' := by
  simp only [GlobalTheory.KummerEisensteinGalois.coPtMu, ffMu_congr N p m k ψ ha, eeMu_congr N p m ψ hb]

omit [CharZero K] in

theorem coPtSb_congr (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) {a a' b b' : ℤ} (ha : a ≡ a' [ZMOD N])
    (hb : b ≡ b' [ZMOD N]) : coPtSb N p m k ψ c d a b = coPtSb N p m k ψ c d a' b' := by
  funext s
  simp only [coPtSb, coPtMu_congr N p m k ψ ha hb, coPtMu_congr N p m k ψ (ha.mul_left c) hb,
    coPtMu_congr N p m k ψ ha (hb.mul_left d), coPtMu_congr N p m k ψ (ha.mul_left c) (hb.mul_left d)]

omit [CharZero K] in

theorem sum_mul_coPtSb_eq_sum_inv (N p m k : ℕ) [NeZero N] (ψ : DirichletCharacter K (p ^ m)) (χ : DirichletCharacter K N)
    (c d x : ℤ) (s : ℕ) :
    ∑ δ : (ZMod N)ˣ, χ (δ : ZMod N) * coPtSb N p m k ψ c d (x * ((δ : ZMod N).val : ℤ)) ((δ : ZMod N).val : ℤ) s =
      ∑ δ : (ZMod N)ˣ, χ⁻¹ (δ : ZMod N) *
        coPtSb N p m k ψ c d (x * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ)) (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) s := by
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun δ => ?_
  have : χ⁻¹ ((δ⁻¹ : (ZMod N)ˣ) : ZMod N) = χ (δ : ZMod N) := by
    rw [MulChar.inv_apply_eq_inv', ← MulChar.coe_toUnitHom, ← MulChar.coe_toUnitHom, map_inv, Units.val_inv_eq_inv_val, inv_inv]
  simp only [Equiv.inv_apply, inv_inv, this]

omit [CharZero K] in

theorem chiAvg_inv (N p m k : ℕ) [NeZero N] (ψ : DirichletCharacter K (p ^ m)) (χ : DirichletCharacter K N)
    (c d x : ℤ) (s : ℕ) :
    chiAvg N p m k ψ (fun n => χ⁻¹ (n : ZMod N)) c d x s =
      ∑ δ : (ZMod N)ˣ, χ (δ : ZMod N) * coPtSb N p m k ψ c d (x * ((δ : ZMod N).val : ℤ)) ((δ : ZMod N).val : ℤ) s := by
  simp only [chiAvg, ZMod.natCast_zmod_val, MulChar.inv_apply_eq_inv', inv_inv]

omit [CharZero K] in

theorem chiAvg_eq_sum_inv (N p m k : ℕ) [NeZero N] (ψ : DirichletCharacter K (p ^ m)) (χ : DirichletCharacter K N)
    (c d x : ℤ) (s : ℕ) :
    chiAvg N p m k ψ (fun n => χ (n : ZMod N)) c d x s =
      ∑ δ : (ZMod N)ˣ, χ (δ : ZMod N) *
        coPtSb N p m k ψ c d (x * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ)) (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) s := by
  have h := chiAvg_inv N p m k ψ χ⁻¹ c d x s
  rw [inv_inv] at h
  rw [h, sum_mul_coPtSb_eq_sum_inv, inv_inv]

omit [CharZero K] in

theorem sum_mul_coPtSb_shift (N p m k : ℕ) [NeZero N] (ψ : DirichletCharacter K (p ^ m)) (χ : DirichletCharacter K N)
    (c d x : ℤ) (t : (ZMod N)ˣ) (s : ℕ) :
    ∑ δ : (ZMod N)ˣ, χ (δ : ZMod N) * coPtSb N p m k ψ c d (((t : ZMod N).val : ℤ) * (x * ((δ : ZMod N).val : ℤ)))
        (((t : ZMod N).val : ℤ) * ((δ : ZMod N).val : ℤ)) s =
      (χ (t : ZMod N))⁻¹ *
        ∑ δ : (ZMod N)ˣ, χ (δ : ZMod N) * coPtSb N p m k ψ c d (x * ((δ : ZMod N).val : ℤ)) ((δ : ZMod N).val : ℤ) s := by
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft t) _ _ fun δ => ?_
  have hb : ((t : ZMod N).val : ℤ) * ((δ : ZMod N).val : ℤ) ≡ (((t * δ : (ZMod N)ˣ) : ZMod N).val : ℤ) [ZMOD N] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    simp only [ZMod.natCast_zmod_val]
  have ha : ((t : ZMod N).val : ℤ) * (x * ((δ : ZMod N).val : ℤ)) ≡ x * (((t * δ : (ZMod N)ˣ) : ZMod N).val : ℤ) [ZMOD N] := by
    rw [mul_left_comm]
    exact hb.mul_left x
  have ht : χ (t : ZMod N) ≠ 0 := by
    rw [← MulChar.coe_toUnitHom]
    exact Units.ne_zero _
  rw [coPtSb_congr N p m k ψ c d ha hb]
  simp only [Equiv.coe_mulLeft, Units.val_mul, map_mul]
  field_simp

omit [CharZero K] in

theorem chiAvg_shift (N p m k : ℕ) [NeZero N] (ψ : DirichletCharacter K (p ^ m)) (χ : DirichletCharacter K N)
    (c d x : ℤ) (t : (ZMod N)ˣ) (s : ℕ) :
    ∑ δ : (ZMod N)ˣ, (χ (δ : ZMod N))⁻¹ * coPtSb N p m k ψ c d (((t : ZMod N).val : ℤ) * (x * ((δ : ZMod N).val : ℤ)))
        (((t : ZMod N).val : ℤ) * ((δ : ZMod N).val : ℤ)) s =
      χ (t : ZMod N) * chiAvg N p m k ψ (fun n => χ (n : ZMod N)) c d x s := by
  have h := sum_mul_coPtSb_shift N p m k ψ χ⁻¹ c d x t s
  simp only [MulChar.inv_apply_eq_inv', inv_inv] at h
  simp only [h, chiAvg, ZMod.natCast_zmod_val]

example (p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d x : ℤ) (s : ℕ) :
    chiAvg 1 p m k ψ (fun _ => 1) c d x s = GlobalTheory.KummerEisensteinGalois.coPtS 1 p m k ψ c d x s := by
  rw [chiAvg, Fintype.sum_unique, ← coPtSb_one, inv_one, one_mul,
    coPtSb_congr 1 p m k ψ c d (a' := x) (b' := 1) Int.modEq_one Int.modEq_one]

example (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (a b : ℤ) (s : ℕ) : coPtSb N p m k ψ 1 1 a b s = 0 := by
  simp [coPtSb]

example : GlobalTheory.KummerEisensteinGalois.coPtMu (K := ℚ) 5 3 0 3 1 1 1 2 = 1 := by
  have h1 : ∀ y : ZMod (3 ^ 0), (1 : DirichletCharacter ℚ (3 ^ 0)) y = 1 := fun y =>
    MulChar.one_apply (@isUnit_of_subsingleton _ _ (inferInstanceAs (Subsingleton (ZMod 1))) y)
  simp [GlobalTheory.KummerEisensteinGalois.coPtMu, GlobalTheory.KummerEisensteinGalois.cmul, GlobalTheory.KummerEisensteinGalois.ffMu, GlobalTheory.KummerEisensteinGalois.eeMu, Finset.sum_range_succ, h1, Int.ModEq]

end GlobalTheory.LambdaValuationPowers
