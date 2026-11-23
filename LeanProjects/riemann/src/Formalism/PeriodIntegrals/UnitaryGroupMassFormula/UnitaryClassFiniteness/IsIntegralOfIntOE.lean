import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing

noncomputable section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.UJClassFin

open PI.UJClassFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem intAf_iff (a : Af F) : a ∈ intAf F ↔ a ∈ Formalism.UG.intAd F := Iff.rfl

theorem intAf_mul {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a * b ∈ intAf F := (intAf_iff _).mpr (mul_mem ((intAf_iff a).mp ha) ((intAf_iff b).mp hb))

theorem intAf_one : (1 : Af F) ∈ intAf F := (intAf_iff _).mpr (one_mem _)

variable (F E) in

def Oh : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {r | ∃ a ∈ intAf F, ∃ e : E, IsIntegral ℤ e ∧ r = a ⊗ₜ[F] e}

theorem tmul_mem_Oh {a : Af F} (ha : a ∈ intAf F) {e : E} (he : IsIntegral ℤ e) : a ⊗ₜ[F] e ∈ Oh F E := AddSubgroup.subset_closure ⟨a, ha, e, he, rfl⟩

theorem Oh_mul {x y : Af F ⊗[F] E} (hx : x ∈ Oh F E) (hy : y ∈ Oh F E) : x * y ∈ Oh F E := by
  unfold Oh at hx hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem y hy' =>
    induction hx using AddSubgroup.closure_induction with
    | mem x hx' =>
      obtain ⟨a, ha, e, he, rfl⟩ := hx'
      obtain ⟨b, hb, f, hf, rfl⟩ := hy'
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact AddSubgroup.subset_closure ⟨a * b, intAf_mul ha hb, e * f, he.mul hf, rfl⟩
    | zero =>
      rw [zero_mul]
      exact zero_mem _
    | add x x' _ _ h1 h2 =>
      rw [add_mul]
      exact add_mem h1 h2
    | neg x _ h1 =>
      rw [neg_mul]
      exact neg_mem h1
  | zero =>
    rw [mul_zero]
    exact zero_mem _
  | add y y' _ _ h1 h2 =>
    rw [mul_add]
    exact add_mem h1 h2
  | neg y _ h1 =>
    rw [mul_neg]
    exact neg_mem h1

theorem isIntegral_of_intOE {e : E} (he : e ∈ Formalism.UG.intOE E) : IsIntegral ℤ e := by
  obtain ⟨a, rfl⟩ := RingHom.mem_range.mp he
  exact RingOfIntegers.isIntegral_coe a

theorem nsmul_tmul' (m n : ℕ) (a : Af F) (e : E) :
    (m * n) • (a ⊗ₜ[F] e) = ((m : Af F) * a) ⊗ₜ[F] ((n : E) * e) := by
  rw [← Nat.cast_smul_eq_nsmul F, Nat.cast_mul, mul_smul, ← TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']
  congr 1
  · rw [Algebra.smul_def, map_natCast]
  · rw [Algebra.smul_def, map_natCast]

theorem den (r : Af F ⊗[F] E) : ∃ m : ℕ, 0 < m ∧ m • r ∈ Oh F E := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩
  | tmul a e =>
    obtain ⟨m1, hm1, h1⟩ := PIW.AdelClassFin.DictRing.af_denom a
    obtain ⟨m2, hm2, h2⟩ := PIW.AdelClassFin.DictRing.e_denom e
    refine ⟨m1 * m2, Nat.mul_pos hm1 hm2, ?_⟩
    rw [nsmul_tmul']
    exact tmul_mem_Oh h1 (isIntegral_of_intOE h2)
  | add x y hx hy =>
    obtain ⟨m1, hm1, h1⟩ := hx
    obtain ⟨m2, hm2, h2⟩ := hy
    refine ⟨m1 * m2, Nat.mul_pos hm1 hm2, ?_⟩
    rw [smul_add, mul_comm m1 m2, mul_smul, mul_comm m2 m1, mul_smul]
    exact add_mem (AddSubgroup.nsmul_mem _ h1 _) (AddSubgroup.nsmul_mem _ h2 _)

theorem alg_tmul (t : F) (a : Af F) (e : E) :
    (algebraMap F (Af F) t * a) ⊗ₜ[F] e = a ⊗ₜ[F] (t • e) := by
  rw [← Algebra.smul_def, TensorProduct.smul_tmul]

theorem approx (N : ℕ) (hN : 0 < N) (r : Af F ⊗[F] E) :
    ∃ e : E, ∃ o ∈ Oh F E, r = inclR (Af F) e + N • o := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | tmul a e =>
    obtain ⟨d, hd, hde⟩ := PIW.AdelClassFin.DictRing.e_denom e
    have hdF : (d : F) ≠ 0 := by exact_mod_cast hd.ne'
    set a' : Af F := algebraMap F (Af F) (d : F)⁻¹ * a with ha'
    have h1 : a ⊗ₜ[F] e = a' ⊗ₜ[F] ((d : E) * e) := by
      rw [ha', alg_tmul]
      congr 1
      rw [Algebra.smul_def, ← mul_assoc, map_inv₀, map_natCast,
        inv_mul_cancel₀ (by exact_mod_cast hd.ne' : (d : E) ≠ 0), one_mul]
    obtain ⟨m, hm, hma⟩ := PIW.AdelClassFin.DictRing.af_denom a'
    obtain ⟨β, y, hy, hβ⟩ := PIW.AdelClassFin.DictRing.af_approx _ hma (N * m) (Nat.mul_pos hN hm)
    have hmF : (m : F) ≠ 0 := by exact_mod_cast hm.ne'
    have h2 : a' = algebraMap F (Af F) ((m : F)⁻¹ * algebraMap (𝓞 F) F β) + (N : Af F) * y := by
      have hinv : algebraMap F (Af F) (m : F)⁻¹ * (m : Af F) = 1 := by
        rw [← map_natCast (algebraMap F (Af F)) m, ← map_mul, inv_mul_cancel₀ hmF, map_one]
      have e1 : algebraMap F (Af F) (m : F)⁻¹ * algebraMap (𝓞 F) (Af F) β =
          algebraMap F (Af F) ((m : F)⁻¹ * algebraMap (𝓞 F) F β) := by
        rw [map_mul, ← IsScalarTower.algebraMap_apply]
      have e2 : algebraMap F (Af F) (m : F)⁻¹ * (((N * m : ℕ) : Af F) * y) = (N : Af F) * y := by
        rw [Nat.cast_mul, mul_comm (N : Af F) (m : Af F), mul_assoc (m : Af F),
          ← mul_assoc (algebraMap F (Af F) (m : F)⁻¹), hinv, one_mul]
      calc a' = algebraMap F (Af F) (m : F)⁻¹ * ((m : Af F) * a') := by rw [← mul_assoc, hinv, one_mul]
        _ = _ := by rw [hβ, mul_add, e1, e2]
    refine ⟨((m : F)⁻¹ * algebraMap (𝓞 F) F β) • ((d : E) * e), y ⊗ₜ[F] ((d : E) * e),
      tmul_mem_Oh hy (isIntegral_of_intOE hde), ?_⟩
    rw [h1, h2, TensorProduct.add_tmul, ← mul_one (algebraMap F (Af F) _), alg_tmul, ← nsmul_eq_mul,
      TensorProduct.smul_tmul']
    simp only [nsmul_eq_mul]
    rfl
  | add x y hx hy =>
    obtain ⟨e1, o1, ho1, rfl⟩ := hx
    obtain ⟨e2, o2, ho2, rfl⟩ := hy
    refine ⟨e1 + e2, o1 + o2, add_mem ho1 ho2, ?_⟩
    rw [map_add, smul_add]; abel

theorem nat_mult (c : 𝓞 F) (hc : c ≠ 0) : ∃ k : ℕ, 0 < k ∧ ∃ c' : 𝓞 F, (k : 𝓞 F) = c * c' := by
  obtain ⟨c', h⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {c}))
  refine ⟨Ideal.absNorm (Ideal.span {c}), ?_, c', by rw [← h, mul_comm]⟩
  rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hc

theorem low_nat {M : ℕ} (L : Set (Fin M → E))
    (h5 : ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ L) :
    ∃ k : ℕ, 0 < k ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L := by
  obtain ⟨c, hc, hL⟩ := h5
  obtain ⟨k, hk, c', hkc⟩ := nat_mult c hc
  refine ⟨k, hk, fun i e he => ?_⟩
  have hkF : (k : F) = (c : F) * (c' : F) := by
    have h1 := congrArg (algebraMap (𝓞 F) F) hkc
    rw [map_natCast, map_mul] at h1
    exact h1
  have he' : IsIntegral ℤ ((c' : F) • e) := by
    rw [Algebra.smul_def]
    exact (map_isIntegral_int (algebraMap F E) (RingOfIntegers.isIntegral_coe c')).mul he
  have e1 : (k : F) • e = (c : F) • ((c' : F) • e) := by
    rw [smul_smul, ← hkF]
  rw [e1]
  exact hL i _ he'

end PI.UnitaryGroupMassFormula.UJClassFin
