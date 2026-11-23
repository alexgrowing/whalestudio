import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.CycFieldA

noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKRes.ResSplit

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem dvd_mul_div_gcd (f r : ℕ) : r ∣ f * (r / Nat.gcd f r) := by
  refine ⟨f / Nat.gcd f r, ?_⟩
  rw [← Nat.mul_div_assoc f (Nat.gcd_dvd_right f r), ← Nat.mul_div_assoc r (Nat.gcd_dvd_left f r), mul_comm]

theorem Qr_le_Kn {f : ℕ} (hq : qK p K = p ^ f) (r : ℕ) : Qr p r ≤ Kn p K (r / Nat.gcd f r) := by
  apply UnramifiedExtensions.Kn_le (Q0 p) bot_le
  intro ζ hζ
  apply UnramifiedExtensions.mem_Kn_of_pow K
  rw [residue_cardinality_base_field] at hζ
  obtain ⟨t, ht⟩ := dvd_mul_div_gcd f r
  obtain ⟨c, hc⟩ : p ^ r - 1 ∣ (p ^ r) ^ t - 1 := by simpa using Nat.sub_dvd_pow_sub_pow (p ^ r) 1 t
  rw [hq, ← pow_mul, ht, pow_mul, hc, pow_mul, hζ, one_pow]

def incQ {f : ℕ} (hq : qK p K = p ^ f) (r : ℕ) : Qr p r →ₐ[ℚ_[p]] Kn p K (r / Nat.gcd f r) :=
  IntermediateField.inclusion (Qr_le_Kn p K hq r)

def incK (n : ℕ) : K →ₐ[ℚ_[p]] Kn p K n := IntermediateField.inclusion (UnramifiedExtensions.le_Kn K n)

def comp {f : ℕ} (hq : qK p K = p ^ f) (r i : ℕ) : KQ p K r →ₐ[ℚ_[p]] Kn p K (r / Nat.gcd f r) :=
  Algebra.TensorProduct.productMap (incK p K _) ((incQ p K hq r).comp ((frobQ p r) ^ i))

def eMap {f : ℕ} (hq : qK p K = p ^ f) (r : ℕ) :
    KQ p K r →ₐ[ℚ_[p]] (Fin (Nat.gcd f r) → Kn p K (r / Nat.gcd f r)) :=
  Pi.algHom _ _ fun i => comp p K hq r i

theorem eMap_apply {f : ℕ} (hq : qK p K = p ^ f) (r : ℕ) (x : KQ p K r) (i : Fin (Nat.gcd f r)) :
    eMap p K hq r x i = comp p K hq r i x := rfl

theorem coe_incQ {f : ℕ} (hq : qK p K = p ^ f) (r : ℕ) (b : Qr p r) :
    ((incQ p K hq r b : Kn p K (r / Nat.gcd f r)) : PadicAlgCl p) = b :=
  IntermediateField.coe_inclusion _ _

theorem coe_incK (n : ℕ) (a : K) : ((incK p K n a : Kn p K n) : PadicAlgCl p) = a :=
  IntermediateField.coe_inclusion _ _

theorem coe_frobQ (r : ℕ) (b : Qr p r) :
    ((frobQ p r b : Qr p r) : PadicAlgCl p) = frobK p (Q0 p) (b : PadicAlgCl p) := rfl

theorem coe_frobQ_pow (r i : ℕ) (b : Qr p r) :
    (((frobQ p r ^ i) b : Qr p r) : PadicAlgCl p) = (frobK p (Q0 p) ^ i) (b : PadicAlgCl p) := by
  induction i generalizing b with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, AlgHom.mul_apply, ih, pow_succ, AlgEquiv.mul_apply, coe_frobQ]

theorem comp_tmul {f : ℕ} (hq : qK p K = p ^ f) (r i : ℕ) (a : K) (b : Qr p r) :
    ((comp p K hq r i (a ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) : Kn p K (r / Nat.gcd f r)) : PadicAlgCl p) =
      (a : PadicAlgCl p) * (frobK p (Q0 p) ^ i) (b : PadicAlgCl p) := by
  have h : comp p K hq r i (a ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) =
      incK p K _ a * incQ p K hq r ((frobQ p r ^ i) b) :=
    Algebra.TensorProduct.productMap_apply_tmul _ _ a b
  rw [h, MulMemClass.coe_mul, coe_incK, coe_incQ, coe_frobQ_pow]

theorem comp_sigKQ {f : ℕ} (hq : qK p K = p ^ f) (r i : ℕ) (x : KQ p K r) :
    comp p K hq r i (sigKQ p K r x) = comp p K hq r (i + 1) x := by
  have h : ∀ y : K ⊗[ℚ_[p]] Qr p r, comp p K hq r i (sigKQ p K r y) = comp p K hq r (i + 1) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact (congrArg _ (map_zero _)).trans ((map_zero _).trans (map_zero _).symm)
    | tmul a b =>
      have h1 : sigKQ p K r (a ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) = (a ⊗ₜ[ℚ_[p]] frobQ p r b : K ⊗[ℚ_[p]] Qr p r) :=
        Algebra.TensorProduct.map_tmul _ _ a b
      rw [h1]
      apply Subtype.ext
      rw [comp_tmul, comp_tmul, coe_frobQ, pow_succ, AlgEquiv.mul_apply]
    | add y z hy hz =>
      have e1 : sigKQ p K r (y + z) = sigKQ p K r y + sigKQ p K r z := map_add _ _ _
      have e2 : comp p K hq r (i + 1) (y + z) = comp p K hq r (i + 1) y + comp p K hq r (i + 1) z := map_add _ _ _
      rw [e1, map_add, e2, hy, hz]
  exact h x

theorem comp_inclK {f : ℕ} (hq : qK p K = p ^ f) (r i : ℕ) (a : K) :
    ((comp p K hq r i (inclK p K r a) : Kn p K (r / Nat.gcd f r)) : PadicAlgCl p) = a := by
  have h : inclK p K r a = (a ⊗ₜ[ℚ_[p]] (1 : Qr p r) : K ⊗[ℚ_[p]] Qr p r) := rfl
  rw [h, comp_tmul, IntermediateField.coe_one, map_one, mul_one]

theorem comp_inclQ {f : ℕ} (hq : qK p K = p ^ f) (r i : ℕ) (b : Qr p r) :
    ((comp p K hq r i (inclQ p K r b) : Kn p K (r / Nat.gcd f r)) : PadicAlgCl p) =
      (frobK p (Q0 p) ^ i) (b : PadicAlgCl p) := by
  have h : inclQ p K r b = ((1 : K) ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) := rfl
  rw [h, comp_tmul, IntermediateField.coe_one, one_mul]

theorem frobenius_pow_root_of_unity {N : ℕ} (hN : ¬ p ∣ N) {ζ : PadicAlgCl p} (hζ : ζ ^ N = 1) (i : ℕ) :
    (frobK p (Q0 p) ^ i) ζ = ζ ^ p ^ i := by
  have hfd : FiniteDimensional ℚ_[p] (Q0 p) := inferInstance
  induction i with
  | zero => simp
  | succ n ih =>
    have h1 : (ζ ^ p ^ n) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    rw [pow_succ', AlgEquiv.mul_apply, ih, (isFrob_iff hfd _).1 (isFrob_frobK hfd) _ N hN h1, residue_cardinality_base_field,
      ← pow_mul, pow_succ]

end GlobalTheory.LKRes.ResSplit
