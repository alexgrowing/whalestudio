import Mathlib
import GroundTheory.FunctionField.PlaceDefs
import GroundTheory.FunctionField.PlaceBasic
import GroundTheory.FunctionField.Approximation
import GroundTheory.FunctionField.ValuationAevalSubCoeffZeroLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.FunctionField

open Module

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

abbrev Divisor := Place k K →₀ ℤ

variable {k K}

namespace Divisor

noncomputable def deg : Divisor k K →+ ℤ :=
  Finsupp.liftAddHom fun v => AddMonoidHom.mulRight (v.deg : ℤ)

theorem deg_apply (D : Divisor k K) : deg D = D.sum fun v n => n * v.deg := by
  simp [deg, Finsupp.liftAddHom_apply]

@[simp]
theorem deg_single (v : Place k K) (n : ℤ) : deg (Finsupp.single v n) = n * v.deg := by
  simp [deg]

theorem deg_eq_sum (D : Divisor k K) : deg D = ∑ v ∈ D.support, D v * v.deg := by
  rw [deg_apply, Finsupp.sum]

theorem deg_nonneg {D : Divisor k K} (hD : 0 ≤ D) : 0 ≤ deg D := by
  rw [deg_eq_sum]
  exact Finset.sum_nonneg fun v _ => mul_nonneg (by simpa using Finsupp.le_def.1 hD v)
    (Int.natCast_nonneg _)

variable [IsFunctionField k K]

theorem eq_zero_of_deg_eq_zero {D : Divisor k K} (hD : 0 ≤ D) (h : deg D = 0) : D = 0 := by
  rw [deg_eq_sum] at h
  have hnn : ∀ v ∈ D.support, 0 ≤ D v * v.deg := fun v _ =>
    mul_nonneg (by simpa using Finsupp.le_def.1 hD v) (Int.natCast_nonneg _)
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h
  ext v
  by_cases hv : v ∈ D.support
  · have := h0 v hv
    have hdeg : (0 : ℤ) < v.deg := by exact_mod_cast v.deg_pos
    rcases mul_eq_zero.1 this with h' | h'
    · simpa using h'
    · omega
  · simpa using hv

end Divisor

variable [IsFunctionField k K]

noncomputable def divisor (x : K) : Divisor k K :=
  Finsupp.ofSupportFinite (fun v : Place k K => v.ord x) (Place.finite_ord_ne_zero x)

@[simp]
theorem divisor_apply (x : K) (v : Place k K) : divisor x v = v.ord x := rfl

@[simp]
theorem divisor_zero : divisor (0 : K) = (0 : Divisor k K) := by
  ext v; simp

@[simp]
theorem divisor_one : divisor (1 : K) = (0 : Divisor k K) := by
  ext v; simp

theorem divisor_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    divisor (x * y) = (divisor x + divisor y : Divisor k K) := by
  ext v; simp [v.ord_mul hx hy]

@[simp]
theorem divisor_inv (x : K) : divisor x⁻¹ = -(divisor x : Divisor k K) := by
  ext v; simp [Place.ord_inv]

theorem divisor_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    divisor (x / y) = (divisor x - divisor y : Divisor k K) := by
  rw [div_eq_mul_inv, divisor_mul hx (inv_ne_zero hy), divisor_inv, sub_eq_add_neg]

theorem divisor_eq_zero_of_isAlgebraic {x : K} (hx : IsAlgebraic k x) (hx0 : x ≠ 0) :
    divisor x = (0 : Divisor k K) := by
  ext v; simp [v.ord_eq_zero_of_isAlgebraic hx hx0]

noncomputable def divisorHom : Additive Kˣ →+ Divisor k K where
  toFun x := divisor ((x.toMul : Kˣ) : K)
  map_zero' := by simp
  map_add' x y := by
    simp only [toMul_add, Units.val_mul]
    exact divisor_mul (Additive.toMul x).ne_zero (Additive.toMul y).ne_zero

theorem divisorHom_apply (x : Kˣ) : divisorHom (Additive.ofMul x) = (divisor (x : K) : Divisor k K) :=
  rfl

variable (k K) in

noncomputable def principalDivisors : AddSubgroup (Divisor k K) := (divisorHom (k := k)).range

theorem mem_principalDivisors {D : Divisor k K} :
    D ∈ principalDivisors k K ↔ ∃ x : K, x ≠ 0 ∧ divisor x = D := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, (Additive.toMul x).ne_zero, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Additive.ofMul (Units.mk0 x hx), rfl⟩

noncomputable def zeroDivisor (x : K) : Divisor k K := divisor x ⊔ 0

noncomputable def poleDivisor (x : K) : Divisor k K := divisor x⁻¹ ⊔ 0

@[simp]
theorem zeroDivisor_apply (x : K) (v : Place k K) :
    zeroDivisor x v = max (v.ord x) 0 := rfl

@[simp]
theorem poleDivisor_apply (x : K) (v : Place k K) :
    poleDivisor x v = max (-v.ord x) 0 := by
  simp [poleDivisor, Finsupp.sup_apply]

theorem zeroDivisor_nonneg (x : K) : (0 : Divisor k K) ≤ zeroDivisor x :=
  Finsupp.le_def.2 fun v => by simp

theorem poleDivisor_nonneg (x : K) : (0 : Divisor k K) ≤ poleDivisor x :=
  Finsupp.le_def.2 fun v => by simp

@[simp]
theorem poleDivisor_inv (x : K) : poleDivisor x⁻¹ = (zeroDivisor x : Divisor k K) := by
  simp [poleDivisor, zeroDivisor]

@[simp]
theorem zeroDivisor_inv (x : K) : zeroDivisor x⁻¹ = (poleDivisor x : Divisor k K) := rfl

theorem zeroDivisor_sub_poleDivisor (x : K) :
    zeroDivisor x - poleDivisor x = (divisor x : Divisor k K) := by
  ext v
  simp only [Finsupp.coe_sub, Pi.sub_apply, zeroDivisor_apply, poleDivisor_apply, divisor_apply]
  rcases le_total 0 (v.ord x) with h | h
  · rw [max_eq_left h, max_eq_right (by omega)]; ring
  · rw [max_eq_right h, max_eq_left (by omega)]; ring

namespace Divisor

def L (D : Divisor k K) : Submodule k K where
  carrier := {z | ∀ v : Place k K, v.valuation z ≤ WithZero.exp (D v)}
  add_mem' {a b} ha hb v := Valuation.map_add_le _ (ha v) (hb v)
  zero_mem' v := by rw [map_zero]; exact zero_le
  smul_mem' c z hz v := by
    rw [Algebra.smul_def, map_mul]
    by_cases hc : c = 0
    · rw [hc, map_zero, map_zero, zero_mul]; exact zero_le
    · rw [v.valuation_algebraMap' hc, one_mul]; exact hz v

theorem mem_L {D : Divisor k K} {z : K} :
    z ∈ L D ↔ ∀ v : Place k K, v.valuation z ≤ WithZero.exp (D v) := Iff.rfl

theorem mem_L_iff_le {D : Divisor k K} {z : K} (hz : z ≠ 0) :
    z ∈ L D ↔ 0 ≤ divisor z + D := by
  rw [mem_L, Finsupp.le_def]
  refine forall_congr' fun v => ?_
  rw [v.valuation_le_exp_iff hz]
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply, divisor_apply]
  omega

theorem L_mono {D E : Divisor k K} (h : D ≤ E) : L D ≤ L E := fun _z hz v =>
  (hz v).trans (WithZero.exp_le_exp.2 (Finsupp.le_def.1 h v))

theorem mem_L_zero {z : K} : z ∈ L (0 : Divisor k K) ↔ IsAlgebraic k z := by
  rw [Place.isAlgebraic_iff_forall_mem, mem_L]
  refine forall_congr' fun v => ?_
  rw [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero, v.valuation_le_one_iff]

theorem L_eq_bot_of_nonpos {D : Divisor k K} (hD : D ≤ 0) {v : Place k K} (hv : D v < 0) :
    L D = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Submodule.mem_bot]
  by_contra hz0
  have hall : ∀ w : Place k K, z ∈ w.ring := fun w =>
    (w.valuation_le_one_iff z).1 ((hz w).trans (by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; simpa using Finsupp.le_def.1 hD w))
  have h0 := v.ord_eq_zero_of_isAlgebraic (Place.isAlgebraic_iff_forall_mem.2 hall) hz0
  have := hz v
  rw [v.valuation_le_exp_iff hz0, h0] at this
  omega

theorem finiteDimensional_L_add_single (D : Divisor k K) (v : Place k K)
    [FiniteDimensional k (L D)] :
    FiniteDimensional k (L (D + Finsupp.single v 1)) ∧
      finrank k (L (D + Finsupp.single v 1)) ≤ finrank k (L D) + v.deg := by
  classical
  set E := D + Finsupp.single v 1 with hE
  have hEv : E v = D v + 1 := by simp [E]
  have hEw : ∀ w, w ≠ v → E w = D w := fun w hw => by
    simp [E, Ne.symm hw]
  obtain ⟨t, ht⟩ := v.valuation_surjective (WithZero.exp (-(D v + 1)))
  have hmem : ∀ z : L E, t * (z : K) ∈ v.ring := fun z => by
    rw [← v.valuation_le_one_iff, map_mul, ht]
    calc WithZero.exp (-(D v + 1)) * v.valuation (z : K)
        ≤ WithZero.exp (-(D v + 1)) * WithZero.exp (E v) := mul_le_mul' le_rfl (z.2 v)
      _ = 1 := by rw [hEv, ← WithZero.exp_add]; simp
  let φ : L E →ₗ[k] v.ResidueField :=
    { toFun := fun z => IsLocalRing.residue v.ring ⟨t * z, hmem z⟩
      map_add' := fun a b => by
        rw [← map_add]
        congr 1
        ext
        simp [mul_add]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, Algebra.smul_def,
          IsScalarTower.algebraMap_apply k v.ring v.ResidueField,
          IsLocalRing.ResidueField.algebraMap_eq, ← map_mul]
        congr 1
        ext
        change t * ((c • a : L E) : K) = (algebraMap k v.ring c : K) * (t * a)
        rw [Submodule.coe_smul, Algebra.smul_def, Place.coe_algebraMap_apply]
        ring }
  have hker : ∀ z : L E, φ z = 0 ↔ (z : K) ∈ L D := by
    intro z
    change IsLocalRing.residue v.ring ⟨t * z, hmem z⟩ = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    change v.ring.valuation (t * z) < 1 ↔ _
    rw [← v.valuation_lt_one_iff, map_mul, ht]
    constructor
    · intro h w
      by_cases hw : w = v
      · rw [hw]
        by_cases hz : (z : K) = 0
        · rw [hz, map_zero]; exact zero_le
        · rw [v.valuation_eq_exp_neg_ord hz, ← WithZero.exp_add, ← WithZero.exp_zero,
            WithZero.exp_lt_exp] at h
          rw [v.valuation_eq_exp_neg_ord hz, WithZero.exp_le_exp]
          omega
      · rw [← hEw w hw]; exact z.2 w
    · intro h
      calc WithZero.exp (-(D v + 1)) * v.valuation (z : K)
          ≤ WithZero.exp (-(D v + 1)) * WithZero.exp (D v) := mul_le_mul' le_rfl (h v)
        _ < 1 := by rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  let ψ : LinearMap.ker φ →ₗ[k] L D :=
    ((L E).subtype.comp (LinearMap.ker φ).subtype).codRestrict (L D)
      fun z => (hker z.1).1 (LinearMap.mem_ker.1 z.2)
  have hψ : Function.Injective ψ := fun a b h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have : FiniteDimensional k (LinearMap.ker φ) := Module.Finite.of_injective ψ hψ
  have hrank := LinearMap.rank_range_add_rank_ker φ
  have hfin : FiniteDimensional k (L E) := by
    apply Module.rank_lt_aleph0_iff.1
    rw [← hrank]
    exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 k _) (Module.rank_lt_aleph0 k _)
  refine ⟨hfin, ?_⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 : finrank k (LinearMap.range φ) ≤ v.deg := Submodule.finrank_le _
  have h3 : finrank k (LinearMap.ker φ) ≤ finrank k (L D) :=
    LinearMap.finrank_le_finrank_of_injective hψ
  omega

theorem finiteDimensional_L_of_le_of_deg_lt (n : ℕ) :
    ∀ {D E : Divisor k K}, D ≤ E → deg (E - D) < n → FiniteDimensional k (L D) →
      FiniteDimensional k (L E) ∧
        (finrank k (L E) : ℤ) ≤ finrank k (L D) + deg E - deg D := by
  classical
  induction n with
  | zero =>
    intro D E hDE hn _
    have := deg_nonneg (sub_nonneg.2 hDE)
    omega
  | succ n ih =>
    intro D E hDE hn hD
    by_cases hED : E = D
    · subst hED
      exact ⟨hD, by omega⟩
    obtain ⟨v, hv⟩ : ∃ v, D v < E v := by
      by_contra h
      push Not at h
      exact hED (le_antisymm (Finsupp.le_def.2 h) hDE)
    set E' := E - Finsupp.single v 1 with hE'
    have hDE' : D ≤ E' := Finsupp.le_def.2 fun w => by
      rw [hE', Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h; omega
      · have := Finsupp.le_def.1 hDE w; omega
    have hn' : deg (E' - D) < n := by
      have h1 : deg (E' - D) = deg (E - D) - v.deg := by
        rw [hE', map_sub, map_sub, map_sub, deg_single]; ring
      have := v.deg_pos
      omega
    obtain ⟨hfin', hle'⟩ := ih hDE' hn' hD
    have hE : E = E' + Finsupp.single v 1 := by rw [hE']; abel
    have := hfin'
    obtain ⟨hfin, hle⟩ := finiteDimensional_L_add_single E' v
    rw [← hE] at hfin hle
    refine ⟨hfin, ?_⟩
    have hdeg : deg E = deg E' + v.deg := by rw [hE, map_add, deg_single, one_mul]
    have : (finrank k (L E) : ℤ) ≤ finrank k (L E') + v.deg := by exact_mod_cast hle
    omega

theorem finiteDimensional_L_of_le {D E : Divisor k K} (hDE : D ≤ E)
    [FiniteDimensional k (L D)] :
    FiniteDimensional k (L E) ∧
      (finrank k (L E) : ℤ) ≤ finrank k (L D) + deg E - deg D :=
  finiteDimensional_L_of_le_of_deg_lt ((deg (E - D)).toNat + 1) hDE (by omega) inferInstance

instance (D : Divisor k K) : FiniteDimensional k (L D) := by
  classical
  obtain ⟨v⟩ := Place.nonempty (k := k) (K := K)
  have hbot : L (-Finsupp.single v 1 : Divisor k K) = ⊥ :=
    L_eq_bot_of_nonpos (v := v) (Finsupp.le_def.2 fun w => by
      have h := Finsupp.single_apply (a := v) (a' := w) (b := (1 : ℤ))
      simp only [Finsupp.coe_neg, Pi.neg_apply, Finsupp.coe_zero, Pi.zero_apply]
      split_ifs at h <;> omega) (by simp)
  have : FiniteDimensional k (L (-Finsupp.single v 1 : Divisor k K)) := by
    rw [hbot]; infer_instance
  have := (finiteDimensional_L_of_le
    (le_sup_right : (-Finsupp.single v 1 : Divisor k K) ≤ D ⊔ -Finsupp.single v 1)).1
  exact Module.Finite.of_injective
    (Submodule.inclusion (L_mono (le_sup_left : D ≤ D ⊔ -Finsupp.single v 1)))
    (Submodule.inclusion_injective _)

theorem finrank_L_le_of_le {D E : Divisor k K} (hDE : D ≤ E) :
    (finrank k (L E) : ℤ) ≤ finrank k (L D) + deg E - deg D :=
  (finiteDimensional_L_of_le hDE).2

theorem L_zero :
    L (0 : Divisor k K) = Subalgebra.toSubmodule (algebraicClosure k K).toSubalgebra := by
  ext z
  rw [mem_L_zero]
  simp [mem_algebraicClosure_iff]

theorem finrank_L_zero : finrank k (L (0 : Divisor k K)) = finrank k (algebraicClosure k K) := by
  rw [L_zero]
  rfl

theorem finrank_L_le_deg_add {D : Divisor k K} (hD : 0 ≤ D) :
    (finrank k (L D) : ℤ) ≤ deg D + finrank k (algebraicClosure k K) := by
  have := finrank_L_le_of_le hD
  rw [finrank_L_zero, map_zero] at this
  omega

theorem finrank_L_le_deg_add_one (hk : algebraicClosure k K = ⊥) {D : Divisor k K}
    (hD : 0 ≤ D) : (finrank k (L D) : ℤ) ≤ deg D + 1 := by
  have := finrank_L_le_deg_add hD
  rw [hk, IntermediateField.finrank_bot] at this
  exact_mod_cast this

end Divisor

end GroundTheory.FunctionField
