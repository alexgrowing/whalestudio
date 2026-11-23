import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import ReciprocityTheory.Automorphisms.PlaceA

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem tame_valued_int (a : 𝓞 L) :
    Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) a) = v.valuation L (algebraMap (𝓞 L) L a) :=
  ReciprocityTheory.Aut.adic_valued_algebraMap v (algebraMap (𝓞 L) L a)

theorem tame_valued_lt_one_iff (a : 𝓞 L) :
    Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) a) < 1 ↔ a ∈ v.asIdeal := by
  rw [tame_valued_int,
    HeightOneSpectrum.valuation_lt_one_iff_mem]

theorem tame_mk_eq {u : v.adicCompletion L} {a b : 𝓞 L}
    (ha : Valued.v (u - algebraMap (𝓞 L) (v.adicCompletion L) a) < 1)
    (hb : Valued.v (u - algebraMap (𝓞 L) (v.adicCompletion L) b) < 1) :
    Ideal.Quotient.mk v.asIdeal a = Ideal.Quotient.mk v.asIdeal b := by
  rw [Ideal.Quotient.eq, ← tame_valued_lt_one_iff, map_sub]
  have e : algebraMap (𝓞 L) (v.adicCompletion L) a - algebraMap (𝓞 L) (v.adicCompletion L) b =
      (u - algebraMap (𝓞 L) (v.adicCompletion L) b) - (u - algebraMap (𝓞 L) (v.adicCompletion L) a) := by
    ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hb ha)

def unitPart : (v.adicCompletion L)ˣ →* (v.adicCompletion L)ˣ where
  toFun x := x * atFin v (unif v) ^ WithZero.log (Valued.v (x : v.adicCompletion L))
  map_one' := by simp
  map_mul' x y := by
    rw [Units.val_mul, map_mul, WithZero.log_mul (by simp) (by simp), zpow_add]
    exact mul_mul_mul_comm _ _ _ _

theorem isUnitAt_unitPart (x : (v.adicCompletion L)ˣ) : IsUnitAt v (unitPart v x) := by
  have h : Valued.v ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) =
      WithZero.exp (-1 : ℤ) := unif_spec v
  have hx : Valued.v (x : v.adicCompletion L) ≠ 0 := by simp
  show Valued.v ((x * atFin v (unif v) ^ WithZero.log (Valued.v (x : v.adicCompletion L)) :
    (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, h, ← WithZero.exp_zsmul]
  nth_rewrite 1 [← WithZero.exp_log hx]
  rw [← WithZero.exp_add]
  simp

theorem unitPart_of_isUnitAt {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) : unitPart v x = x := by
  have h : Valued.v (x : v.adicCompletion L) = 1 := hx
  show x * atFin v (unif v) ^ WithZero.log (Valued.v (x : v.adicCompletion L)) = x
  rw [h]
  simp

theorem exists_unitPart_approx (x : (v.adicCompletion L)ˣ) : ∃ a : 𝓞 L,
    Valued.v ((unitPart v x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) a) < 1 :=
  ReciprocityTheory.Aut.adic_exists_approx v _ (le_of_eq (isUnitAt_unitPart v x))

def resPart : (v.adicCompletion L)ˣ →* 𝓞 L ⧸ v.asIdeal where
  toFun x := Ideal.Quotient.mk v.asIdeal (exists_unitPart_approx v x).choose
  map_one' := by
    refine tame_mk_eq v (b := 1) (exists_unitPart_approx v 1).choose_spec ?_
    simp
  map_mul' x y := by
    rw [← map_mul]
    refine tame_mk_eq v (exists_unitPart_approx v (x * y)).choose_spec ?_
    have hx := (exists_unitPart_approx v x).choose_spec
    have hy := (exists_unitPart_approx v y).choose_spec
    set a := (exists_unitPart_approx v x).choose
    set b := (exists_unitPart_approx v y).choose
    have hu : Valued.v (unitPart v x : v.adicCompletion L) = 1 := isUnitAt_unitPart v x
    have hb : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) b) ≤ 1 := by
      rw [tame_valued_int]
      exact v.valuation_le_one b
    have e : (unitPart v (x * y) : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) (a * b) =
        (unitPart v x : v.adicCompletion L) *
          ((unitPart v y : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) b) +
        ((unitPart v x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) a) *
          algebraMap (𝓞 L) (v.adicCompletion L) b := by
      rw [map_mul, map_mul, Units.val_mul]
      ring
    rw [e]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rwa [map_mul, hu, one_mul]
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hb) hx

theorem resPart_eq {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) {a : 𝓞 L}
    (ha : Valued.v ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) a) < 1) :
    resPart v x = Ideal.Quotient.mk v.asIdeal a := by
  refine tame_mk_eq v (exists_unitPart_approx v x).choose_spec ?_
  rwa [unitPart_of_isUnitAt v hx]

open Classical in

theorem exists_tameLoc_of_residue : ∀ (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) (θ0 : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ), ∃ θ : (v.adicCompletion L)ˣ →* ℂˣ, TameLoc v θ ∧ (∀ (k : Lˣ) (y : 𝓞 L) (b : (𝓞 L ⧸ v.asIdeal)ˣ), (k : L) = (y : L) → (b : 𝓞 L ⧸ v.asIdeal) = Ideal.Quotient.mk v.asIdeal y → θ (atFin v k) = θ0 b) ∧ ∀ x, IsUnitAt v x → ∃ b, θ x = θ0 b := by
  intro L _ _ v θ0
  haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  refine ⟨θ0.comp (resPart v).toHomUnits, ⟨fun x => ?_, fun x hx h1 => ?_⟩, fun k y b hk hb => ?_,
    fun x _ => ⟨_, rfl⟩⟩
  · have hf : IsOfFinOrder ((θ0 ((resPart v).toHomUnits x) : ℂˣ) : ℂ) :=
      ((Units.coeHom ℂ).comp θ0).isOfFinOrder (isOfFinOrder_of_finite _)
    exact hf.norm_eq_one
  · have e : (resPart v).toHomUnits x = 1 := by
      apply Units.ext
      show resPart v x = Ideal.Quotient.mk v.asIdeal 1
      refine resPart_eq v hx ?_
      rw [map_one]
      refine lt_of_le_of_lt h1 ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    rw [MonoidHom.comp_apply, e, map_one]
  · have ek : ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) =
        algebraMap (𝓞 L) (v.adicCompletion L) y := by
      show algebraMap L (v.adicCompletion L) (k : L) = _
      rw [hk]
      rfl
    have hy : y ∉ v.asIdeal := by
      intro hy
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hy] at hb
      haveI := v.isPrime
      exact b.ne_zero hb
    have hu : IsUnitAt v (atFin v k) := by
      show Valued.v ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1
      rw [ek]
      refine le_antisymm ?_ (not_lt.1 fun h => hy ((tame_valued_lt_one_iff v y).1 h))
      rw [tame_valued_int]
      exact v.valuation_le_one y
    have e : (resPart v).toHomUnits (atFin v k) = b := by
      apply Units.ext
      show resPart v (atFin v k) = _
      rw [hb]
      refine resPart_eq v hu ?_
      rw [ek, sub_self, map_zero]
      exact zero_lt_one
    rw [MonoidHom.comp_apply, e]

end GlobalTheory.Mem.Chr
