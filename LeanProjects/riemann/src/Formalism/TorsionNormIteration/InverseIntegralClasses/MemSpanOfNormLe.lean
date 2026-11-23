import Formalism.TorsionNormIteration.InvIntegralOfClass

noncomputable section

universe u v

namespace Formalism.LT.FrobP

open Formalism.G

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem norm_sigma_le {p q : ℕ} {σ : K →+* K} (hσ : IsFrobLift p q σ) (hp : ‖(p : K)‖ < 1)
    (a : K) (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  have h1 : ‖σ a - a ^ q‖ ≤ ‖(p : K)‖ := hσ a ha
  have h2 : ‖a ^ q‖ ≤ 1 := by
    rw [norm_pow]
    first
      | exact pow_le_one₀ (norm_nonneg a) ha
      | exact pow_le_one q (norm_nonneg a) ha
  calc ‖σ a‖ = ‖(σ a - a ^ q) + a ^ q‖ := by rw [sub_add_cancel]
    _ ≤ max ‖σ a - a ^ q‖ ‖a ^ q‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le (h1.trans hp.le) h2

def sigmaO {p q : ℕ} {σ : K →+* K} (hσ : IsFrobLift p q σ) (hp : ‖(p : K)‖ < 1) :
    unitBall K →+* unitBall K :=
  (σ.comp (unitBall K).subtype).codRestrict (unitBall K)
    (fun x => norm_sigma_le hσ hp x.1 x.2)

theorem natCast_coe (p : ℕ) : (((p : unitBall K)) : K) = (p : K) := by
  first
    | exact map_natCast (unitBall K).subtype p
    | simp

theorem norm_le_of_mem_span {p : ℕ} (x : unitBall K)
    (hx : x ∈ Ideal.span {((p : ℕ) : unitBall K)}) : ‖(x : K)‖ ≤ ‖(p : K)‖ := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  have hy : ‖(y : K)‖ ≤ 1 := y.2
  have e : ((y * ((p : ℕ) : unitBall K) : unitBall K) : K) = (y : K) * (p : K) := by
    rw [← natCast_coe p]
    rfl
  rw [e, norm_mul]
  calc ‖(y : K)‖ * ‖(p : K)‖ ≤ 1 * ‖(p : K)‖ := mul_le_mul_of_nonneg_right hy (norm_nonneg _)
    _ = ‖(p : K)‖ := one_mul _

theorem mem_span_of_norm_le {p : ℕ} (hp0 : (p : K) ≠ 0) (x : unitBall K)
    (hx : ‖(x : K)‖ ≤ ‖(p : K)‖) : x ∈ Ideal.span {((p : ℕ) : unitBall K)} := by
  have hy : ‖(x : K) / (p : K)‖ ≤ 1 := by
    rw [norm_div]
    first
      | exact div_le_one_of_le₀ hx (norm_nonneg _)
      | exact (div_le_one (norm_pos_iff.mpr hp0)).mpr hx
  refine Ideal.mem_span_singleton'.mpr ⟨⟨(x : K) / (p : K), hy⟩, ?_⟩
  apply Subtype.ext
  show (x : K) / (p : K) * ((p : unitBall K) : K) = (x : K)
  rw [natCast_coe, div_mul_cancel₀ _ hp0]

theorem natCast_nonunit {p : ℕ} (hp : ‖(p : K)‖ < 1) :
    ((p : ℕ) : unitBall K) ∈ nonunits (unitBall K) := by
  rw [mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu'⟩ := hu.exists_left_inv
  have h2 : (u : K) * (p : K) = 1 := by
    have h0 := congrArg Subtype.val hu'
    rw [← natCast_coe p]
    exact h0
  have hu1 : ‖(u : K)‖ ≤ 1 := u.2
  have h3 := congrArg norm h2
  rw [norm_mul, norm_one] at h3
  have h4 : ‖(u : K)‖ * ‖(p : K)‖ ≤ ‖(p : K)‖ := by
    calc ‖(u : K)‖ * ‖(p : K)‖ ≤ 1 * ‖(p : K)‖ := mul_le_mul_of_nonneg_right hu1 (norm_nonneg _)
      _ = ‖(p : K)‖ := one_mul _
  linarith

def liftO {ι : Type v} (A : MvPowerSeries ι K) (hA : IntegralMv A) :
    MvPowerSeries ι (unitBall K) :=
  fun d => ⟨MvPowerSeries.coeff d A, hA d⟩

theorem map_liftO {ι : Type v} (A : MvPowerSeries ι K) (hA : IntegralMv A) :
    MvPowerSeries.map (unitBall K).subtype (liftO A hA) = A := by
  ext d
  rw [MvPowerSeries.coeff_map]
  rfl

theorem main {ι : Type v} (p h : ℕ) (hpr : p.Prime) (σ : K →+* K) (hp0 : (p : K) ≠ 0)
    (hp : ‖(p : K)‖ < 1) (hσ : IsFrobLift p (p ^ h) σ) (A : MvPowerSeries ι K)
    (hA : IntegralMv A) :
    DivByMv (p : K) (A ^ (p ^ h) - MvPowerSeries.expand (p ^ h) (pow_ne_zero h hpr.ne_zero)
      (MvPowerSeries.map σ A)) := by
  classical
  haveI : Fact p.Prime := ⟨hpr⟩
  haveI hchar : CharP (unitBall K ⧸ Ideal.span {((p : ℕ) : unitBall K)}) p :=
    CharP.quotient (unitBall K) p (natCast_nonunit hp)
  haveI : ExpChar (unitBall K ⧸ Ideal.span {((p : ℕ) : unitBall K)}) p := ExpChar.prime hpr
  have hq : p ^ h ≠ 0 := pow_ne_zero h hpr.ne_zero
  have hkey : (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)})).comp (sigmaO hσ hp)
      = (iterateFrobenius (unitBall K ⧸ Ideal.span {((p : ℕ) : unitBall K)}) p h).comp
          (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)})) := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, iterateFrobenius_def, ← map_pow]
    first
      | rw [Ideal.Quotient.eq]
      | rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    apply mem_span_of_norm_le hp0
    first
      | exact hσ c.1 c.2
      | (push_cast; exact hσ c.1 c.2)
  have h1 : MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)}))
        (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA))
      = MvPowerSeries.map (iterateFrobenius (unitBall K ⧸ Ideal.span {((p : ℕ) : unitBall K)}) p h)
        (MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)})) (liftO A hA)) := by
    ext d
    simp only [MvPowerSeries.coeff_map]
    exact RingHom.congr_fun hkey _
  have hmain : MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : unitBall K)}))
      ((liftO A hA) ^ (p ^ h) - MvPowerSeries.expand (p ^ h) hq
        (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA))) = 0 := by
    rw [map_sub, map_pow, MvPowerSeries.map_expand, h1, ← MvPowerSeries.map_expand,
      MvPowerSeries.map_iterateFrobenius_expand p hpr.ne_zero, sub_self]
  have hcoeffI : ∀ d, MvPowerSeries.coeff d ((liftO A hA) ^ (p ^ h) - MvPowerSeries.expand (p ^ h) hq
      (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA))) ∈ Ideal.span {((p : ℕ) : unitBall K)} := by
    intro d
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← MvPowerSeries.coeff_map, hmain, map_zero]
  have h2 : MvPowerSeries.map (unitBall K).subtype (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA))
      = MvPowerSeries.map σ A := by
    ext d
    first
      | rfl
      | (simp only [MvPowerSeries.coeff_map]; rfl)
  have hsub : MvPowerSeries.map (unitBall K).subtype ((liftO A hA) ^ (p ^ h)
      - MvPowerSeries.expand (p ^ h) hq (MvPowerSeries.map (sigmaO hσ hp) (liftO A hA)))
      = A ^ (p ^ h) - MvPowerSeries.expand (p ^ h) (pow_ne_zero h hpr.ne_zero) (MvPowerSeries.map σ A) := by
    rw [map_sub, map_pow, MvPowerSeries.map_expand, h2, map_liftO]
  intro d
  rw [← hsub, MvPowerSeries.coeff_map]
  exact norm_le_of_mem_span (p := p) _ (hcoeffI d)

end Formalism.LT.FrobP

namespace Formalism.LT

open Formalism.G

theorem FrobCongr_valid : Formalism.LT.FrobCongr.{u, v} := by
  intro K _ _ _ p q hq σ hset ι A hA
  obtain ⟨hpr, ⟨h, _, rfl⟩, hp, hσ⟩ := hset
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
  exact FrobP.main p h hpr σ hp0 hp hσ A hA

end Formalism.LT
