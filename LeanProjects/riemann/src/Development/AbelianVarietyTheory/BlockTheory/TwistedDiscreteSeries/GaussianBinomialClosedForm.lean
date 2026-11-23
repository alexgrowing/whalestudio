import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables

open MeasureTheory Formalism.UG GlobalTheory.Doubling GlobalTheory.PRep

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

abbrev GD (σ : L →+* L) (n : ℕ) : Subgroup (GL (Fin (n + n)) L) := UJ σ (dblGram finSumFinEquiv (antiJ L n))

def KD (σ : L →+* L) (n : ℕ) : Subgroup (GD σ n) := (intPts (intL L).subtype (GD σ n)).subgroupOf (GD σ n)

abbrev PD (σ : L →+* L) (n : ℕ) : Subgroup (GD σ n) := siegelOf finSumFinEquiv (GD σ n).subtype

abbrev aD (σ : L →+* L) (n : ℕ) : PD σ n →* Lˣ := aOf finSumFinEquiv (GD σ n).subtype

def io1 (σ : L →+* L) (n : ℕ) (g : GU σ n) : GD σ n := ioU σ finSumFinEquiv (J := antiJ L n) rfl (g, 1)

def IsUnr (χ : Lˣ →* ℂˣ) : Prop := ∀ u : Lˣ, Valued.v (u : L) = 1 → χ u = 1

def secVal (q : ℕ) (χ : Lˣ →* ℂˣ) (t : ℂ) (a : Lˣ) : ℂ := χ a * (q : ℂ) ^ (-(2 * (ordL (a : L) : ℂ) * t))

def IsSphSec (σ : L →+* L) (q n : ℕ) (χ : Lˣ →* ℂˣ) (s : ℂ) (Φ : GD σ n → ℂ) : Prop :=
  ∀ (p : PD σ n), ∀ k ∈ KD σ n, Φ (p * k) = secVal q χ (s + (n : ℂ) / 2) (aD σ n p)

def IsZonal {σ : L →+* L} {n : ℕ} (ϖ : L) (q : ℕ) (α : Fin (n / 2) → ℂˣ) (w : GU σ n → ℂ) : Prop :=
  IsBiInv (KU σ n) w ∧ w 1 = 1 ∧
    ∀ h ∈ Hecke ℂ (KU σ n), hAct (KU σ n) h w 1 = SatU ϖ q h fun i => (α i : ℂ)

def varX (q n : ℕ) (ε s : ℂ) : ℂ := ε * (q : ℂ) ^ (-(2 * s + n))

def varY (q : ℕ) (ε s : ℂ) : ℂ := ε * (q : ℂ) ^ (-(2 * s + 1))

def Domain {r : ℕ} (y : ℂ) (α : Fin r → ℂˣ) : Prop :=
  ‖y‖ < 1 ∧ ∀ i, ‖y‖ * ‖(α i : ℂ)‖ < 1 ∧ ‖y‖ * ‖(α i : ℂ)‖⁻¹ < 1

def closedForm (q n : ℕ) (X y : ℂ) (α : Fin (n / 2) → ℂˣ) : ℂ :=
  (∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * X)) *
    (∏ i, (1 - y * (α i : ℂ))⁻¹ * (1 - y / (α i : ℂ))⁻¹) * (if Odd n then (1 - y)⁻¹ else 1)

def stdL (q n : ℕ) (α : Fin (n / 2) → ℂˣ) (ε z : ℂ) : ℂ :=
  GlobalTheory.LFun.eulerFac (GlobalTheory.LGrp.bcParam n α) (ε * ((q ^ 2 : ℕ) : ℂ) ^ (-z))

def etaL (q k : ℕ) (z : ℂ) : ℂ := (1 - (-1) ^ k * (q : ℂ) ^ (-z))⁻¹

def dFac (q n m : ℕ) (s : ℂ) : ℂ := ∏ i ∈ Finset.range n, etaL q (m + i) (2 * s + n - i)

def UnramDoublingInert : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ),
    IsUnramInv (ϖ : L) σ q →
    ∀ [MeasurableSpace (GU σ n)] [BorelSpace (GU σ n)] (μ : Measure (GU σ n)) [μ.IsHaarMeasure],
    μ (KU σ n) = 1 →
    ∀ (χ : Lˣ →* ℂˣ), IsUnr χ → ∀ (s : ℂ) (Φ : GD σ n → ℂ), IsSphSec σ q n χ s Φ →
    ∀ (α : Fin (n / 2) → ℂˣ) (w : GU σ n → ℂ), IsZonal (ϖ : L) q α w →
      (Domain (varY q (χ ϖ) s) α →
        Integrable (fun g => Φ (io1 σ n g) * w g) μ ∧
        ∫ g, Φ (io1 σ n g) * w g ∂μ = closedForm q n (varX q n (χ ϖ) s) (varY q (χ ϖ) s) α ∧
        ∀ m : ℕ, (χ ϖ : ℂ) = (-1) ^ m →
          ∫ g, Φ (io1 σ n g) * w g ∂μ = stdL q n α (χ ϖ) (s + 1 / 2) / dFac q n m s) ∧
      (n ≤ 1 → Integrable (fun g => Φ (io1 σ n g) * w g) μ ∧ ∫ g, Φ (io1 σ n g) * w g ∂μ = 1)

theorem secVal_mul {q : ℕ} (hq : q ≠ 0) (χ : Lˣ →* ℂˣ) (t : ℂ) (a b : Lˣ) :
    secVal q χ t (a * b) = secVal q χ t a * secVal q χ t b := by
  have h : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  simp only [secVal, map_mul, Units.val_mul, P.fIwasawa_ordL_mul _ _ a.ne_zero b.ne_zero, Int.cast_add]
  rw [show -(2 * ((ordL (a : L) : ℂ) + (ordL (b : L) : ℂ)) * t) =
    -(2 * (ordL (a : L) : ℂ) * t) + -(2 * (ordL (b : L) : ℂ) * t) by ring, Complex.cpow_add _ _ h]
  ring

theorem secVal_unit (q : ℕ) {χ : Lˣ →* ℂˣ} (hχ : IsUnr χ) (t : ℂ) {a : Lˣ} (ha : Valued.v (a : L) = 1) :
    secVal q χ t a = 1 := by
  have : ordL (a : L) = 0 := by
    have h0 : Valued.v (a : L) ≠ 0 := by rw [ha]; exact one_ne_zero
    have h1 : WithZero.unzero h0 = 1 := WithZero.coe_injective (by rw [WithZero.coe_unzero, ha]; rfl)
    simp [ordL, h0, h1]
  simp [secVal, hχ a ha, this]

theorem v_aD_le {σ : L →+* L} {n : ℕ} (p : PD σ n) (hp : (p : GD σ n) ∈ KD σ n) : Valued.v (aD σ n p : L) ≤ 1 := by
  obtain ⟨-, x, hx⟩ := hp
  have e : ((GD σ n).subtype p).1 = x.1.map (intL L).subtype := by
    rw [show (GD σ n).subtype p = _ from hx.symm]; rfl
  rw [val_aOf, e, leviMat_map]
  exact (congrArg Valued.v ((intL L).subtype.map_det _).symm).le.trans (leviMat finSumFinEquiv x.1).det.2

theorem v_aD_eq {σ : L →+* L} {n : ℕ} (p : PD σ n) (hp : (p : GD σ n) ∈ KD σ n) : Valued.v (aD σ n p : L) = 1 := by
  have h := v_aD_le p⁻¹ (inv_mem hp)
  rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀,
    inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _)))] at h
  exact le_antisymm (v_aD_le p hp) h

theorem exists_isSphSec (σ : L →+* L) {q : ℕ} (hq : q ≠ 0) (n : ℕ) {χ : Lˣ →* ℂˣ} (hχ : IsUnr χ) (s : ℂ) :
    ∃ Φ, IsSphSec σ q n χ s Φ := by
  classical
  refine ⟨fun g => if h : ∃ p : PD σ n, ∃ k ∈ KD σ n, g = p * k then
    secVal q χ (s + (n : ℂ) / 2) (aD σ n h.choose) else 0, fun p k hk => ?_⟩
  have h : ∃ p' : PD σ n, ∃ k' ∈ KD σ n, (p : GD σ n) * k = p' * k' := ⟨p, k, hk, rfl⟩
  obtain ⟨k', hk', e⟩ := h.choose_spec
  have hm : ((p⁻¹ * h.choose : PD σ n) : GD σ n) ∈ KD σ n := by
    have : ((p⁻¹ * h.choose : PD σ n) : GD σ n) = k * k'⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
      exact e.symm
    rw [this]
    exact mul_mem hk (inv_mem hk')
  simp only [dif_pos h]
  rw [← mul_inv_cancel_left p h.choose, map_mul, secVal_mul hq, secVal_unit q hχ _ (v_aD_eq _ hm), mul_one]

theorem isZonal_of_isSatVecU {ϖ : L} {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv ϖ σ q) {V : Type} [AddCommGroup V]
    [Module ℂ V] {ρ : Representation ℂ (GU σ n) V} {x : V} {α : Fin (n / 2) → ℂˣ}
    (hx : GlobalTheory.LFun.IsSatVecU ϖ q ρ x α) (l : V →ₗ[ℂ] ℂ) (hl : ∀ k ∈ KU σ n, ∀ y, l (ρ k y) = l y) (h1 : l x = 1) :
    IsZonal ϖ q α fun g => l (ρ g x) := by
  refine ⟨fun a b g => ?_, by simpa using h1, fun h hh => ?_⟩
  · simp only [map_mul, Module.End.mul_apply, hl _ a.2, GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ b.2]
  · have e := congrArg l (hx.2.2 h hh)
    rw [map_smul, h1, smul_eq_mul, mul_one] at e
    rw [← e]
    refine Eq.trans (finsum_congr fun c => ?_)
      (l.toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec (P.isCommensurated_integral_unitary_of_unramified hU n) hh ρ x)).symm
    simp

theorem isZonal_one [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (n : ℕ) :
    ∃ α : Fin (n / 2) → ℂˣ, (∀ i, (α i : ℂ) = (q : ℂ) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ))) ∧
      IsZonal (σ := σ) ϖ q α fun _ => 1 := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hU.2.2.2.2.2.1; omega)
  refine ⟨fun i => Units.mk0 _ (zpow_ne_zero ((n : ℤ) - 1 - 2 * (i.val : ℤ)) hq), fun _ => rfl, fun _ _ _ => rfl, rfl,
    fun h hh => ?_⟩
  refine (congrFun (Final.SatakeInert L ϖ σ q n (n / 2) hU (by omega) (by omega)
    (fun i => (q : ℂ) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ))) (fun i => zpow_ne_zero _ hq) h hh
    (fun _ => 1) fun b g k _ _ => ?_) 1).trans (by simp)
  rw [mul_one, chiDeltaU]
  refine (Finset.prod_eq_one fun i _ => ?_).symm
  split_ifs
  · rw [← zpow_mul, ← zpow_add₀ hq]
    convert zpow_zero (q : ℂ) using 2
    ring
  · rfl

example (q : ℕ) (ε s : ℂ) (α : Fin (1 / 2) → ℂˣ) (h : varY q ε s ≠ 1) :
    closedForm q 1 (varX q 1 ε s) (varY q ε s) α = 1 := by
  have : varX q 1 ε s = varY q ε s := by simp [varX, varY]
  simp [closedForm, this, sub_ne_zero.2 h.symm]

end GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables

end
