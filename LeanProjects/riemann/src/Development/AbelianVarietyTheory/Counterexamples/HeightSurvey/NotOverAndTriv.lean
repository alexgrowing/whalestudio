import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

noncomputable section

namespace GlobalTheory.Height.OrderTieGuards

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 Formalism.L2.Pj

section Unit

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  {v : AddValuation Ω (WithTop ℤ)} {la : HeightOneSpectrum (𝓞 K)}

omit [NumberField K] in

theorem nonneg_int (v : AddValuation Ω (WithTop ℤ)) (a : 𝓞 K) : 0 ≤ v (algebraMap K Ω (a : K)) := by
  have h : IsIntegral ℤ (algebraMap K Ω (a : K)) := map_isIntegral_int (algebraMap K Ω) a.isIntegral_coe
  have h2 : IsIntegral (vRing v) (algebraMap K Ω (a : K)) := h.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := vRing v) (K := Ω)).1 h2
  rw [← hy]
  exact y.2

theorem zero_of_notMem (ho : IsOver (K := K) v la) {a : 𝓞 K} (ha : a ∉ la.asIdeal) :
    v (algebraMap K Ω (a : K)) = 0 :=
  le_antisymm (not_lt.1 fun h => ha ((ho a).1 h)) (nonneg_int v a)

theorem zero_of_unit (ho : IsOver (K := K) v la) {u : K} (hu : la.valuation K u = 1) :
    v (algebraMap K Ω u) = 0 := by
  obtain ⟨n, d, hnd⟩ := la.exists_primeCompl_mul_eq_of_integer u hu.le
  have hd : la.valuation K (algebraMap (𝓞 K) K d) = 1 := (la.valuation_eq_one_iff_notMem).2 d.2
  have hn : la.valuation K (algebraMap (𝓞 K) K n) = 1 := by rw [← hnd, map_mul, hu, hd, one_mul]
  have h1 := zero_of_notMem ho ((la.valuation_eq_one_iff_notMem).1 hn)
  have h2 := zero_of_notMem ho (a := d) d.2
  have h3 : algebraMap K Ω u * algebraMap K Ω ((d : 𝓞 K) : K) = algebraMap K Ω ((n : 𝓞 K) : K) := by
    rw [← map_mul]; exact congrArg _ hnd
  have h4 := congrArg v h3
  rwa [AddValuation.map_mul, h1, h2, add_zero] at h4

theorem v_zpow (hv : IsNormDiscrete v) {x : Ω} (hx : x ≠ 0) {m : ℤ} (hm : v x = m) (k : ℤ) :
    v (x ^ k) = ((k * m : ℤ) : WithTop ℤ) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one₀ hx, AddValuation.map_mul, ih, hm, ← WithTop.coe_add]; congr 1; ring
  | pred k ih =>
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (hv.1 _ (zpow_ne_zero (-(k : ℤ) - 1) hx))
    have e : x ^ (-(k : ℤ) - 1) * x = x ^ (-(k : ℤ)) := by rw [← zpow_add_one₀ hx]; congr 1; ring
    have h := congrArg v e
    rw [AddValuation.map_mul, ih, hm, ← hs, ← WithTop.coe_add, WithTop.coe_inj] at h
    rw [← hs, WithTop.coe_inj]; linarith

theorem exists_mul (hv : IsNormDiscrete v) (ho : IsOver (K := K) v la) :
    ∃ m : ℤ, 0 < m ∧ (∃ p ∈ la.asIdeal, p ≠ 0 ∧ vLa la (p : K) = 1) ∧
      ∀ a : K, a ≠ 0 → v (algebraMap K Ω a) = ((m * vLa la a : ℤ) : WithTop ℤ) := by
  obtain ⟨p, hp⟩ := la.intValuation_exists_uniformizer
  have hpK : la.valuation K (p : K) = WithZero.exp (-1 : ℤ) := by
    rw [← hp]; exact HeightOneSpectrum.valuation_of_algebraMap la p
  have hp0 : (p : K) ≠ 0 := by
    intro h; rw [h, map_zero] at hpK; exact WithZero.exp_ne_zero hpK.symm
  have hpm : p ∈ la.asIdeal := by
    rw [← la.intValuation_lt_one_iff_mem, hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hx : algebraMap K Ω (p : K) ≠ 0 := (map_ne_zero _).2 hp0
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (hv.1 _ hx)
  have hm0 : 0 < m := by
    have := (ho p).2 hpm
    rw [← hm] at this; exact_mod_cast this
  refine ⟨m, hm0, ⟨p, hpm, fun h => hp0 (by simp [h]), by simp [vLa, hpK]⟩, fun a ha => ?_⟩
  have hva : la.valuation K a ≠ 0 := by simpa using ha
  have hu : la.valuation K (a / (p : K) ^ vLa la a) = 1 := by
    rw [map_div₀, map_zpow₀, hpK, ← WithZero.exp_zsmul, div_eq_one_iff_eq WithZero.exp_ne_zero]
    simp [vLa, WithZero.exp_log hva]
  have e : algebraMap K Ω a = algebraMap K Ω (a / (p : K) ^ vLa la a) * algebraMap K Ω (p : K) ^ vLa la a := by
    rw [← map_zpow₀ (algebraMap K Ω), ← map_mul, div_mul_cancel₀ _ (zpow_ne_zero _ hp0)]
  rw [congrArg v e, AddValuation.map_mul, zero_of_unit ho hu, zero_add, v_zpow hv hx hm.symm, mul_comm]

theorem restrict_eq (hv : IsNormDiscrete v) (ho : IsOver (K := K) v la) :
    0 < ramIdx (K := K) v la ∧
      ∀ a : K, a ≠ 0 → v (algebraMap K Ω a) = ((ramIdx (K := K) v la * vLa la a : ℤ) : WithTop ℤ) := by
  obtain ⟨m, hm, ⟨p, hp, hp0, hp1⟩, h⟩ := exists_mul hv ho
  have : ramIdx (K := K) v la = m := by
    refine IsLeast.csInf_eq ⟨⟨p, hp, hp0, ?_⟩, ?_⟩
    · rw [h _ (by exact_mod_cast hp0), hp1, mul_one]
    · rintro n ⟨a, ha, ha0, hn⟩
      have h1 := (ho a).2 ha
      rw [h _ (by exact_mod_cast ha0)] at hn h1
      have h2 : m * vLa la (a : K) = n := by exact_mod_cast hn
      have h3 : 0 < m * vLa la (a : K) := by exact_mod_cast h1
      have h4 : 0 < vLa la (a : K) := (mul_pos_iff_of_pos_left hm).1 h3
      nlinarith
  rw [this]; exact ⟨hm, h⟩

end Unit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def Clause (h : GenFrEx Xo c) (Z : Comp Xo c) (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) (e : ℤ)
    (val : Rul Xo c → EReal) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
    (((ordC δ v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) = ((e : ℝ) : EReal) * val f

variable {h : GenFrEx Xo c} {Z : Comp Xo c} {δ δ' : Ix Dw → ℤ} {v : AddValuation (Om Z) (WithTop ℤ)} {e : ℤ}
  {val : Rul Xo c → EReal}

end GlobalTheory.Height.OrderTieGuards
