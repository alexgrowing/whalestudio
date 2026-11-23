import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RowChartCounterexample

open Formalism.L2.FormalSeriesBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {C : Type} [Field C]

theorem embOK_vl_ne {T : CDVR} {V : VF C} {ι : T.Fr →+* C} (h : EmbOK T V ι) :
    vV T.V ((V.l : ℕ) : T.Fr) ≠ 0 := by
  intro h0
  have hl : ((V.l : ℕ) : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 V.l_prime.ne_zero
  have := h _ hl
  rw [map_natCast, V.v_l, h0] at this
  simp at this

theorem vV_nonneg (T : CDVR) (a : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr a) := by
  unfold vV
  by_cases ha : valV T.V (algebraMap T.V T.Fr a) = 0
  · simp [ha]
  have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 :=
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
  have := (WithZero.log_le_log ha one_ne_zero).2 h1
  simp at this
  omega

theorem embOK_eOf {T : CDVR} {V : VF C} {ι : T.Fr →+* C} (h : EmbOK T V ι) :
    0 < eOf T V ∧ ((eOf T V : ℕ) : ℤ) = vV T.V ((V.l : ℕ) : T.Fr) := by
  have h0 : 0 ≤ vV T.V ((V.l : ℕ) : T.Fr) := by
    have := vV_nonneg T (V.l : T.V)
    rwa [map_natCast] at this
  have h1 := embOK_vl_ne h
  unfold eOf
  omega

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

variable {l : Level H} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {ι : T.Fr →+* C} {V : VF C}
variable {Orb : Type} {d : ℕ}

theorem em_int_holds (τ : E →+* ℂ) (x : 𝓞 E) (h : EmbOK T V ι) : V.Ge 0 (emA3 io ι τ x) := by
  have hx : IsIntegral ℤ (io (embK c τ x)) :=
    (Algebra.IsIntegral.isIntegral (R := ℤ) x).map_of_comp_eq (RingHom.id ℤ) (io.comp (embK c τ)) (Subsingleton.elim _ _)
  have hx' : IsIntegral T.V (io (embK c τ x)) := hx.tower_top
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (K := T.Fr)).1 hx'
  show V.Ge 0 (ι (io (embK c τ x)))
  rw [← hz]
  by_cases h0 : algebraMap T.V T.Fr z = 0
  · rw [h0, map_zero]; exact VF.Ge.zero 0
  unfold VF.Ge
  rw [h _ h0, ← (embOK_eOf h).2]
  have := vV_nonneg T z
  exact WithTop.coe_le_coe.2 (div_nonneg (by exact_mod_cast this) (by positivity))

open Classical in

def selfVF (T : CDVR) (p : ℕ) (hp : p.Prime) (h : 0 < vV T.V ((p : ℕ) : T.Fr)) : VF T.Fr where
  v := AddValuation.of
    (fun x => if x = 0 then ⊤ else (((vV T.V x : ℝ) / (vV T.V ((p : ℕ) : T.Fr) : ℝ) : ℝ) : WithTop ℝ))
    (by simp) (by simp [vV])
    (fun x y => by
      by_cases hxy : x + y = 0
      · simp [hxy]
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      simp only [hx, hy, hxy, if_false]
      have hp0 : (0 : ℝ) ≤ (vV T.V ((p : ℕ) : T.Fr) : ℝ) := by exact_mod_cast h.le
      rcases min_le_iff.1 (min_le_vV_add (V := T.V) hx hy hxy) with h' | h'
      · exact min_le_iff.2 (Or.inl (WithTop.coe_le_coe.2 (div_le_div_of_nonneg_right (by exact_mod_cast h') hp0)))
      · exact min_le_iff.2 (Or.inr (WithTop.coe_le_coe.2 (div_le_div_of_nonneg_right (by exact_mod_cast h') hp0))))
    (fun x y => by
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      simp only [hx, hy, mul_ne_zero hx hy, if_false]
      rw [vV_mul hx hy, Int.cast_add, add_div, WithTop.coe_add])
  l := p
  l_prime := hp
  v_l := by
    have h1 : ((p : ℕ) : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have h2 : (vV T.V ((p : ℕ) : T.Fr) : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    rw [AddValuation.of_apply, if_neg h1, div_self h2]
    rfl

def padicT (p : ℕ) [Fact p.Prime] : CDVR where
  V := ℤ_[p]

end GlobalTheory.RowChartCounterexample
