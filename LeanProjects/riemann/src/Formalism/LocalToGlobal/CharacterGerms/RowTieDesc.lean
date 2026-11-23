import Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

section Chart

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def chartDerivativeCoefficient (C3 : IntChart T io y) (k n : ℕ) (f : PS T.Fr n (chD C3.ch)) (P : MvPolynomial (LtN Dw n) T.Fr) : T.Fr :=
  nabValN (a3B C3) T.Fr (a3h C3) H.w0 k f (fun ℓ => ℓ.2.2) (fun ℓ => chartUnitVectors C3 ⟨ℓ.1, ℓ.2.1⟩) P

theorem nuLocC_le_nval (C3 : IntChart T io y) (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (P : MvPolynomial (LtN Dw n) T.Fr) (hP : P ∈ FFV (Dw := Dw) T a n) (f : PS T.Fr n (chD C3.ch)) (hf : IsIntPS T f) :
    nuLocC C3 e k a n ≤ nval T.V e (chartDerivativeCoefficient C3 k n f P) := by
  unfold nuLocC chartDerivativeCoefficient
  exact le_trans (iInf₂_le P hP) (iInf₂_le f hf)

end Chart

section Val

variable {C : Type} [Field C] {V : VF C}

theorem le_v_sum (x : WithTop ℝ) {m : ℕ} (z : Fin m → C) (h : ∀ i, x ≤ V.v (z i)) : x ≤ V.v (∑ i, z i) := by
  refine Finset.sum_induction z (fun w => x ≤ V.v w)
    (fun a b ha hb => le_trans (le_min ha hb) (V.v.map_add a b)) ?_ (fun i _ => h i)
  rw [AddValuation.map_zero]
  exact le_top

end Val

variable (Xo c)

def NabMapSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C)
    (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : PS T.Fr n (chD C3.ch)) (P : MvPolynomial (LtN Dw n) T.Fr),
      Y.nab (chartLetterSystem C3 V ι a) n (MvPowerSeries.map ι f) (MvPolynomial.map ι P) = ι (chartDerivativeCoefficient C3 k n f P)

def DescSpanSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ P ∈ (chartLetterSystem C3 V ι a).FF n, ∀ f : PS C n (chD C3.ch), IntS V f →
      ∃ (m : ℕ) (r : Fin m → C) (Pi : Fin m → MvPolynomial (LtN Dw n) T.Fr) (fi : Fin m → PS T.Fr n (chD C3.ch)),
        (∀ i, V.Ge 0 (r i)) ∧ (∀ i, Pi i ∈ FFV (Dw := Dw) T a n) ∧ (∀ i, IsIntPS T (fi i)) ∧
        Y.nab (chartLetterSystem C3 V ι a) n f P =
          ∑ i, r i * Y.nab (chartLetterSystem C3 V ι a) n (MvPowerSeries.map ι (fi i)) (MvPolynomial.map ι (Pi i))

def NvalEqSt : Prop :=
  ∀ (T : CDVR) (C : Type) [Field C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ x : T.Fr, (WithBot.some (V.v (ι x)) : WithBot (WithTop ℝ)) = nval T.V (eOf T V) x

variable {Xo c}

theorem descent_of (h1 : NabMapSt Xo c) (h2 : DescSpanSt Xo c) (h3 : NvalEqSt) : DescentSt Xo c := by
  intro T io y C3 C _ _ V ι hι k Y hY a n
  unfold FBChart.nuPlE
  refine le_iInf₂ fun x hx => ?_
  obtain ⟨P, hP, f, hf, rfl⟩ := hx
  obtain ⟨m, r, Pi, fi, hr, hPi, hfi, heq⟩ := h2 T io y C3 C V ι hι k Y hY a n P hP f hf
  have hz : ∀ i, nuLocC C3 (eOf T V) k a n ≤ (WithBot.some (V.v (Y.nab (chartLetterSystem C3 V ι a) n
      (MvPowerSeries.map ι (fi i)) (MvPolynomial.map ι (Pi i)))) : WithBot (WithTop ℝ)) := by
    intro i
    rw [h1 T io y C3 C V ι k Y hY a n (fi i) (Pi i), h3 T C V ι hι]
    exact nuLocC_le_nval C3 (eOf T V) k a n (Pi i) (hPi i) (fi i) (hfi i)
  rw [heq]
  generalize nuLocC C3 (eOf T V) k a n = ν at hz ⊢
  rcases ν with _ | w
  · exact bot_le
  · refine WithBot.coe_le_coe.mpr (le_v_sum w _ fun i => ?_)
    have hzi := WithBot.coe_le_coe.mp (hz i)
    rw [AddValuation.map_mul]
    calc w = 0 + w := (zero_add w).symm
      _ ≤ V.v (r i) + _ := add_le_add (hr i) hzi

end Formalism.L2.FormalSeriesBounds
