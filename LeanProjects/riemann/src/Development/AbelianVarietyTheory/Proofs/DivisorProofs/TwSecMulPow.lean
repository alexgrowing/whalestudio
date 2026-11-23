import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatTw.TwSec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c}

theorem exists_pow {G₀ : WTZ E} (s : TwSec U x Z G₀) (n : ℕ) :
    ∃ u : TwSec U x Z (n • G₀), u.lo = n • s.lo ∧ u.degLo = n * s.degLo := by
  induction n with
  | zero =>
    obtain ⟨-, -, h2, -, h3⟩ := const_spec (x := x) s.pts (1 : c.F) one_ne_zero
    refine ⟨(const x s.pts 1 one_ne_zero).copy (zero_nsmul G₀).symm, ?_, ?_⟩
    · funext w
      show (const x s.pts 1 one_ne_zero).lo w = _
      rw [h2 w]
      simp [vAdd]
    · show (const x s.pts 1 one_ne_zero).degLo = _
      rw [h3]; simp
  | succ n ih =>
    obtain ⟨u, hl, hd⟩ := ih
    refine ⟨(u.mul s).copy (succ_nsmul G₀ n).symm, ?_, ?_⟩
    · show u.lo + s.lo = _
      rw [hl, succ_nsmul]
    · show (u.mul s).degLo = _
      rw [degLo_mul, hd]; push_cast; ring

end GlobalTheory.FlatTw.TwSec

theorem GlobalTheory.FlatTw.twSec_mul_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c), (∀ (G₀ G₁ : WTZ E) (s : TwSec U x Z G₀) (t : TwSec U x Z G₁), ∃ u : TwSec U x Z (G₀ + G₁), u.sig = s.sig * t.sig ∧ u.cInf = s.cInf * t.cInf ∧ u.lo = s.lo + t.lo ∧ u.degLo = s.degLo + t.degLo) ∧ ∀ (G₀ : WTZ E) (s : TwSec U x Z G₀) (n : ℕ), ∃ u : TwSec U x Z (n • G₀), u.lo = n • s.lo ∧ u.degLo = n * s.degLo := by
  intro E _ _ _ H Dw l Xo c r U x Z
  exact ⟨fun G₀ G₁ s t => ⟨s.mul t, rfl, rfl, rfl, TwSec.degLo_mul s t⟩, fun G₀ s n => s.exists_pow n⟩
