import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.BarTorsionGenerators
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SplitOfFactorisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvectionEq

noncomputable section

namespace GlobalTheory.NoCommonZeroCompare

section Quadratic

structure IsQuad {R : Type} [CommRing R] (c : R →+* R) (w : R) (k : ℤ) (d : ℕ) : Prop where
  prime : d.Prime
  four : 4 * k = 1 + d
  sq : w * w = w - k
  conj : c w = 1 - w
  span : ∀ x : R, ∃ a b : ℤ, x = a + b * w
  indep : ∀ a b : ℤ, (a : R) + b * w = 0 → a = 0 ∧ b = 0

variable {R : Type} [CommRing R] {c : R →+* R} {w : R} {k : ℤ} {d : ℕ}

theorem IsQuad.cc (h : IsQuad c w k d) (x : R) : c (c x) = x := by
  obtain ⟨a, b, rfl⟩ := h.span x
  simp [h.conj]

end Quadratic

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.BarTorsionGenerators GlobalTheory.HostCompare

section Level

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

end Level

section Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

end Points

section Record

variable {D : D7}

end Record

def LongOn (P : ∀ (D : D7) (T : Top D) (j : ℕ), WeightFamilies.Wt D j → ℕ → Prop) : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (α : 𝓞 D.host.E) (q : ℕ),
    P D T j w q → D.R.r ≤ w.n → IsJetLevel T.Q.l α q → 4 * WeightAlgebra.DF w + 4 ≤ q →
    ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
      NoCommonZero (T.Q.Xo j) T.Q.c σ (gens (T.Q.Xo j) T.Q.c (T.nab j) α (wtA w) w.n)

def IsFull (D : D7) (T : Top D) (j : ℕ) (w : WeightFamilies.Wt D j) (q : ℕ) : Prop :=
  q = T.Q.l.M ∧ LastPos (T.Q.Dw j) (wtA w)

def IsRest (D : D7) (T : Top D) (j : ℕ) (w : WeightFamilies.Wt D j) (q : ℕ) : Prop :=
  q = D.host.g 0 ∨ q = D.host.g 1 ∨ ¬ LastPos (T.Q.Dw j) (wtA w)

end GlobalTheory.NoCommonZeroCompare
