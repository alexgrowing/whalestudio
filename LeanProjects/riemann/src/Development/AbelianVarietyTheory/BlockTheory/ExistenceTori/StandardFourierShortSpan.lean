import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ShortRuleRepresentationChange

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {nab : NabV Xo c}

def RankRange (Dw : Datum H) (n : ℕ) : Prop :=
  3 ≤ Dw.p + Dw.q ∧ 8 * (Module.finrank ℚ E / 2) * (Dw.p + Dw.q) + 4 ≤ n

def SpanRange (Dw : Datum H) (l : Level H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  l.A = 1 ∧ Dom a n ∧ RankRange Dw n

section Span

variable (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ)
  (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))

def shortSpanK (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule c.F (Rul Xo c) :=
  Submodule.span c.F (shortGen Δ hK nV a n)

def CuspLeSpan : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), SpanRange Dw l a n → cusp a n ≤ shortSpanK Δ hK nV a n

def CuspEqSpan : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), SpanRange Dw l a n → OnePos Dw a → cusp a n = shortSpanK Δ hK nV a n

def GenNeZero : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), SpanRange Dw l a n → cusp a n ≠ ⊥ → ∃ f ∈ shortGen Δ hK nV a n, f ≠ 0

end Span

def SpanAtEmb (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ) {σ : c.F →+* ℂ} {r : ℕ}
    (U : Formalism.L2.PjFree.Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), SpanRange Dw l a n →
    ∀ Q ∈ Formalism.L2.PjFree.holSub U.X (Formalism.L2.PjFree.laU U a n),
      ∃ Q' ∈ Submodule.span ℂ (Formalism.L2.PjFree.rdU U '' shortGen Δ hK nV a n),
        ∀ k, ∀ x ∈ (U.X k).dom, Q k x = Q' k x

section Std

variable (Xo c nab)

def IsTranslateFamily {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) (w : (Fin n → NamedCl Dw l) → Rul Xo c) : Prop :=
  ∀ x : Fin n → Dw.La, IsThRule Xo c nab x P (w fun b => Submodule.Quotient.mk (x b))

def fourierComb {n : ℕ} (x₀ : Fin n → ConjCl Dw l) (w : (Fin n → NamedCl Dw l) → Rul Xo c) : Rul Xo c :=
  fun p y => ∑ t ∈ levelIndex Dw l n, algebraMap c.F p.R (indCoeff c x₀ t) * w t p y

def StdFourier : Prop :=
  ∀ (n N : ℕ) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F),
    IsSeriesData (DeltaDatum.triv Xo c nab) (Lat.std E n) N β a P →
    (∃ w, IsTranslateFamily Xo c nab P w) ∧
    ∀ w, IsTranslateFamily Xo c nab P w → ∀ f : Rul Xo c,
      IsShortRule (DeltaDatum.triv Xo c nab) (Lat.std E n) N β x₀ a P f ↔
        f = fun p y => algebraMap c.F p.R β⁻¹ * fourierComb Xo c x₀ w p y

def StdFourierUnit : Prop :=
  ∀ (n N : ℕ) (β : c.F), (Lat.std E n).Admissible l.M N → IsBeLat Dw c (Lat.std E n) β →
    ∃ u : (𝓞 c.F)ˣ, ∀ (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F),
      P ∈ harmLat Dw c a (Lat.std E n) →
      (∃ w, IsTranslateFamily Xo c nab P w) ∧
      ∀ w, IsTranslateFamily Xo c nab P w → ∀ f : Rul Xo c,
        IsShortRule (DeltaDatum.triv Xo c nab) (Lat.std E n) N β x₀ a P f ↔
          f = fun p y => algebraMap c.F p.R ((u : 𝓞 c.F) : c.F) * fourierComb Xo c x₀ w p y

end Std

section Canonical

variable (Xo c)

def IsUnfAll {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) : Prop :=
  ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)

def SpanCanonical : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
    ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), IsUnfAll Xo c U →
    ∀ (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ),
      CuspLeSpan Δ hK nV (Formalism.L2.PjFree.cusp Xo c U) ∧ CuspEqSpan Δ hK nV (Formalism.L2.PjFree.cusp Xo c U)

def NeZeroCanonical : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
    ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), IsUnfAll Xo c U →
    ∀ (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ), GenNeZero Δ hK nV (Formalism.L2.PjFree.cusp Xo c U)

def StdCanonical : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → StdFourier Xo c nab

def SpanAtEmbCanonical : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
    ∀ (σ : c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb c σ → ∀ (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r),
    Formalism.L2.PjFree.IsUnf U → ∀ (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ), SpanAtEmb Δ hK nV U

def ShortSpanClaims : Prop := SpanCanonical Xo c ∧ NeZeroCanonical Xo c ∧ StdCanonical Xo c

end Canonical

section Basic₂

variable {Δ : DeltaDatum Xo c nab} {hK : ReflexLe Dw c} {nV : ℕ}
  {cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)}

theorem CuspLeSpan.genNeZero (h : CuspLeSpan Δ hK nV cusp) : GenNeZero Δ hK nV cusp := by
  intro a n hr hne
  by_contra h0
  push Not at h0
  exact hne (le_bot_iff.1 ((h a n hr).trans (Submodule.span_eq_bot.2 h0).le))

theorem CuspLeSpan.cuspEqSpan (h : CuspLeSpan Δ hK nV cusp) (h' : ShortInCusp Δ hK nV cusp) :
    CuspEqSpan Δ hK nV cusp :=
  fun a n hr hp => le_antisymm (h a n hr) (Submodule.span_le.2 (h' a n hr.2.1 hp))

theorem SpanCanonical.neZero (h : SpanCanonical Xo c) : NeZeroCanonical Xo c :=
  fun nab hn r U hU Δ hK nV => (h nab hn r U hU Δ hK nV).1.genNeZero

theorem exists_spanRange (hr : 3 ≤ Dw.p + Dw.q) (hA : l.A = 1) : ∃ a n, SpanRange Dw l a n ∧ OnePos Dw a := by
  obtain ⟨τ, hτ⟩ := exists_inPsi H
  refine ⟨fun _ => 1, 8 * (Module.finrank ℚ E / 2) * (Dw.p + Dw.q) + 4,
    ⟨hA, ⟨fun _ => antitone_const, ⟨4 * (Module.finrank ℚ E / 2) * (Dw.p + Dw.q) + 2, by ring⟩⟩, hr, le_rfl⟩,
    τ, hτ, fun _ => le_rfl⟩

theorem StdFourier.unit (h : StdFourier Xo c nab) : StdFourierUnit Xo c nab := by
  intro n N β hN hβ
  obtain ⟨b, hb, hs⟩ := hβ.1
  have hu : IsUnit b := by
    rw [latIdeal_std] at hs
    rw [← Ideal.span_singleton_eq_top, hs]
    simp only [reflexIdeal, Ideal.map_top]
    simp [← Ideal.one_eq_top]
  obtain ⟨u, rfl⟩ := hu
  refine ⟨u⁻¹, fun x₀ a P hP => ?_⟩
  have e : (((u⁻¹ : (𝓞 c.F)ˣ) : 𝓞 c.F) : c.F) = β⁻¹ := by
    rw [← hb]
    refine eq_inv_of_mul_eq_one_left ?_
    exact (map_mul (algebraMap (𝓞 c.F) c.F) _ _).symm.trans (by rw [Units.inv_mul, map_one])
  rw [e]
  exact h n N β x₀ a P ⟨std_mem_reps _ n 1, hN, hβ, hP⟩

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan
