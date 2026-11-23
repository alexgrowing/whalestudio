import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem unitC_of_finite_character : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Cls : Type) [CommGroup Cls] [Finite Cls] (δ : Cls →* d.c₂.Fˣ) (gdet : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom) → Cls), 1 ≤ Dw.p + Dw.q → CMP Xo c d _ Cls δ gdet false → UnitC d := by
  intro E _ _ _ H Dw l Xo c n d Cls _ _ δ gdet hpq hC
  have hSB := (@GlobalTheory.lawsFieldsSeparately).2.1
  have hAT := @GlobalTheory.T.framedPoint_reduced_from_testRing hSB E _ _ _ H Dw d.l₂ d.Xo₂ d.c₂
  have hW := (GlobalTheory.Frames.algebraic_laws hSB E H Dw d.l₂ d.Xo₂ d.c₂).2.2.1
  obtain ⟨hs, hv⟩ := hC
  unfold Formalism.L2.Pj.sec Formalism.L2.Pj.secW at hs
  have hN := (show _ ∧ _ from hs).1
  have hm : Nat.card Cls ≠ 0 := Nat.card_pos.ne'

  have key : ∀ (p : Formalism.L2.Pj.TRing d.c₂.F) (y₀ : FrPt d.Xo₂ d.c₂ p.R),
      (d.cδ p y₀) ^ Nat.card Cls = 1 := by
    intro p y₀
    refine sub_eq_zero.mp (Formalism.L2.Pj.eq_zero_of_cpts d.c₂.F.val.toRingHom p _ fun ψ => ?_)
    obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hSB E H Dw d.l₂ d.Xo₂ d.c₂ p.R
      (Formalism.L2.Pj.CAt d.c₂.F.val.toRingHom) ψ y₀
    have hev : Formalism.L2.Pj.evR d.Xo₂ d.c₂ d.cδ z = ψ (d.cδ p y₀) := by
      unfold Formalism.L2.Pj.evR Formalism.L2.Pj.evalAt
      split
      · next h => exact hW d.cδ hN _ _ _ _ _ _ _ _ h.choose_spec.choose_spec.choose_spec hz
      · next h => exact absurd ⟨p, ψ, y₀, hz⟩ h
    rw [map_sub, map_pow, map_one, ← hev, hv z]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one, map_one,
      sub_self]
  unfold GlobalTheory.Dict.UnitC
  intro A y
  letI := A
  obtain ⟨p, φ, y₀, hy⟩ := hAT ℂ y
  have hev : Formalism.L2.Pj.evR d.Xo₂ d.c₂ d.cδ y = φ (d.cδ p y₀) := by
    unfold Formalism.L2.Pj.evR Formalism.L2.Pj.evalAt
    split
    · next h => exact hW d.cδ hN _ _ _ _ _ _ _ _ h.choose_spec.choose_spec.choose_spec hy
    · next h => exact absurd ⟨p, φ, y₀, hy⟩ h
  rw [hev]
  exact norm_eq_one_of_pow_eq_one (by rw [← map_pow, key, map_one]) hm

end GlobalTheory.Dict
