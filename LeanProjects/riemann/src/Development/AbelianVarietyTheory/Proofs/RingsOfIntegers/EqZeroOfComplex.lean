import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IndepPts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.CoverRoot

theorem eq_zero_of_complex {K : Type} [Field K] (σ : K →+* ℂ) (p : TRing K) (r : p.R)
    (h : ∀ χ : p.R →ₐ[K] CAt σ, χ r = 0) : r = 0 := by
  refine ReciprocityTheory.ChartRestriction.G.TB.detAlg_holds K p.n p.I p.rad r fun L _ _ _ ψ => ?_
  letI : Algebra K ℂ := σ.toAlgebra
  let e : L →ₐ[K] ℂ := IsAlgClosed.lift
  have h2 : e (ψ r) = 0 := h (e.comp ψ)
  exact (map_eq_zero_iff e e.injective).mp h2

theorem value_pow_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Cls : Type) [CommGroup Cls] [Finite Cls] (δ : Cls →* d.c₂.Fˣ) (gdet : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom) → Cls), CMP Xo c d _ Cls δ gdet false → ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ ^ m₀ = 1 := by
  intro E _ _ _ H Dw l Xo c n d Cls _ _ δ gdet h
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hWD := (GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂).2.2.1
  have hnat := h.1.1
  refine ⟨Nat.card Cls, Nat.card_pos, fun k _ _ y₂ => ?_⟩
  obtain ⟨p, φ, y', hy⟩ := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂ k y₂
  have key : d.cδ p y' ^ Nat.card Cls - 1 = 0 := by
    refine eq_zero_of_complex d.c₂.F.val.toRingHom p _ fun χ => ?_
    obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw d.l₂ d.Xo₂ d.c₂ _ _ χ y'
    have e1 : evR d.Xo₂ d.c₂ d.cδ z = χ (d.cδ p y') :=
      ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of _ _ hWD d.cδ hnat p χ y' z hz
    have e2 := h.2 z
    rw [map_sub, map_pow, map_one, ← e1, e2, ← map_pow, if_neg (by simp), ← Units.val_pow_eq_pow_val, ← map_pow,
      pow_card_eq_one', map_one, Units.val_one, map_one, sub_self]
  have e3 : evR d.Xo₂ d.c₂ d.cδ y₂ = φ (d.cδ p y') :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of _ _ hWD d.cδ hnat p φ y' y₂ hy
  rw [e3, ← map_pow, sub_eq_zero.mp key, map_one]

end GlobalTheory.CoverRoot
