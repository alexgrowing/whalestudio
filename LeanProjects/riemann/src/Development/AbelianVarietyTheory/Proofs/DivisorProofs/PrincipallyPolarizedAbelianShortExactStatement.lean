import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarizedAbelianShortExact
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principally_polarized_abelian_short_exact : GlobalTheory.CovTop.HypothesesXH → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.PoincareDeRhamDuality →
  ∀ (p : ℕ) [Fact p.Prime] (T : Scheme.{0}) [Algebra (ZMod p) Γ(T, ⊤)],
    GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.IsProjSurface (ZMod p) T →
    ∀ (A : Over T) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      (∃ c, GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A c) →
      ∃ (S₁ S₂ : ShortComplex T.Modules), S₁.ShortExact ∧ S₂.ShortExact ∧ GlobalTheory.VB.IsVB S₁.X₂ (2 * g) ∧
        Nonempty (S₁.X₂ ≅ S₂.X₂) ∧ Nonempty (S₁.X₁ ≅ GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A) ∧
        Nonempty (S₁.X₃ ≅ GlobalTheory.VB.dual (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A)) ∧
        Nonempty (S₂.X₁ ≅ (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).obj
          (GlobalTheory.VB.dual (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A))) ∧
        Nonempty (S₂.X₃ ≅ (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).obj
          (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A)) := by
  first | exact @GlobalTheory.TwoFiltrations.main | exact GlobalTheory.TwoFiltrations.main | (intros; apply GlobalTheory.TwoFiltrations.main <;> assumption)
