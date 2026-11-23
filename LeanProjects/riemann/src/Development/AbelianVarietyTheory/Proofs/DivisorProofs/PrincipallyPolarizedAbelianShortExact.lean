import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOfBijectiveLiftSemi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHodgeShortExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHodgeFiltrationExistsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.TwoFiltrations

theorem main : GlobalTheory.CovTop.HypothesesXH → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.PoincareDeRhamDuality →
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
  intro hX hP hD p _ T _ _ A _ g hA hg hc
  obtain ⟨H, hH⟩ := GlobalTheory.DeRhamSheaf.exists_isDeRhamSheaf hP.p5 T A g hA hg
  have hV := GlobalTheory.DeRhamSheaf.VB.isVB_of_isDeRhamSheaf hP.p5 T A g hA hg H hH
  obtain ⟨S₁, h₁, ⟨e₁⟩, ⟨a₁⟩, ⟨b₁⟩⟩ := GlobalTheory.T.de_rham_hodge_short_exact hX hP hD T A g hA hg hc H hH
  obtain ⟨S₂, h₂, ⟨e₂⟩, ⟨a₂⟩, ⟨b₂⟩⟩ :=
    GlobalTheory.T.de_rham_conjugate_filtration_exists hX.dual hX.cube hX.conj hP hD p T A g hA hg hc H hH
  exact ⟨S₁, S₂, h₁, h₂, hV.of_iso e₁.symm, ⟨e₁ ≪≫ e₂.symm⟩, ⟨a₁⟩, ⟨b₁⟩, ⟨a₂⟩, ⟨b₂⟩⟩

end GlobalTheory.TwoFiltrations
