import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHodgeFiltrationExists
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_conjugate_filtration_exists : GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.ConjugateFiltration →
    GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.PoincareDeRhamDuality → ∀ (p : ℕ) [Fact p.Prime] (T : Scheme.{0})
    [Algebra (ZMod p) Γ(T, ⊤)] (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∃ c, GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A c) →
    ∀ H : T.Modules, GlobalTheory.DeRhamSheaf.IsDeRhamSheaf A H →
      ∃ S : ShortComplex T.Modules, S.ShortExact ∧ Nonempty (S.X₂ ≅ H) ∧
        Nonempty (S.X₁ ≅ (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).obj
          (GlobalTheory.VB.dual (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A))) ∧
        Nonempty (S.X₃ ≅ (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).obj
          (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A)) := by
  first | exact @GlobalTheory.ConjSeq.conjugate_sequence | exact GlobalTheory.ConjSeq.conjugate_sequence | (intros; apply GlobalTheory.ConjSeq.conjugate_sequence <;> assumption)
