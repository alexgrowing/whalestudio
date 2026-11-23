import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPullbackDeRhamMapExists
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_pullback_de_rham_map_exists : GlobalTheory.CovTop.Hypotheses2 → ∀ (p : ℕ) [Fact p.Prime] {T : Scheme.{0}} [Algebra (ZMod p) Γ(T, ⊤)] (A : Over T) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∃ Ψ : (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).obj H ⟶ H, ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      e V hV ((Ψ).app V (GlobalTheory.QCoh.pullbackSections (GlobalTheory.VB.frob T p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))) H
        (le_refl V) s)) =
      GlobalTheory.ConjSeq.frobDR p Γ(T, V) (GlobalTheory.SS.FrobField.cast_zero (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) V)
        (onAff A hV) (e V hV s) := by
  first | exact @GlobalTheory.LinFrob.exists_linFrob | exact GlobalTheory.LinFrob.exists_linFrob | (intros; apply GlobalTheory.LinFrob.exists_linFrob <;> assumption)
