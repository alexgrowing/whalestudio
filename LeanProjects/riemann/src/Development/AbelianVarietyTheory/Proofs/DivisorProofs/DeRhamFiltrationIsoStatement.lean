import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamFiltrationIso
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_filtration_iso : GlobalTheory.CovTop.Hypotheses2 → ∀ {T : Scheme.{0}} (A : Over T) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∀ F : GlobalTheory.VB.Sub H, (∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ F.sec V ↔ e V hV s ∈ PrimitiveSubmodule (onAff A hV)) →
    Nonempty (F.toMod ≅ GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A) := by
  first | exact @GlobalTheory.HodgeIso.main | exact GlobalTheory.HodgeIso.main | (intros; apply GlobalTheory.HodgeIso.main <;> assumption)
