import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjective
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIff
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_into_de_rham_injective : GlobalTheory.CovTop.Hypotheses2 → ∀ (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (H : T.Modules) (e : ∀ (V : T.Opens) (hV : IsAffineOpen V),
        Γ(H, V) ≃ₗ[Γ(T, V)] GlobalTheory.DeRham.primDR (GlobalTheory.DeRhamSheaf.onAff A hV)),
      GlobalTheory.HodgeSeqSheaf.IsDRTriv A H e →
      ∃ i : GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A ⟶ H, ∀ (V : T.Opens) (hV : IsAffineOpen V),
        Function.Injective (GlobalTheory.QCoh.appLinear i V) ∧
        LinearMap.range ((e V hV).toLinearMap ∘ₗ GlobalTheory.QCoh.appLinear i V) =
          GlobalTheory.DeRham.PrimitiveSubmodule (GlobalTheory.DeRhamSheaf.onAff A hV) ∧
        ∃ N : Submodule Γ(T, V) Γ(H, V), IsCompl (LinearMap.range (GlobalTheory.QCoh.appLinear i V)) N := by
  first | exact @GlobalTheory.HodgeSub.main | exact GlobalTheory.HodgeSub.main | (intros; apply GlobalTheory.HodgeSub.main <;> assumption)
