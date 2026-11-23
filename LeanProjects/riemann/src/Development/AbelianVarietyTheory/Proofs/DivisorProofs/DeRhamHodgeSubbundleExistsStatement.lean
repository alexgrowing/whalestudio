import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHodgeSubbundleExists
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_hodge_subbundle_exists : GlobalTheory.CovTop.Hypotheses2 → ∀ (p : ℕ) [Fact p.Prime] {T : Scheme.{0}} [Algebra (ZMod p) Γ(T, ⊤)] (A : Over T) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∃ C : GlobalTheory.VB.Sub H, ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ C.sec V ↔ e V hV s ∈ GlobalTheory.ConjSeq.conjDR p Γ(T, V)
        (GlobalTheory.SS.FrobField.cast_zero (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) V) (onAff A hV) := by
  first | exact @GlobalTheory.ConjSeq.ConjSub.exists_conjSub | exact GlobalTheory.ConjSeq.ConjSub.exists_conjSub | (intros; apply GlobalTheory.ConjSeq.ConjSub.exists_conjSub <;> assumption)
