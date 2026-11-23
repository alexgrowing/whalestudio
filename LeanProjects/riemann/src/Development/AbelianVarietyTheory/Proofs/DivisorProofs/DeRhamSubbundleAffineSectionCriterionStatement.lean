import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamSubbundleAffineSectionCriterion
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_subbundle_affine_section_criterion : GlobalTheory.Published.ConjugateFiltration → GlobalTheory.CovTop.Hypotheses2 → ∀ (p : ℕ) [Fact p.Prime] {T : Scheme.{0}} [Algebra (ZMod p) Γ(T, ⊤)] (A : Over T) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∀ F : GlobalTheory.VB.Sub H, (∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ F.sec V ↔ e V hV s ∈ PrimitiveSubmodule (onAff A hV)) →
    ∀ C : GlobalTheory.VB.Sub H, (∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ C.sec V ↔ e V hV s ∈ GlobalTheory.ConjSeq.conjDR p Γ(T, V)
        (GlobalTheory.SS.FrobField.cast_zero (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) V) (onAff A hV)) →
    Nonempty (C.toMod ≅ (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).obj (cokernel F.incl)) := by
  first | exact @GlobalTheory.ConjSeq.conj_iso_frobPull_quot | exact GlobalTheory.ConjSeq.conj_iso_frobPull_quot | (intros; apply GlobalTheory.ConjSeq.conj_iso_frobPull_quot <;> assumption)
