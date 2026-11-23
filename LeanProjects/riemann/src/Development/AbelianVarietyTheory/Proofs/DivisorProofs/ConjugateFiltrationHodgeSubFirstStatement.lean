import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateFiltrationHodgeSubFirst
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_filtration_hodge_sub_first : GlobalTheory.Published.ConjugateFiltration → GlobalTheory.CovTop.Hypotheses2 → ∀ (p : ℕ) [Fact p.Prime] {T : Scheme.{0}} [Algebra (ZMod p) Γ(T, ⊤)] (A : Over T) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∀ F : GlobalTheory.VB.Sub H, (∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ F.sec V ↔ e V hV s ∈ PrimitiveSubmodule (onAff A hV)) →
    ∀ Ψ : (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).obj H ⟶ H, (∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      e V hV ((Ψ).app V (GlobalTheory.QCoh.pullbackSections (GlobalTheory.VB.frob T p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))) H
        (le_refl V) s)) =
      GlobalTheory.ConjSeq.frobDR p Γ(T, V) (GlobalTheory.SS.FrobField.cast_zero (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) V)
        (onAff A hV) (e V hV s)) →
    (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).map F.incl ≫ Ψ = 0 := by
  first | exact @GlobalTheory.ConjSeq.frobPull_incl_comp_linFrob_eq_zero | exact GlobalTheory.ConjSeq.frobPull_incl_comp_linFrob_eq_zero | (intros; apply GlobalTheory.ConjSeq.frobPull_incl_comp_linFrob_eq_zero <;> assumption)
