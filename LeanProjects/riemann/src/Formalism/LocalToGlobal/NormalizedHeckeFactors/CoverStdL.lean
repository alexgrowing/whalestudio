import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverFP
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.HeckeStdStatement

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.BasicNotions

namespace Formalism.L2

section Rfl

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

end Rfl

theorem heckeStdPlain_of_statement (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement) : HeckeStdPlain := by
  intro L _ _ _ n a J χ B hJo hB s ϖ k hs hu hk1 hk2
  exact h L n a.W a.ρ a.alg J χ B hJo hB s ϖ k hs hu hk1 hk2

theorem linkEtaTw_of_statement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M ∧ SplitEx (Fm.D x i)) :
    LocsCoverTwF Fm :=
  linkEtaTw_of_plain Fm (heckeStdPlain_of_statement h) hfam

theorem etaN_eq_etaJ_of_statement {D : D7} {M : MtFam D} (T : NormalizedLocalCompatibility D M)
    (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement) (HT : HeckeTied D M) (hex : SplitEx D) {j : ℕ}
    {w : D.what₂.places.Pl} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hw : D.what₂.muAt w ≠ D.what₂.mu0) :
    etaN T j w = D.what₂.etaJ j w :=
  etaN_eq_etaJ_of_plain T (heckeStdPlain_of_statement h) HT hex h1 h2 hw

end Formalism.L2
