import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfCrystallineLift
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.TwentyWordsLeB
import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowBoundsOfAllLettersThickStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowBoundAtPlaceOfLatticeColengthBoundStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowBoundsOfNonThickLetterStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink.RowsCD

theorem lt_ratIn {x y : ℝ} (h : x < y) : x < ((Formalism.MainNotions.N.ratIn x y : ℚ) : ℝ) := by
  unfold Formalism.MainNotions.N.ratIn
  rw [dif_pos h]
  exact (exists_rat_btwn h).choose_spec.1

theorem flat_pos {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) : 0 < Formalism.MainNotions.N.flat L bd l := by
  unfold Formalism.MainNotions.N.flat
  have hE : 0 < Formalism.MainNotions.TwistedPlaces.eta₃ L := by
    unfold Formalism.MainNotions.TwistedPlaces.eta₃; have := L.etaSz_pos; positivity
  have hW : 0 ≤ Formalism.MainNotions.TwistedPlaces.wP L := by
    unfold Formalism.MainNotions.TwistedPlaces.wP Formalism.MainNotions.TwistedPlaces.wB
    have h1 := Formalism.MainNotions.TwistedPlaces.w''_nonneg L
    have h2 := L.etaSz_pos
    have h3 := le_max_left (L.sc.w'' D.R.n + L.etaSz)
      ((⨆ t : D.host.TT, (L.bT t : ℝ)) + L.sc.b' / L.sc.x + L.etaSz)
    have h4 : (0 : ℝ) ≤ ((D.R.t : ℝ) + 1) / 2 := by positivity
    linarith
  have h1 : 0 ≤ (Formalism.MainNotions.TwistedPlaces.wP L + Formalism.MainNotions.TwistedPlaces.eta₃ L) / (l : ℝ) :=
    div_nonneg (by linarith) (Nat.cast_nonneg _)
  have h3 := Formalism.MainNotions.TwistedPlaces.L_ge_one L
  have h4 := L.Sc_pos
  by_cases hb : bd
  · rw [if_pos hb]; linarith
  · rw [if_neg hb]; linarith

theorem coreF_pos {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 < Formalism.MainNotions.N.coreF L bd l lam := by
  unfold Formalism.MainNotions.N.coreF
  have hr : (0 : ℝ) < D.R.r := by linarith [Formalism.MainNotions.TwistedPlaces.k_le_r D, Formalism.MainNotions.TwistedPlaces.k_ge_five D]
  have hn : (0 : ℝ) < (Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1 := by positivity
  exact mul_pos (mul_pos hn hr) (flat_pos L bd l)

theorem bdCD_lt {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E))
    (K₁ K₂ K₃ : ℝ) : Formalism.MainNotions.N.bdCD L bd l lam K₁ K₂ K₃ < Formalism.MainNotions.N.bdCD L bd l lam K₁ (K₂ + 1) K₃ := by
  have e : Formalism.MainNotions.N.bdCD L bd l lam K₁ (K₂ + 1) K₃ =
      Formalism.MainNotions.N.bdCD L bd l lam K₁ K₂ K₃ + Formalism.MainNotions.N.coreF L bd l lam := by
    unfold Formalism.MainNotions.N.bdCD; ring
  rw [e]
  linarith [coreF_pos L bd l lam]

end GlobalTheory.NLink.RowsCD

theorem GlobalTheory.NLink.lengthBoundAtPlaces_of_jointCond : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), ArcLiftingSetup.aux₃ D HW F 320 → RamifiedCoefficientChains.aux₃ D HW F 25 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → π ∈ D.nd.Zgood i → LocalRepresentationCongruenceCondition L HW i r ρ π → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc (lenRowCD L (fun lam => bandOf L HW 320 i r ρ lam) (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃ (D.nd.l i)) := by
  intro D L P HW F C₂ i r ρ π dc h17 h04 h54 h67 hl hπ hJ w hw _ C hC
  have hl2 : D.nd.l i ≠ 2 := by omega
  obtain ⟨hur, hW⟩ := hJ w hw
  have hg : Good (D.nbr i w hw).Kw 1 C.LL := hC.good_one hl2 (le_trans (le_inf le_rfl hur) le_sup_left)
  obtain ⟨Wd, hB, hBox, hcase⟩ := hW C hg
  have hrow : RowL i r ρ π w hw C (bdCD L (bandOf L HW 320 i r ρ w) (D.nd.l i) w
      (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
    rcases hcase with hNT | ⟨hC', d, hAT⟩
    · exact GlobalTheory.T.rowBounds_of_nonThick_letter D L P HW F C₂ i r ρ π w hw C hg Wd h17 h54 h67 hl hπ hB hBox hNT
    · exact GlobalTheory.T.rowBounds_of_all_letters_thick D L P HW F C₂ i r ρ π w hw C hg Wd d _ h04 h54 h67 hl hB hBox hC' hAT
  exact GlobalTheory.T.rowBound_at_place_of_latticeColengthBound D i r ρ π w hw C _ _ hrow
    (GlobalTheory.NLink.RowsCD.lt_ratIn (GlobalTheory.NLink.RowsCD.bdCD_lt L _ _ w _ _ _)).le
