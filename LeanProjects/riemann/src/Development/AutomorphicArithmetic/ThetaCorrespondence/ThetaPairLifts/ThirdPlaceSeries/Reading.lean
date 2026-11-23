import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightConditionsAtIndex
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPointStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizeAltBisStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftWeightNumerator
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ

set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CovTop.HodgeGapBounds
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
end Weights
end GlobalTheory.CovTop.HodgeGapBounds
namespace GlobalTheory.CovTop.HodgeGapBounds
theorem reading_alt : _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 < (Fm.D x ι).R.m → LawsJ p.T ∧ 1 ≤ (dat p i).p ∧
    1 ≤ (dat p i).q ∧ 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 ∧ InR (Fm.D x ι) ((i : ℕ) + 1) ∧ Even (p.κ i).n ∧
    (∀ τ, Antitone (uM p i τ)) ∧ (∀ τ, 1 ≤ gap (uM p i τ) ((dat p i).p - 1)) ∧
    ∀ s : ℤ, (s = -(cZero (Fm.D x ι) ((i : ℕ) + 1)) ∨ s = 0 ∨ s = cZero (Fm.D x ι) ((i : ℕ) + 1)) →
      (∀ τ, Antitone ((laOf (dat p i) (wtA (p.κ i)) (p.κ i).n + s • hodgeWt (dat p i)) τ)) ∧
      ∀ τ, 1 ≤ gap ((laOf (dat p i) (wtA (p.κ i)) (p.κ i).n + s • hodgeWt (dat p i)) τ) ((dat p i).p - 1) := by
  have hA := _root_.GlobalTheory.T.weight_parameter_strict_antitone_alt _root_.GlobalTheory.T.cov_size_bound
  have hB := _root_.GlobalTheory.CovTop.WtShape.wtN_z
  unfold _root_.GlobalTheory.CovTop.LiftWeightNumerator at hB
  unfold _root_.GlobalTheory.CovTop.LiftsCondition at hA hB ⊢
  refine (hA.and hB).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩ := h
  refine ⟨0, le_rfl, max x1 x2, fun x hx hle ι p hp i hi => ?_⟩
  have a := h1 x hx ((le_max_left _ _).trans hle) ι p hp i hi
  have b := h2 x hx ((le_max_right _ _).trans hle) ι p hp i
  obtain ⟨hp1, hq1, hdeg, -, hSA, -, hanti⟩ := a
  have hc0 : 0 ≤ cZero (Fm.D x ι) ((i : ℕ) + 1) := Int.natCast_nonneg _
  have hgap : ∀ τ, 1 ≤ gap (uM p i τ) ((dat p i).p - 1) := fun τ =>
    one_le_gap_uMinus _ τ hp1 hq1 (hSA τ).1
  have hant0 : ∀ τ, Antitone (uM p i τ) := fun τ => by simpa using (hanti 0 (by norm_num) τ).1
  refine ⟨p.fw.laws, hp1, hq1, hdeg, ⟨by omega, i.2⟩, b.dom.2, hant0, hgap, fun s hs => ?_⟩
  obtain ⟨t, ht3, hts⟩ : ∃ t : ℕ, t ≤ 3 ∧ s + cZero (Fm.D x ι) ((i : ℕ) + 1) = (t : ℤ) * cZero (Fm.D x ι) ((i : ℕ) + 1) := by
    rcases hs with hs | hs | hs
    · exact ⟨0, by norm_num, by rw [hs]; ring⟩
    · exact ⟨1, by norm_num, by rw [hs]; ring⟩
    · exact ⟨2, by norm_num, by rw [hs]; ring⟩
  rw [laOf_add_smul (kc := (Fm.D x ι).R.k - 1) (c0 := cZero (Fm.D x ι) ((i : ℕ) + 1))]
  refine ⟨fun τ => antitone_add_par _ _ τ ?_, fun τ => ?_⟩
  · rw [hts]; exact (hanti t ht3 τ).1
  · rw [gap_add_smul_hodge _ _ _ τ hp1 hq1]
    have := hgap τ
    have h2 : 0 ≤ s + cZero (Fm.D x ι) ((i : ℕ) + 1) := by rw [hts]; positivity
    exact le_add_of_le_of_nonneg this h2
end GlobalTheory.CovTop.HodgeGapBounds
end
end
