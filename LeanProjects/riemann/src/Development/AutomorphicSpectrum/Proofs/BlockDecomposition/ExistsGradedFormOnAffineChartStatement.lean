import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGradedFormOnAffineChart
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfMk
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCohomologyRestrictionBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationPropertyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIffStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_graded_form_on_affine_chart : KH.LocGr → KH.PolyTf → ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {W₀ : X.Opens} {d : ℕ}
    (c : Coord q W₀ d) (r : ℕ) (hr : r < s),
    ∃ ω : Idx r d → HU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) (St (TF l s) {W₀}) r,
      ∀ (W : X.Opens) (hW : IsAffineOpen W) (hle : W ≤ W₀) (Q : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))))
        (hQ : Q = St (TF l s) {W}) (hQ₀ : Q ≤ St (TF l s) {W₀}) (hF : IsFil (sP Q) (sFil Q)) (hQW : ∀ T, Q T → InU W T)
        (h : HU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) Q r),
        ∃! f : Idx r d → Γ(X, W), h = ∑ k, GlobalTheory.CompanionTheory.GrCech.fAct hF hQW r (f k) ((resU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) hQ₀).pull r (ω k)) := by
  first | exact @GlobalTheory.CompanionTheory.GrCech.Omega.basis | exact GlobalTheory.CompanionTheory.GrCech.Omega.basis | (intros; apply GlobalTheory.CompanionTheory.GrCech.Omega.basis <;> assumption)
