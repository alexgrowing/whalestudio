import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArcDataOfBadReductionFiniteExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtIn
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arcData_of_badReduction_finiteExtension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype), Y.N3 → Y.SplitFibres → ∀ (T : CDVR) (io : c.F →+* T.Fr) (b : V →+* T.V) (y' : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), (algebraMap T.V T.Fr).comp b = io.comp V.subtype → y' ≫ Y.s = spMap b → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' → ¬ Set.range y' ⊆ abLocus Y.t.G → ∃ (T' : CDVR) (g : T.V →+* T'.V) (ϖ : T'.V) (a : ArcIn Dw l V.subtype T'.V (g.comp b)), Function.Injective g ∧ g.Finite ∧ Irreducible ϖ ∧ Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id T'.V) ϖ (spMap g ≫ y') := by
  first | exact @GlobalTheory.ArcOfPoint.exists_arcIn_of_bad_reduction | exact GlobalTheory.ArcOfPoint.exists_arcIn_of_bad_reduction | (intros; apply GlobalTheory.ArcOfPoint.exists_arcIn_of_bad_reduction <;> assumption)
