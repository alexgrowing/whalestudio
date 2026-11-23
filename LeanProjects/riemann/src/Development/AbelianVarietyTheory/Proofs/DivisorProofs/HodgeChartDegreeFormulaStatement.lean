import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartDegreeFormula
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorAtMulTriangular
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MvPolynomial Formalism.BasicNotions.DV
open GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag
open GlobalTheory.Cartier GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.WholeFlag
open IsDedekindDomain GlobalTheory.WholeFlag.Glue GlobalTheory.WholeFlag.GlueProof
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_chart_degree_formula : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ) (V : Cover Y) (W : Y.X.Opens) {ι : Type} (U : ι → V.X.Opens) (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (L : Fin g → LB V.X) (m : ℕ) (r : ∀ i, ((L i).pull V.j).ι → V.G.functionFieldˣ), Hyp A p V W U H J d T L m r → ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W → ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ∀ q b : Idx ι L, ⊤ ≤ yt ⁻¹ᵁ chartOpen V U H L m r q → ⊤ ≤ yt ⁻¹ᵁ chartOpen V U H L m r b → ∀ (k : Fin g) (i : Fin (g + g)), ((k : ℕ) < i → e.w (valAt (z ≫ V.j) (((chartM V H J q)⁻¹ * chartM V H J b) i (Fin.castAdd g k))) < 1) ∧ e.w (valAt (z ≫ V.j) (((chartM V H J q)⁻¹ * chartM V H J b) (Fin.castAdd g k) (Fin.castAdd g k)) - valAt z ((chartC V H q k / chartC V H b k : V.G.functionFieldˣ) : V.G.functionField)) < 1 := by
  first | exact @GlobalTheory.WholeFlag.GlueProof.Compare.compare_charts | exact GlobalTheory.WholeFlag.GlueProof.Compare.compare_charts | (intros; apply GlobalTheory.WholeFlag.GlueProof.Compare.compare_charts <;> assumption)
