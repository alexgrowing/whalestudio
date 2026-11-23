import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittChartDescendLevel
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.InUQT
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution CrystallineSemistableComparison.Pb.LsQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_chart_descend_level : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ} (hn : n ≠ 0) {W : X.Opens} {d : ℕ} (c' : Chart (Wc.pd l k (n + 1)) l q ((Wc.res l k (n + 1)).comp ρ) W d), ∃ (c : Chart (Wc.pd l k n) l q ((Wc.res l k n).comp ρ) W d) (e : c.D ≅ (qF (F := B.schFn q) (ρ := ρ) hn).obj c'.D), (∀ i, e.hom.φ (c.t i) = Ideal.Quotient.mk _ (c'.t i)) ∧ (FlatT ((qF (F := B.schFn q) (ρ := ρ) hn).obj c'.D) → FlatT c.D) := by
  first | exact @GlobalTheory.CompanionTheory.ChartRed.chart_q | exact GlobalTheory.CompanionTheory.ChartRed.chart_q | (intros; apply GlobalTheory.CompanionTheory.ChartRed.chart_q <;> assumption)
