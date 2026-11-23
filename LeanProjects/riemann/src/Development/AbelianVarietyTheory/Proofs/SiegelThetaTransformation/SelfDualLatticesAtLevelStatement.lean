import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattices_at_level : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∀ (M : ℕ) (h : GA D S) (Λ : Lt D.host.E S.rank), 0 < M → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → Λ ∈ Vset D.host.E S.rank M) ∧ ∀ (Lv : SW.Level C.X) (g : GA D T) (L : Lt D.host.E T.rank), L.FG → IsMov (fmt T g) C.X.Λ L → SelfD C.X L ∧ (TrivAt T (C.under Lv) g → L ∈ Lv.lats) ∧ C.under Lv ≠ ⊥ ∧ (L ∈ Lv.lats → ∃ g' ∈ GfC T, TrivAt T (C.under Lv) g' ∧ IsMov (fmt T g') C.X.Λ L) := by
  first | exact @GlobalTheory.Ker.MovLev.mov_mem_lattices | exact GlobalTheory.Ker.MovLev.mov_mem_lattices | (intros; apply GlobalTheory.Ker.MovLev.mov_mem_lattices <;> assumption)
