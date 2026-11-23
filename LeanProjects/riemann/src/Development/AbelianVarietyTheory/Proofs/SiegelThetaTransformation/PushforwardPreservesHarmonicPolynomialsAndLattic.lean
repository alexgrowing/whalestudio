import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FirstIffSecondAndResiduals

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.PushKeeps

theorem push_keeps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (h : Matrix (Fin n) (Fin n) E), IsUnitaryM h → (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), pushLet c h P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) ∧ ∀ Λ : GenLat E n, (Λ.Unimod → (actLat h Λ).Unimod) ∧ Moves h Λ.La (actLat h Λ).La ∧ ccT h * h = 1 ∧ ∀ P ∈ harmL (Dw := Dw) c Λ a, pushLet c h P ∈ harmL (Dw := Dw) c (actLat h Λ) a := by
  intro E _ _ _ H Dw l c n a h hu
  refine ⟨fun P hP => ?_, fun Λ => ⟨GlobalTheory.RepCompare.unimod_act hu, fun v => ?_, hu,
    fun P hP => GlobalTheory.RepCompare.push_mem c hu hP⟩⟩
  · obtain ⟨h1, h2, h3⟩ := hP
    exact ⟨GlobalTheory.PushHarm.push_mem_harmK E H Dw l c n h P hu h1,
      (GlobalTheory.Proof.ColumnMapShift.push_rows E H Dw l c n h P fun τ i => a (τ, i)).1 h2,
      (GlobalTheory.Proof.ColumnMapShift.push_rows E H Dw l c n h P fun τ i => a (τ, i)).2 h3⟩
  · have h' : adjM h * h = 1 := hu
    rw [GlobalTheory.RepCompare.mem_actLat]
    constructor
    · exact fun hv => ⟨v, hv, rfl⟩
    · rintro ⟨u, hu', e⟩
      have e' := congrArg (adjM h).mulVec e
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h', Matrix.one_mulVec, Matrix.one_mulVec] at e'
      exact e' ▸ hu'

end GlobalTheory.PushKeeps
