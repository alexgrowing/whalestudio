import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanInst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.TieUpA
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GamAtOfLawsCore
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeightModuleIsLatticeOfShortSeriesSpan

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps GlobalTheory

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.RunLat

theorem thc_le_shortTh {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) : X.Thc s w ≤ X.shortTh w := by
  intro x hx
  simp only [PJ.Thc, PJ.scaled, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply] at hx
  obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hx
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hz)

theorem spanAt_of_shortG {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) (β : ℝ) (h : WeightAlgebra.ShortG X w (X.Thc s w) β) : PullbackSections.SpanAt X w := by

  obtain ⟨Sh, hSh, hspan, -⟩ := h
  show Submodule.span _ _ = ⊤
  rw [eq_top_iff, ← hspan]
  exact Submodule.span_mono fun x hx => thc_le_shortTh X s w (hSh hx)

theorem latAt_and_spanAt_of_hypC : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR Bx CT : ℝ) (S : Scal (recB h.toLawsCore)) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : IsDedekindDomain.HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ), EtaleWeightGaps.HypC large₂ (recPlus h j hj) H C2 A2 CR Bx CT S ka wL wF Tn nP nW h0 nus → EtaleWeightGaps.LatAt (recB h.toLawsCore) j ka ∧ ∀ u ∈ ({wF, (recPlus h j hj).wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)), PullbackSections.SpanAt (recPlus h j hj) u := by
  intro D T h j hj large₂ H C2 A2 CR Bx CT S ka wL wF Tn nP nW h0 nus hC
  obtain ⟨hPar, -, hScal, -, hH2, -, -, -⟩ := hC
  obtain ⟨-, -, -, hsK, -, po, -, -, PLam, -, -, hF, hF0, hK⟩ := hScal
  have hSpK : PullbackSections.SpanAt (recPlus h j hj) ka := spanAt_of_shortG _ _ _ _ hK
  refine ⟨GlobalTheory.latAt_record D _ h.toLawsCore (GlobalTheory.RunIn.gamAt_of_lawsCore' D _ h.toLawsCore) large₂ H.CA hPar
    j ka _ (recPlus h j hj) S wL wF hsK hSpK hH2, ?_⟩
  intro u hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl
  · exact spanAt_of_shortG _ _ _ _ hF
  · exact spanAt_of_shortG _ _ _ _ hF0
  · exact hSpK

end GlobalTheory.RunLat
