import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsCoordinateRelationUniversalJetsStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartLawActionEqTransportedOfCoordRelStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.TangentDirectionTwoChartsLinearPartStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetFramesDifferByUnitEachOrderStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioFirstPartialLawStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioSecondPartialLawStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioSymmetrySeriesStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioAdjointnessSeriesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem jRel_of_charts_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)), Function.Surjective (t.G ⊗ t.G).hom.appTop.hom → ∀ (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x' → IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e → IsFrameG t (𝟙 (Sp V)) d x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e' → ∃ φ φi : Pt V 1 d, (∀ m, ∃ ε : PS V 2 d, JRel m B B' φ φi ε) ∧ ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t (𝟙 (Sp V)) (dirs x') u' v → u = (dLin φ).mulVec u' := by
  intro E _ _ _ H _ hstar V _ _ t hsurj d B B' κ κ' _ _ tg tg' uv uv' x x' e e' hc hc' hu hu' hf hf'
  obtain ⟨φ, φi, hinv, hx, -⟩ := GlobalTheory.T.exists_coordinateRelation_universalJets V t.G d x x' hu hu'
  obtain ⟨hlaw, hact⟩ := GlobalTheory.T.chart_law_action_eq_transported_of_coordRel E H V t d B B' κ κ' tg tg' uv uv' x x' φ φi hc hc' hu hinv hx
  obtain ⟨hg, h1, h2, hs, ha⟩ := (isFrameG_iff t _ d x _ _ _ _ _ _ e).1 hf
  obtain ⟨hg', h1', h2', hs', ha'⟩ := (isFrameG_iff t _ d x' _ _ _ _ _ _ e').1 hf'
  have h0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0 := hinv.1
  refine ⟨φ, φi, fun m => ?_,
    GlobalTheory.T.tangentDirection_two_charts_linearPart E H V t d B B' κ κ' tg tg' uv uv' x x' φ hc hc' hu h0 hx⟩
  obtain ⟨ε, hε, hr⟩ := GlobalTheory.T.jetFrames_differ_by_unit_each_order E H V t d x x' e e' φ h0 hx hg hg' m
  exact ⟨ε, hinv, hε, hlaw, hact,
    GlobalTheory.T.frame_ratio_first_partial_law E H V t d B B' κ κ' tg tg' uv uv' x x' e e' φ φi m ε hc hc' hinv hx hlaw hact hg hg' hr h1 h1',
    GlobalTheory.T.frame_ratio_second_partial_law E H V t d B B' κ κ' tg tg' uv uv' x x' e e' φ φi m ε hc hc' hinv hx hlaw hact hg hg' hr h2 h2',
    GlobalTheory.T.frame_ratio_symmetry_series E H V t d B B' κ κ' tg tg' uv uv' x x' e e' φ φi m ε hc hc' hinv hx hlaw hact hg hg' hr hs hs',
    GlobalTheory.T.frame_ratio_adjointness_series E H V t d B B' κ κ' tg tg' uv uv' x x' e e' φ φi m ε hc hc' hinv hx hlaw hact hg hg' hr hstar hsurj ha ha'⟩

end GlobalTheory.ChartCmp
