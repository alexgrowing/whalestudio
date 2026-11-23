import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AdjointnessSeriesTransportFramesStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FirstPartialLawPushAlongTripleMapStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.SecondPartialLawPushAlongTripleMapStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FamSyPushStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PushChartStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsPushFrStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGroupIsoCubicalIsoOfTripleMapIdStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartsWithFramesRelatedAllOrdersStatement

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem jrel_of_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (V : Type) [CommRing V] [IsLocalRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))), Function.Surjective (t'.G ⊗ t'.G).hom.appTop.hom → ∀ (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t'.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t' (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d) x' → IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e → IsFrameG t' (𝟙 (Sp V)) d x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e' → ∃ φ φi : Pt V 1 d, (∀ m, ∃ ε : PS V 2 d, JRel m B B' φ φi ε) ∧ ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t' (𝟙 (Sp V)) (dirs x') u' (v ≫ n.φ) → u = (dLin φ).mulVec u' := by
  intro E _ _ _ H _ hstar V _ _ t t' n hs d B B' κ κ' _ _ tg tg' uv uv' x x' e e' hc hc' hu hu' hf hf'
  obtain ⟨y, hy, hyu, hyc, hycomb⟩ := GlobalTheory.T.pushChartAlt E H V t t' n d x
  obtain ⟨_, _, _, _, _, w, hw⟩ := GlobalTheory.T.exists_groupIso_cubicalIso_of_tripleMap_id E H V t t' n
  obtain ⟨hg, h1, h2, h3, h4⟩ := (isFrameG_iff t _ d x _ _ _ _ _ _ e).1 hf
  obtain ⟨f, hp⟩ := GlobalTheory.T.exists_pushFr_of_isGen E H V t t' n w d x y e hw.1 hy hg
  have hfy : IsFrameG t' (𝟙 (Sp V)) d y B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad f :=
    (isFrameG_iff t' _ d y _ _ _ _ _ _ f).2
      ⟨fun m => (hp m).1,
        GlobalTheory.T.firstPartialLaw_push_along_tripleMap E H V t t' n w d x y e f hw hy hg hp _ _ κ tg uv _ hc h1,
        GlobalTheory.T.secondPartialLaw_push_along_tripleMap E H V t t' n w d x y e f hw hy hg hp _ _ κ tg uv _ hc h2,
        GlobalTheory.T.famSy_of_pushFr_cubIso E H V t t' n w d x y e f hw hy hg hp _ h3,
        GlobalTheory.T.adjointness_series_transport_frames E H V t t' n w d x y e f hw hy hg hp _ _ κ tg uv _ hc h4⟩
  obtain ⟨φ, φi, hj, hd⟩ := GlobalTheory.T.chartsWithFrames_related_allOrders E H hstar V t' hs d B B' κ κ' (fun l => tg l ≫ n.φ) tg' uv uv' y x' f e'
    (hyc _ _ κ tg uv hc) hc' (hyu hu) hu' hfy hf'
  exact ⟨φ, φi, hj, fun u u' v h h' => hd u u' _ (hycomb u v h) h'⟩

end GlobalTheory.ChartCmp
