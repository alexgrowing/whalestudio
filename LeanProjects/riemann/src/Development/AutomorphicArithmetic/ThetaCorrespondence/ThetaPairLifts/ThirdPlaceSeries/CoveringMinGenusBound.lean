import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringMinGenusBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPointStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizesOfCoverStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeepLatticeEqLevelLatticeOfCovers

set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.LevDesc
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
namespace GlobalTheory.CovGminTop
section Abstract
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end Abstract
section Point
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
theorem covering_gmin_of_gram_deep_size : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.MinimalGenerator := by
  intro hP hGr hDG hS
  obtain ⟨C, hC, hg⟩ := _root_.GlobalTheory.T.exists_good_cover_at_minimal_level hP
  refine Closed.imp (((_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS).and (_root_.GlobalTheory.T.size_bounds_for_family_alt hS)).and ((_root_.GlobalTheory.T.exists_psi_isTypeLevel_latDeep_eq_latN hP hGr hDG).and hDG)) ?_
  rintro eps Fm CH - ⟨⟨⟨_, -, h1⟩, _, -, h2⟩, ⟨_, -, h3⟩, _, -, h4⟩
  obtain ⟨x1, h5⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (C + 45)
  obtain ⟨x0, h⟩ := (h1.and h2).and (h3.and h4)
  refine ⟨0, le_rfl, max x0 x1, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := h x hx ((le_max_left _ _).trans hle) ι p hp
  obtain ⟨b1, b2, b3, -⟩ := a1 i hi
  obtain ⟨c1, c2, c3, c4, c5, c6, -, -, c7, c8, -, c9, c10, -⟩ := a2 i hi Y hY
  obtain ⟨fr, ψ, -, d1, d2, d3⟩ := a3 i hi Y hY
  have hL := (h5 x ((le_max_right _ _).trans hle) ι).2.2.1
  have hn : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 4 ≤ (p.κ i).n := by
    rw [WtShape.cols_eq]; exact (Fm.parT x hx ι).nV_ge
  obtain ⟨s, e1, e2, e3⟩ := hg _ p.T c1 _ b1 b2 b3 c2 Y _ _ hY.1 _ c3 c4 c5 c6 le_rfl (wtA (p.κ i)) (p.κ i).n
    (dom_wtA _) (p.κ i).n_even hn (half_lt_laOf p i) (c9.trans (by linarith))
  obtain ⟨k1, k2⟩ := GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm _ p.T c1 _ b1 b2 b3 c2 Y _ _ hY.1 (Gk p i)
    ((Int.even_coe_nat _).2 (p.κ i).n_even)
  refine gminAt_of_gens p i Y (by omega) d1.coprime k1 k2 (a4 i hi Y hY).1 _ _ d2 s e1 e2 _ _ (fun y hy σ => (e3 y hy σ).1)
    (num_step hC (hL.trans ?_) (one_le_kap p i b1) c10 d3)
  have f1 : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.f)
  have f2 : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.r)
  exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le f1 f2)
end GlobalTheory.CovGminTop
end
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_gmin_of_prints_gram_deep_size : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.MinimalGenerator := by
  first | exact @_root_.GlobalTheory.CovGminTop.covering_gmin_of_gram_deep_size | exact _root_.GlobalTheory.CovGminTop.covering_gmin_of_gram_deep_size | (intros; apply _root_.GlobalTheory.CovGminTop.covering_gmin_of_gram_deep_size <;> assumption)
end
end
