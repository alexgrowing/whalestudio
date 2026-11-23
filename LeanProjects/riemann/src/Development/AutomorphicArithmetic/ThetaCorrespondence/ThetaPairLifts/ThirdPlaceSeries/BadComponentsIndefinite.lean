import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BadComponentsIndefinite
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoverTypeLatticeComparison
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalShareCountLeExp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RegularEmbeddingsCoverBadEmbeddingLocus

set_option synthInstance.maxHeartbeats 200000

section
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
noncomputable section
namespace GlobalTheory.BadIndef
set_option maxHeartbeats 1000000 in
theorem bad_components_indefinite_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i _ _ _ => BadAt p i := by
  intro hX hP hGD hQ hS hT hSA hGr hG hDG hSz hFD hDg hSh
  have hB := _root_.GlobalTheory.T.cover_type_lattice_comparison_alt hP hG hDG
  have hW := _root_.GlobalTheory.T.local_share_number_bound_alt hP hGr
  have hE := _root_.GlobalTheory.T.bad_embedding_locus_covered_by_regular_alt hX hP hGD hQ hS hT hSA hG hDG hSz hFD hDg hSh
  refine Formalism.MainNotions.Closed.imp (((hB.and hW).and hE).and hDG) ?_
  rintro eps Fm CH - ⟨⟨⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩, ⟨C3, -, x3, h3⟩⟩, ⟨C4, -, x4, h4⟩⟩
  refine ⟨0, le_rfl, max (max x1 x4) (max x2 x3), fun x hx hle ι p hp i hi Y hY => ?_⟩
  have l1 : x1 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hle
  have l4 : x4 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hle
  have l2 : x2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have l3 : x3 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  obtain ⟨ψ₀, hψ₀, hsh⟩ := h2 x hx l2 ι p hp i
  obtain ⟨fr, π, s, ρ, χ, Pb, lam, ψ, lamb, H, hsp, hwh, hlb, hhalf, hPb, hH, hρ, hrkT, hrkB⟩ :=
    h1 x hx l1 ι p hp i hi Y hY
  have hemb := fun k => h3 x hx l3 ι p hp i hi Y hY fr π ρ χ Pb lamb H hPb hH hρ k
  choose n hn1 hn2 using hemb
  have hgd := (h4 x hx l4 ι p hp i hi Y hY).1
  haveI : FiniteDimensional Y.d.c₂.F (Y.V (Gk p i)) := finiteDimensional_of_lat _ hgd.2.1 hgd.2.2
  obtain ⟨S, hSg, hbd⟩ := GlobalTheory.T.bad_part_dim_le_sum_local_shares_whittaker (Fm.D x ι) _ _ π s hsp ρ Pb lam ψ hwh lamb hlb H hhalf n (3 / 2) hn1 hn2 ψ₀ hψ₀
  have hs := hsh S hSg
  have e0 : (0 : ℝ) ≤ Module.finrank ℂ (eig ρ (Pb.comap π) lamb) := Nat.cast_nonneg _
  have e1 : 0 ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := (Real.exp_pos _).le
  have k1 := mul_le_mul_of_nonneg_right hs e0
  have k2 := mul_nonneg e1 e0
  have key : (Formalism.HN.rkK (CovTop.latBad p.R.toRealDat p.F.lv2 i) : ℝ) ≤
      3 * Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) * Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) := by
    rw [hrkT, hrkB]
    refine hbd.trans ?_
    linarith
  exact key
end GlobalTheory.BadIndef
end
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
theorem _root_.GlobalTheory.T.covers_badAt_of_deep_good_size_flat_degree : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i _ _ _ => BadAt p i := by
  first | exact @_root_.GlobalTheory.BadIndef.bad_components_indefinite_alt | exact _root_.GlobalTheory.BadIndef.bad_components_indefinite_alt | (intros; apply _root_.GlobalTheory.BadIndef.bad_components_indefinite_alt <;> assumption)
end
end
