import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdmissibleAffineModelDividingTuple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBundleOnAdmissibleModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSumDivThetaConstDotProductMem
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlobalGenerators
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem exists_model_semiAbelian_of_geo :
    GlobalTheory.Published.SemistableReductionSt → ThmUSt → Laws → Laws2 → UTorsSt → ZHGeoSt → ZHSt := by
  intro hN hU hL hL2 hTors hGeo o Ω _ _ _ hb S ρ hBig J₀ _ t₀ ht hfin
  have hT : S.HasTests := (GlobalTheory.T.thetaSystem_hasTests_of_real_point hN hU hL hL2 hTors o Ω S ρ).1
  obtain ⟨M, U₀, hA, -, hD⟩ := @GlobalTheory.ZH.exists_admissible_affine_model_dividing_tuple o Ω _ _ _ _ S J₀ _ t₀ ht hfin
  obtain ⟨EE, hEE, hE⟩ := @GlobalTheory.ZH.exists_isEE_of_adm o Ω _ _ _ _ S M U₀ hT hA
  have hO : S.Over₀ M U₀ := hA.1
  haveI := hb.ft
  haveI := hb.char
  have hll := @GlobalTheory.ZH.classical_points_and_local_regularity o Ω _ _ _ _ _ M U₀ hO.normal
  have hte := @GlobalTheory.ZH.exists_at_test_of_cen o Ω _ _ _ _ S M U₀ hT hO
  have hwt := @GlobalTheory.ZH.test_weights o Ω _ _ _ _ S
  have h0a := @GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω _ _ _ _ S M U₀ hO
  have h0b := @GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω _ _ _ _ S M U₀ hO hll hte h0a
  have h11 := @GlobalTheory.thetaSys_norm_FF_le_exp o Ω _ _ _ _ S hwt
  have h12 := @GlobalTheory.norm_val_FF_eq_of_div o Ω _ _ _ _ S M U₀ hO h0a h11 hte
  have hne := @GlobalTheory.ZH.FF_TT_ne_zero o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt
  have hsec := @GlobalTheory.ZH.DualSection.ff_div_th_mul_dotProduct_mem o Ω _ _ _ _ S M U₀ EE hA hll hte h0a h0b hwt h11 h12 hne hE
  obtain ⟨n, a, GG, hGG⟩ := @GlobalTheory.ZH.GlobalGen.exists_global_generators o Ω _ _ _ _ S M U₀ EE hA hll.2 h0b hne hE hsec
  exact ⟨M, U₀, EE, hO, hD, hEE, hGeo o Ω S ρ hBig M U₀ EE hO hEE ⟨n, a, fun k j => (GG k j : Ω), hGG⟩⟩

end GlobalTheory.ZH
