import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsIntegralNoetherianCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrHomEqAndIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullbackStructureModuleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineFiniteFree
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem inter_pull_isogeny_eq_deg_mul : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f →
    ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left,
    inter A (fun j => CechPic.pull f.hom.left (c j)) = deg f * inter B c := by
  intro K _ A B f hf J _ hJ c
  obtain ⟨hdim, hflat, -, hrank⟩ := isogeny_flat_finrank K A B f hf
  haveI : IsFinite f.hom.left := hf.1
  haveI : Surjective f.hom.left := hf.2
  haveI := (isIntegral_isLocallyNoetherian_compactSpace K A).1
  haveI := (isIntegral_isLocallyNoetherian_compactSpace K B).1
  have hAproj := (GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K A).2
  have hBproj := (GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K B).2
  have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have hXproj : IsProjOver (f.hom.left ≫ B.X.hom) := by rw [hw]; exact hAproj
  have hAd := topologicalKrullDim_eq_dim K A
  have hBd := topologicalKrullDim_eq_dim K B

  have hgen : f.hom.left (genericPoint A.X.left) = genericPoint B.X.left := by
    have h1 := (genericPoint_spec A.X.left).image f.hom.left.continuous
    rw [Set.image_univ_of_surjective f.hom.left.surjective, closure_univ] at h1
    exact h1.eq (genericPoint_spec B.X.left)
  obtain ⟨V, hgV, hV, hV', hfree⟩ := GlobalTheory.GenFree.exists_affine_finite_free K A.X.left B.X.left B.X.hom
    f.hom.left hXproj hBproj hgen (by rw [hAd, hBd, hdim]) _ rfl
  set n := f.hom.left.residueDegree (genericPoint A.X.left)

  have hn : deg f = n := by
    letI := (f.hom.left.app V).hom.toAlgebra
    obtain ⟨hfr, hfin, hrk⟩ := hfree
    haveI := hfr
    haveI := hfin
    haveI : Module.Flat Γ(B.X.left, V) Γ(A.X.left, f.hom.left ⁻¹ᵁ V) := inferInstance
    obtain ⟨z, -⟩ : genericPoint B.X.left ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
    have e := Scheme.Hom.finrank_of_isPullback _ _ _ _ (GlobalTheory.isPullback_fromSpec_app f.hom.left hV hV') z
    rw [hrank] at e
    have e2 := (Scheme.Hom.finrank_SpecMap_algebraMap Γ(B.X.left, V) Γ(A.X.left, f.hom.left ⁻¹ᵁ V) z).symm.trans e
    rw [Module.rankAtStalk_eq_finrank_of_free, hrk] at e2
    exact e2.symm

  choose L hL hc using fun j => cls_surj (c j)
  obtain rfl : c = fun j => cls (L j) (hL j) := funext fun j => (hc j).symm
  let e : Fin A.dim ≃ J := (Fintype.equivFinOfCardEq hJ).symm
  have key := GlobalTheory.FieldProj.interNum_pull_eq_mul K A.X.left B.X.left B.X.hom f.hom.left hXproj hBproj V n
    hgV hV hV' hfree A.dim (by rw [hBd, hdim]) (fun i => L (e i)) (fun i => hL (e i))
  rw [hw] at key
  rw [hn]
  have hL' : ∀ i, ((fun i => L (e i)) i).pull f.hom.left |>.IsLB := fun i => Semi.LB.isLB_pull (hL (e i)) _
  letI := GlobalTheory.algebraΓOfHom A.X.hom
  letI := GlobalTheory.algebraΓOfHom B.X.hom
  rw [interNum_eq_multiDiff K _ hL', interNum_eq_multiDiff K _ (fun i => hL (e i))] at key
  unfold inter
  rw [← multiDiff_comp_equiv e, ← multiDiff_comp_equiv e (fun j => cls (L j) (hL j))]
  convert key using 3
  · rename_i i
    exact (cls_pull (hL (e i)) f.hom.left _).symm
  · rfl

end GlobalTheory.AV.AbVar
