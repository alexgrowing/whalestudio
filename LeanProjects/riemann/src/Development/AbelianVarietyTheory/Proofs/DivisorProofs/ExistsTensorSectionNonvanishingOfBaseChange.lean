import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIsPsEffAndBigTensNef
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

noncomputable section

namespace GlobalTheory.FieldDescent

open scoped TensorProduct

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC in

theorem exists_sec_of_pull {F E : Type} [Field F] [Field E] [Algebra F E] {Y X : Scheme.{0}}
    {p : Y ⟶ Sp F} {q : X ⟶ Sp E} {π : X ⟶ Y} (H : IsPullback π q p (spMap (algebraMap F E)))
    [CompactSpace Y] [Y.IsSeparated] {N : LB Y} (hN : N.IsLB) (σ : (N.pull π).Sec) (x : X)
    (hx : x ∈ nonzeroLocus σ) : ∃ θ : N.Sec, π x ∈ nonzeroLocus θ := by
  classical
  obtain ⟨n, V, c, hVa, hVc, hcov⟩ := exists_affine_chart_cover N hN
  letI instV : ∀ a, Algebra F Γ(Y, V a) := fun a => (algX p (V a)).toAlgebra
  letI instW : ∀ ab : Fin n × Fin n, Algebra F Γ(Y, V ab.1 ⊓ V ab.2) := fun ab => (algX p _).toAlgebra
  let δ : (∀ a, Γ(Y, V a)) →ₗ[F] (∀ ab : Fin n × Fin n, Γ(Y, V ab.1 ⊓ V ab.2)) :=
    { toFun := fun f ab => dfun N V c hVc f ab.1 ab.2
      map_add' := fun f g => by
        funext ab
        simp only [dfun, Pi.add_apply, map_add, mul_add]
        abel
      map_smul' := fun r f => by
        funext ab
        simp only [dfun, RingHom.id_apply, Pi.smul_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
        rw [ReciprocityTheory.ChartRestriction.G.DVR.rs_mul, ReciprocityTheory.ChartRestriction.G.DVR.rs_mul, rs_algX, rs_algX]
        ring }
  have hδ : ∀ m, δ m = 0 ↔ dfun N V c hVc m = 0 := fun m => by
    constructor
    · intro h; funext a b; exact congrFun h (a, b)
    · intro h; funext ab; exact congrFun (congrFun h ab.1) ab.2
  have hV'c : ∀ a, π ⁻¹ᵁ V a ⊓ q ⁻¹ᵁ ⊤ ≤ (N.pull π).U (fun _ => c a) := fun a y hy =>
    Set.mem_iInter.2 fun _ => hVc a hy.1
  let m' : ∀ a, Γ(X, π ⁻¹ᵁ V a ⊓ q ⁻¹ᵁ ⊤) := fun a => ReciprocityTheory.ChartRestriction.G.DVR.rs (hV'c a) (σ.f (fun _ => c a))
  let t : (∀ a, Γ(Y, V a)) ⊗[F] E := (TensorProduct.piLeft (R := F) (N := E) (M := fun a => Γ(Y, V a))).symm
    (fun a => (eTens p q π H (V a) (hVa a)).symm (m' a))
  have hpt : ∀ a, (TensorProduct.piLeft (R := F) (N := E) (M := fun a => Γ(Y, V a))) t a =
      (eTens p q π H (V a) (hVa a)).symm (m' a) := fun a => by
    simp only [t, LinearEquiv.apply_symm_apply]
  have ht : δ.rTensor E t = 0 := by
    apply (TensorProduct.piLeft (R := F) (N := E) (M := fun ab : Fin n × Fin n => Γ(Y, V ab.1 ⊓ V ab.2))).injective
    rw [map_zero]
    funext ab
    obtain ⟨a, b⟩ := ab
    rw [piLeft_apply_eq, ← LinearMap.rTensor_comp_apply]
    have hdec : (LinearMap.proj (a, b) : (∀ ab : Fin n × Fin n, Γ(Y, V ab.1 ⊓ V ab.2)) →ₗ[F] _).comp δ =
        (rsL p (V a) (V a ⊓ V b) inf_le_left).comp (LinearMap.proj a) -
          (mulL p (V a ⊓ V b) (ReciprocityTheory.ChartRestriction.G.Semi.res (pair_le N V c hVc a b) (N.g (c a) (c b))).val).comp
            ((rsL p (V b) (V a ⊓ V b) inf_le_right).comp (LinearMap.proj b)) := by
      ext f; rfl
    rw [hdec, LinearMap.rTensor_sub, LinearMap.sub_apply, LinearMap.rTensor_comp_apply, LinearMap.rTensor_comp_apply,
      LinearMap.rTensor_comp_apply, ← piLeft_apply_eq, ← piLeft_apply_eq, hpt, hpt]
    apply (eTens p q π H (V a ⊓ V b) ((hVa a).inf (hVa b))).injective
    rw [map_sub, eTens_rs p q π H (V a) (V a ⊓ V b) (hVa a) _ inf_le_left, eTens_mul,
      eTens_rs p q π H (V b) (V a ⊓ V b) (hVa b) _ inf_le_right, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, Pi.zero_apply, map_zero, sub_eq_zero]
    refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.fn_ext fun y hy => ?_
    have hyk : y ∈ (N.pull π).U (fun _ => c a) := Set.mem_iInter.2 fun _ => hVc a hy.1.1
    have hyl : y ∈ (N.pull π).U (fun _ => c b) := Set.mem_iInter.2 fun _ => hVc b hy.1.2
    have hyk' : y ∈ π ⁻¹ᵁ V a ⊓ q ⁻¹ᵁ ⊤ := ⟨hy.1.1, hy.2⟩
    have hyl' : y ∈ π ⁻¹ᵁ V b ⊓ q ⁻¹ᵁ ⊤ := ⟨hy.1.2, hy.2⟩
    have hφy : π y ∈ V a ⊓ V b := hy.1
    simp only [m']
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_mul _ y _ hy, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res _ y _ hy,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res _ y _ hyk', ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res _ y _ hy,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res _ y _ hyl', ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_appLE π _ _ _ (𝟙 _) y hy]
    erw [Category.id_comp, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_unit _ y _ hφy, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_res _ y _ hφy]
    erw [gs_sec (N.pull π) σ (fun _ => c a) (fun _ => c b) y hyk hyl,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_pull_g N π (𝟙 _) y (fun _ => c a) (fun _ => c b) hyk hyl, Category.id_comp]
  let b := Module.Basis.ofVectorSpace F E
  let e₁ := TensorProduct.equivFinsuppOfBasisRight (M := ∀ a, Γ(Y, V a)) b
  let e₂ := TensorProduct.equivFinsuppOfBasisRight (M := ∀ ab : Fin n × Fin n, Γ(Y, V ab.1 ⊓ V ab.2)) b
  have nat : ∀ u β, e₂ (δ.rTensor E u) β = δ (e₁ u β) := by
    intro u β
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul m a =>
      simp only [LinearMap.rTensor_tmul, e₁, e₂, TensorProduct.equivFinsuppOfBasisRight_apply_tmul,
        Finsupp.mapRange_apply, map_smul]
    | add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv]
  have hβ : ∀ β, dfun N V c hVc (e₁ t β) = 0 := fun β =>
    (hδ _).1 (by rw [← nat, ht, map_zero, Finsupp.zero_apply])
  choose θ hθ using fun β => exists_glue N V c hVc hN hcov (e₁ t β) (hβ β)
  by_contra hcon
  push_neg at hcon
  obtain ⟨j, hj⟩ : ∃ j, π x ∈ V j := TopologicalSpace.Opens.mem_iSup.1 (by rw [hcov]; trivial)
  have hxj : x ∈ π ⁻¹ᵁ V j ⊓ q ⁻¹ᵁ ⊤ := ⟨hj, trivial⟩
  have hxc : x ∈ (N.pull π).U (fun _ => c j) := hV'c j hxj
  have hu := (mem_nonzeroLocus_iff_isUnit σ hxc).1 hx
  rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res (𝟙 X) x (hV'c j) hxj] at hu
  change IsUnit (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 X) x _ (m' j)) at hu
  have hexp : t = (e₁ t).sum fun β m => m ⊗ₜ[F] b β := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  have hm : m' j = (e₁ t).sum fun β m => (π.appLE (V j) (π ⁻¹ᵁ V j ⊓ q ⁻¹ᵁ ⊤) inf_le_left).hom (m j) *
      algX q (π ⁻¹ᵁ V j ⊓ q ⁻¹ᵁ ⊤) (b β) := by
    have h1 := hpt j
    rw [hexp, piLeft_apply_eq, Finsupp.sum, map_sum] at h1
    simp only [LinearMap.rTensor_tmul, LinearMap.proj_apply] at h1
    rw [← RingEquiv.apply_symm_apply (eTens p q π H (V j) (hVa j)) (m' j), ← h1, map_sum, Finsupp.sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [eTens_tmul]
  have key : ∀ β, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 X) x _
      ((π.appLE (V j) (π ⁻¹ᵁ V j ⊓ q ⁻¹ᵁ ⊤) inf_le_left).hom (e₁ t β j)) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := fun β => by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_appLE π _ _ _ (𝟙 X) x hxj, Category.id_comp, ← hθ β]
    simp only [ev]
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res π x (hVc j) hj, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      ← mem_nonzeroLocus_iff_pull (θ β) π x (hVc j hj)]
    exact hcon (θ β)
  have hmem : ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 X) x _ (m' j) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [hm, Finsupp.sum, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_eq (𝟙 X) x _ hxj, map_sum, map_sum]
    refine Ideal.sum_mem _ fun β _ => ?_
    rw [map_mul, map_mul, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_eq (𝟙 X) x _ hxj]
    exact Ideal.mul_mem_right _ _ (key β)
  exact (IsLocalRing.mem_maximalIdeal _).1 hmem hu

theorem exists_sec_tens_of_baseChange : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → ∀ (L M : LB Y), L.IsLB → M.IsLB → ∀ x : X, (∃ s : (tens (L.pull π) (M.pull π)).Sec, x ∈ nonzeroLocus s) → ∃ s : (tens L M).Sec, π x ∈ nonzeroLocus s := by
  intro k E _ _ _ Y X p q π H hP L M hL hM x ⟨s, hs⟩
  have : IsProper p := CommonModel.isProper_of_isProjOver hP
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : Y.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  have hN := isLB_tens hL hM
  have hNp := LB.isLB_pull hN π
  have hT := isLB_tens (LB.isLB_pull hL π) (LB.isLB_pull hM π)
  have iso : LBIso ((tens L M).pull π) (tens (L.pull π) (M.pull π)) := by
    refine (cls_eq_iff hNp hT).1 ?_
    rw [cls_pull hN π hNp, cls_tens hL hM hN, map_add, cls_tens (LB.isLB_pull hL π) (LB.isLB_pull hM π) hT,
      cls_pull hL π, cls_pull hM π]
  obtain ⟨s₂, hs₂⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hNp hT iso s
  exact exists_sec_of_pull H hN s₂ x (hs₂ ▸ hs)

end GlobalTheory.FieldDescent
