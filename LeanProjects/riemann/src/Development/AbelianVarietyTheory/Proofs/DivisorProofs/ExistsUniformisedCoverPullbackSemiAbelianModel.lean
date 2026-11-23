import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModificationClosureOfGraphStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalStructureSemiAbelianExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePulledSemiAbelianEqAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointOfLiesOverGenericStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.Mum.CoverPull

theorem pt_mem_abLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ∀ (Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE) (w : Sp Ω), M.pt w ∈ abLocus Z.G := by
  intro o Ω _ _ _ _ S ρS M U₀ EE hO Z w
  haveI : IsProper ρS.P.A.hom := ρS.P.isAb.proper
  haveI : IsProper ((Over.pullback Z.u₀).obj ρS.P.A).hom := by
    show IsProper (pullback.snd ρS.P.A.hom Z.u₀)
    infer_instance
  refine GlobalTheory.range_subset_abLocus_of_isProper (G' := (Over.pullback Z.u₀).obj ρS.P.A) (f := U₀.ι) (φ := Z.φ) Z.semi Z.cart.1 ?_
  have hm : M.pt w ∈ U₀ := M.top_le_preimage_pt hO.ne (x := w) trivial
  exact ⟨⟨_, hm⟩, rfl⟩

theorem exists_unif_pullback : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE) (T : Scheme.{0}) (h : T ⟶ M.Z) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ξ : Sp W ⟶ T, ((ξ ≫ h) ⁻¹' abLocus Z.G).Nonempty → ∃ (G' : Over (Sp W)) (_ : GrpObj G') (_ : IsCommMonObj G') (β : G'.left ⟶ ((Over.pullback h).obj Z.G).left) (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G'), IsGrpPullback G' ((Over.pullback h).obj Z.G) ξ β ∧ LBIso U'.LG.L ((Z.L.L.pull (pullback.fst Z.G.hom h)).pull β) := by
  intro o Ω _ _ _ S ρS M U₀ EE Z T h W _ _ _ hW ξ hab
  obtain ⟨hdvr, hc, hch⟩ := (GlobalTheory.LN.cDvr_iff W).1 hW
  haveI := hch
  obtain ⟨D, A, U, hl, -⟩ := Z.unif W inferInstance inferInstance hc (ξ ≫ h) hab
  have hpt : (pullback.snd Z.G.hom (ξ ≫ h) ≫ ξ) ≫ h = pullback.snd Z.G.hom (ξ ≫ h) ≫ ξ ≫ h := Category.assoc _ _ _
  let β : pullback Z.G.hom (ξ ≫ h) ⟶ pullback Z.G.hom h :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ ξ) (pullback.condition.trans hpt.symm)
  have hβf : β ≫ pullback.fst Z.G.hom h = pullback.fst Z.G.hom (ξ ≫ h) := pullback.lift_fst _ _ _
  have hβs : β ≫ pullback.snd Z.G.hom h = pullback.snd Z.G.hom (ξ ≫ h) ≫ ξ := pullback.lift_snd _ _ _
  refine ⟨(Over.pullback (ξ ≫ h)).obj Z.G, inferInstance, inferInstance, β, D, A, U, ?_, ?_⟩
  · refine (isGrpPullback_pullback Z.G h).cancel ?_ hβs
    exact (isGrpPullback_pullback Z.G (ξ ≫ h)).congr rfl hβf.symm
  · exact LBIso.trans U.LG.isLB (pull_isLB Z.L.isLB _) (pull_isLB (pull_isLB Z.L.isLB _) _) hl
      (GlobalTheory.GenSpread.lbIso_pull_pull Z.L.isLB β hβf.symm)

end GlobalTheory.Mum.CoverPull

namespace GlobalTheory.Mum

theorem exists_uCover_of_zhOut : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → GlobalTheory.ZH.ZHOut ρS M U₀ EE → ∀ (b : o →+* R₁) (e : Ω →+* FractionRing R₁), (∀ x : o, e (algebraMap o Ω x) = algebraMap R₁ (FractionRing R₁) (b x)) → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (φ : A₁.A.left ⟶ ρS.P.A.left), IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ → LBIso A₁.L (ρS.P.L.pull φ) → ∃ C : UCover R₁, C.A = A₁ := by
  intro R₁ _ _ _ o Ω _ _ _ _ S ρS M U₀ EE hO Z b e hb A₁ φ hcart hlb
  have hs : IsProper M.s := GlobalTheory.SpreadAb.isProper_of_isProjOver hO.proj
  have hy : (spMap e ≫ M.pt) ≫ M.s = jK R₁ ≫ spMap b := by
    rw [Category.assoc, M.pt_s, jK, spMap, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact hb x
  obtain ⟨M', h, hgp, -⟩ := GlobalTheory.T.exists_modification_closure_of_graph R₁ o b M.Z M.s hs _ hy
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_cubicalStructure_semiAbelianExtension o Ω S ρS M U₀ EE hO Z
  have hw : pullback.fst Z.G.hom h ≫ Z.G.hom = ((Over.pullback h).obj Z.G).hom ≫ h := pullback.condition
  have mul : ∀ (T : Over M'.S) (x y : T ⟶ (Over.pullback h).obj Z.G), toBase hw (x * y) = toBase hw x * toBase hw y := by
    intro T x y
    exact Over.OverMorphism.ext ((isGrpPullback_pullback Z.G h).2 T x y (toBase hw x) (toBase hw y) rfl rfl).symm
  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, -⟩ := GlobalTheory.UU.exists_isCPMap P₀ mul _ (pull_isLB P₀.L.isLB _) _
    (GlobalTheory.UU.pullIso_isGen P₀.L.isLB _)
  obtain ⟨α, hα, hαl⟩ := GlobalTheory.T.genericFibre_pulled_semiAbelian_eq_abelianVariety R₁ o Ω S ρS M U₀ EE hO Z e M' h hgp A₁ φ hcart hlb
  refine ⟨{ toModif := M'
            G := (Over.pullback h).obj Z.G
            semi := IsSemiAbelian.pullback _ _ Z.semi
            P := ⟨⟨_, rig, pull_isLB P₀.L.isLB _, hr⟩, c, s, h₁, h₂, h₃⟩
            A := A₁
            α := α
            α_cart := hα
            α_lb := by
              show LBIso A₁.L ((P₀.L.L.pull (pullback.fst Z.G.hom h)).pull α)
              rw [hP₀]; exact hαl
            trait := ?_ }, rfl⟩
  intro W _ _ _ hW φW ξ hφ hξ
  obtain ⟨w, k, hk⟩ := GlobalTheory.T.exists_genericPoint_of_lies_over_generic R₁ M' W φW ξ hφ hξ
  have hab : ((ξ ≫ h) ⁻¹' abLocus Z.G).Nonempty := by
    refine ⟨w, ?_⟩
    have e1 : (ξ ≫ h) w = M.pt ((spMap e) k) := by
      rw [Scheme.Hom.comp_apply, hk, ← Scheme.Hom.comp_apply, hgp, Scheme.Hom.comp_apply]
    show (ξ ≫ h) w ∈ abLocus Z.G
    rw [e1]
    exact CoverPull.pt_mem_abLocus o Ω S ρS M U₀ EE hO Z _
  obtain ⟨G', iG, cG, β, D', A', U', hβ, hl⟩ := CoverPull.exists_unif_pullback o Ω S ρS M U₀ EE Z M'.S h W hW ξ hab
  have hid : spMap (RingHom.id W) ≫ ξ = ξ := by
    rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  refine ⟨W, _, inferInstance, inferInstance, RingHom.id W, G', iG, cG, β, D', A', U', hW, Function.injective_id,
    RingHom.Finite.id W, hid.symm ▸ hβ, ?_⟩
  show LBIso U'.LG.L ((P₀.L.L.pull (pullback.fst Z.G.hom h)).pull β)
  rw [hP₀]; exact hl

end GlobalTheory.Mum
