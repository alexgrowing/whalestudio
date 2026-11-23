import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveSubbundleCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedGraphClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsomorphismSubbundleLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelNonvanishingWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMapExtendsAfterScaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMapExtendsAfterScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleMapDeterminedGenericStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericSubspaceMapExtendsStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsSubbundle)

namespace GlobalTheory.CorankTriple

open TopologicalSpace ReciprocityTheory.ChartRestriction.G GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier
open GlobalTheory.TrueGeo.SmallSec (fnMap fnMap_fnOf)
open GlobalTheory.CorankPair (genRes_pullback_map comp_eq_smul final_eq stalk_smul)

theorem exists_genIso_ofGeneric {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Z : GlobalTheory.Vert.Model O} {F F' : Z.X.Modules} (φ : Z.GenIso F F') (uf : F ⟶ F') (u₂f : F' ⟶ F) (g g₂ : O)
    (hg : g ≠ 0) (hg₂ : g₂ ≠ 0) (hu : Z.genRes.map uf = φ.hom ≫ Z.genRes.map (smulHom F' (Z.const g)))
    (huu₂ : uf ≫ u₂f = smulHom _ (Z.const g) ≫ smulHom _ (Z.const g₂))
    (hu₂u : u₂f ≫ uf = smulHom _ (Z.const g₂) ≫ smulHom _ (Z.const g))
    (M : Submodule Z.X.functionField (genStalk F)) (M' : Submodule Z.X.functionField (genStalk F'))
    (h₁ : ∀ t ∈ M, stalkLinear uf (genericPoint Z.X) t ∈ M')
    (h₂ : ∀ t ∈ M', stalkLinear u₂f (genericPoint Z.X) t ∈ M) :
    ∃ ψ : Z.GenIso (Sub.ofGeneric M).toMod (Sub.ofGeneric M').toMod,
      ψ.hom ≫ Z.genRes.map (Sub.ofGeneric M').incl = Z.genRes.map (Sub.ofGeneric M).incl ≫ φ.hom := by
  obtain ⟨v, hv⟩ := GlobalTheory.T.generic_subspace_map_extends Z.X _ _ uf M M' h₁
  obtain ⟨v₂, hv₂⟩ := GlobalTheory.T.generic_subspace_map_extends Z.X _ _ u₂f M' M h₂
  have hvv₂ : v ≫ v₂ = smulHom _ (Z.const g) ≫ smulHom _ (Z.const g₂) :=
    comp_eq_smul (Sub.ofGeneric M).incl (Sub.ofGeneric M').incl v v₂ uf u₂f _ _ hv hv₂ huu₂
  have hv₂v : v₂ ≫ v = smulHom _ (Z.const g₂) ≫ smulHom _ (Z.const g) :=
    comp_eq_smul (Sub.ofGeneric M').incl (Sub.ofGeneric M).incl v₂ v u₂f uf _ _ hv₂ hv hu₂u
  have : IsIso (Z.genRes.map v) := by
    have := GlobalTheory.Vert.Model.isIso_genRes_map_smulHom (Sub.ofGeneric M).toMod hg
    have := GlobalTheory.Vert.Model.isIso_genRes_map_smulHom (Sub.ofGeneric M).toMod hg₂
    have := GlobalTheory.Vert.Model.isIso_genRes_map_smulHom (Sub.ofGeneric M').toMod hg
    have := GlobalTheory.Vert.Model.isIso_genRes_map_smulHom (Sub.ofGeneric M').toMod hg₂
    have h₁ : IsIso (Z.genRes.map v ≫ Z.genRes.map v₂) := by
      rw [← Functor.map_comp, hvv₂, Functor.map_comp]; infer_instance
    have h₂ : IsIso (Z.genRes.map v₂ ≫ Z.genRes.map v) := by
      rw [← Functor.map_comp, hv₂v, Functor.map_comp]; infer_instance
    have : Mono (Z.genRes.map v) := mono_of_mono _ (Z.genRes.map v₂)
    have : Epi (Z.genRes.map v) := epi_of_epi (Z.genRes.map v₂) _
    exact isIso_of_mono_of_epi _
  exact ⟨asIso (Z.genRes.map v) ≪≫ GlobalTheory.Vert.Model.GenIso.smul _ g hg,
    final_eq (Sub.ofGeneric M).incl (Sub.ofGeneric M').incl v uf φ g hg hv hu⟩

theorem exists_corankOne_triple : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (r : ℕ) (E E' E'' : B.X.Modules) (φ : B.GenIso E E') (φ' : B.GenIso E' E''), GlobalTheory.VB.IsVB E (r + 1) → GlobalTheory.VB.IsVB E' (r + 1) → GlobalTheory.VB.IsVB E'' (r + 1) → ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (K K' K'' : B'.X.Modules) (i : K ⟶ (Scheme.Modules.pullback f.f).obj E) (i' : K' ⟶ (Scheme.Modules.pullback f.f).obj E') (i'' : K'' ⟶ (Scheme.Modules.pullback f.f).obj E'') (ψ : B'.GenIso K K') (ψ' : B'.GenIso K' K''), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ GlobalTheory.VB.IsSubbundle i ∧ GlobalTheory.VB.IsSubbundle i' ∧ GlobalTheory.VB.IsSubbundle i'' ∧ GlobalTheory.VB.IsVB K r ∧ GlobalTheory.VB.IsVB K' r ∧ GlobalTheory.VB.IsVB K'' r ∧ ψ.hom ≫ B'.genRes.map i' = B'.genRes.map i ≫ (φ.pull f.comp_str).hom ∧ ψ'.hom ≫ B'.genRes.map i'' = B'.genRes.map i' ≫ (φ'.pull f.comp_str).hom := by
  intro O _ _ _ p _ _ _ B hB r E E' E'' φ φ' hE hE' hE''
  have := hE.isQuasicoherent
  have := hE'.isQuasicoherent
  have := hE''.isQuasicoherent

  obtain ⟨g, u, hg, hu⟩ := GlobalTheory.ClearDenom.exists_smul_eq_genRes_map O B E E' _ _ hE hE' φ.hom
  obtain ⟨g₂, u₂, hg₂, hu₂⟩ := GlobalTheory.ClearDenom.exists_smul_eq_genRes_map O B E' E _ _ hE' hE φ.inv
  obtain ⟨k, w₁, hk, hw₁⟩ := GlobalTheory.ClearDenom.exists_smul_eq_genRes_map O B E' E'' _ _ hE' hE'' φ'.hom
  obtain ⟨k₂, w₂, hk₂, hw₂⟩ := GlobalTheory.ClearDenom.exists_smul_eq_genRes_map O B E'' E' _ _ hE'' hE' φ'.inv
  have huu : u₂ ≫ u = smulHom E' (B.const g₂) ≫ smulHom E' (B.const g) := by
    refine GlobalTheory.MixedLocalChains.hom_ext_of_genRes O B _ _ _ _ _ hE' ?_
    rw [Functor.map_comp, Functor.map_comp, hu₂, hu, Category.assoc, ← Category.assoc (B.genRes.map _),
      VB.pullback_map_smulHom, smulHom_comp, Category.assoc, Iso.inv_hom_id_assoc]
    simp only [VB.pullback_map_smulHom]
  have huu₂ : u ≫ u₂ = smulHom E (B.const g) ≫ smulHom E (B.const g₂) := by
    refine GlobalTheory.MixedLocalChains.hom_ext_of_genRes O B _ _ _ _ _ hE ?_
    rw [Functor.map_comp, Functor.map_comp, hu₂, hu, Category.assoc, ← Category.assoc (B.genRes.map _),
      VB.pullback_map_smulHom, smulHom_comp, Category.assoc, Iso.hom_inv_id_assoc]
    simp only [VB.pullback_map_smulHom]
  have hww : w₂ ≫ w₁ = smulHom E'' (B.const k₂) ≫ smulHom E'' (B.const k) := by
    refine GlobalTheory.MixedLocalChains.hom_ext_of_genRes O B _ _ _ _ _ hE'' ?_
    rw [Functor.map_comp, Functor.map_comp, hw₂, hw₁, Category.assoc, ← Category.assoc (B.genRes.map _),
      VB.pullback_map_smulHom, smulHom_comp, Category.assoc, Iso.inv_hom_id_assoc]
    simp only [VB.pullback_map_smulHom]
  have hww₂ : w₁ ≫ w₂ = smulHom E' (B.const k) ≫ smulHom E' (B.const k₂) := by
    refine GlobalTheory.MixedLocalChains.hom_ext_of_genRes O B _ _ _ _ _ hE' ?_
    rw [Functor.map_comp, Functor.map_comp, hw₂, hw₁, Category.assoc, ← Category.assoc (B.genRes.map _),
      VB.pullback_map_smulHom, smulHom_comp, Category.assoc, Iso.hom_inv_id_assoc]
    simp only [VB.pullback_map_smulHom]

  choose U e hx he using id hE
  choose U' e' hx' he' using id hE'
  choose U'' e'' hx'' he'' using id hE''
  obtain ⟨T, hT⟩ := exists_finset_iSup_eq_top U hx
  obtain ⟨T', hT'⟩ := exists_finset_iSup_eq_top U' hx'
  obtain ⟨T'', hT''⟩ := exists_finset_iSup_eq_top U'' hx''
  let l' := ((he' (genericPoint B.X)).stalkBasis _ (hx' (genericPoint B.X))).coord 0
  let l₀ : genStalk E →ₗ[B.X.functionField] B.X.functionField := l'.comp (stalkLinear u (genericPoint B.X))
  let l₂ : genStalk E'' →ₗ[B.X.functionField] B.X.functionField := l'.comp (stalkLinear w₂ (genericPoint B.X))
  have hl' : l' ≠ 0 := fun h0 => by
    have := LinearMap.congr_fun h0 ((he' _).stalkBasis _ (hx' (genericPoint B.X)) 0)
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same] at this
    exact one_ne_zero this
  have hgerm (c : O) (hc : c ≠ 0) : B.X.presheaf.germ ⊤ (genericPoint B.X) trivial (B.const c) ≠ 0 := fun h0 =>
    (B.isRegularFn_const hc).ne_zero (germ_injective_of_isIntegral B.X (genericPoint B.X) (show genericPoint B.X ∈ (⊤ : B.X.Opens) from trivial) (h0.trans (map_zero _).symm))
  have hl₀ : l₀ ≠ 0 := fun h0 => by
    have := LinearMap.congr_fun h0 (stalkLinear u₂ _ ((he' _).stalkBasis _ (hx' (genericPoint B.X)) 0))
    have e₁ : l₀ (stalkLinear u₂ _ ((he' _).stalkBasis _ (hx' (genericPoint B.X)) 0)) =
        B.X.presheaf.germ ⊤ (genericPoint B.X) trivial (B.const g) *
          B.X.presheaf.germ ⊤ (genericPoint B.X) trivial (B.const g₂) := by
      change l' ((stalkLinear u _ ∘ₗ stalkLinear u₂ _) _) = _
      rw [← stalkLinear_comp, huu, stalkLinear_comp, LinearMap.comp_apply, stalk_smul, stalk_smul,
        map_smul, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
        smul_eq_mul, smul_eq_mul, mul_one]
    rw [e₁, LinearMap.zero_apply] at this
    exact mul_ne_zero (hgerm g hg) (hgerm g₂ hg₂) this
  have hl₂ : l₂ ≠ 0 := fun h0 => by
    have := LinearMap.congr_fun h0 (stalkLinear w₁ _ ((he' _).stalkBasis _ (hx' (genericPoint B.X)) 0))
    have e₁ : l₂ (stalkLinear w₁ _ ((he' _).stalkBasis _ (hx' (genericPoint B.X)) 0)) =
        B.X.presheaf.germ ⊤ (genericPoint B.X) trivial (B.const k₂) *
          B.X.presheaf.germ ⊤ (genericPoint B.X) trivial (B.const k) := by
      change l' ((stalkLinear w₂ _ ∘ₗ stalkLinear w₁ _) _) = _
      rw [← stalkLinear_comp, hww₂, stalkLinear_comp, LinearMap.comp_apply, stalk_smul, stalk_smul,
        map_smul, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
        smul_eq_mul, smul_eq_mul, mul_one]
    rw [e₁, LinearMap.zero_apply] at this
    exact mul_ne_zero (hgerm k₂ hk₂) (hgerm k hk) this
  let w : (T ⊕ (T' ⊕ T'')) → Fin (r + 1) → B.X.functionField := fun a => Sum.elim
    (fun (α : T) (j : Fin (r + 1)) => l₀ (E.presheaf.germ _ _ (gen_mem (hx α)) (e α j)))
    (Sum.elim
      (fun (β : T') (j : Fin (r + 1)) => l' (E'.presheaf.germ _ _ (gen_mem (hx' β)) (e' β j)))
      (fun (γ : T'') (j : Fin (r + 1)) => l₂ (E''.presheaf.germ _ _ (gen_mem (hx'' γ)) (e'' γ j)))) a
  have hw : ∀ a, ∃ j, w a j ≠ 0 := by
    rintro (α | β | γ)
    · by_contra! H
      exact hl₀ (((he α).stalkBasis _ (gen_mem (hx α))).ext fun j => by
        rw [IsFrame.stalkBasis_apply]; exact H j)
    · by_contra! H
      exact hl' (((he' β).stalkBasis _ (gen_mem (hx' β))).ext fun j => by
        rw [IsFrame.stalkBasis_apply]; exact H j)
    · by_contra! H
      exact hl₂ (((he'' γ).stalkBasis _ (gen_mem (hx'' γ))).ext fun j => by
        rw [IsFrame.stalkBasis_apply]; exact H j)
  obtain ⟨B', f, hη, hB', hrel, hdiv⟩ := GlobalTheory.T.normal_model_nonvanishing_weights O B hB (T ⊕ (T' ⊕ T'')) (Fin (r + 1)) w hw
  have hF := hE.pullback f.f
  have hF' := hE'.pullback f.f
  have hF'' := hE''.pullback f.f
  have := hF.isQuasicoherent
  have := hF'.isQuasicoherent
  have := hF''.isQuasicoherent
  have hU₂ : genericPoint B'.X ∈ f.f ⁻¹ᵁ U' (genericPoint B.X) := show f.f _ ∈ U' _ from hη ▸ hx' _
  let uf := (Scheme.Modules.pullback f.f).map u
  let u₂f := (Scheme.Modules.pullback f.f).map u₂
  let w₁f := (Scheme.Modules.pullback f.f).map w₁
  let w₂f := (Scheme.Modules.pullback f.f).map w₂
  let m' := (((he' _).pullback f.f).stalkBasis _ hU₂).coord 0
  let m : genStalk ((Scheme.Modules.pullback f.f).obj E) →ₗ[B'.X.functionField] B'.X.functionField :=
    m'.comp (stalkLinear uf (genericPoint B'.X))
  let m'' : genStalk ((Scheme.Modules.pullback f.f).obj E'') →ₗ[B'.X.functionField] B'.X.functionField :=
    m'.comp (stalkLinear w₂f (genericPoint B'.X))
  have cE (α : T) (j : Fin (r + 1)) (hα : genericPoint B'.X ∈ f.f ⁻¹ᵁ U α) :
      m (((Scheme.Modules.pullback f.f).obj E).presheaf.germ _ _ hα
        (pullbackSections f.f E (le_refl (f.f ⁻¹ᵁ U α)) (e α j))) =
        fnMap f.f (specializes_of_eq hη) (w (.inl α) j) := by
    change m' (stalkLinear uf _ _) = _
    rw [stalkLinear_germ, pullback_map_app_pullbackSections,
      GlobalTheory.CorankOne.coord_pullback f.f hη (hx' _) hU₂ (he' _) 0 (gen_mem (hx α)) hα]
    change _ = fnMap f.f _ (l' (stalkLinear u _ _))
    rw [stalkLinear_germ]
  have cE' (β : T') (j : Fin (r + 1)) (hβ : genericPoint B'.X ∈ f.f ⁻¹ᵁ U' β) :
      m' (((Scheme.Modules.pullback f.f).obj E').presheaf.germ _ _ hβ
        (pullbackSections f.f E' (le_refl (f.f ⁻¹ᵁ U' β)) (e' β j))) =
        fnMap f.f (specializes_of_eq hη) (w (.inr (.inl β)) j) :=
    GlobalTheory.CorankOne.coord_pullback f.f hη (hx' _) hU₂ (he' _) 0 (gen_mem (hx' β)) hβ _
  have cE'' (γ : T'') (j : Fin (r + 1)) (hγ : genericPoint B'.X ∈ f.f ⁻¹ᵁ U'' γ) :
      m'' (((Scheme.Modules.pullback f.f).obj E'').presheaf.germ _ _ hγ
        (pullbackSections f.f E'' (le_refl (f.f ⁻¹ᵁ U'' γ)) (e'' γ j))) =
        fnMap f.f (specializes_of_eq hη) (w (.inr (.inr γ)) j) := by
    change m' (stalkLinear w₂f _ _) = _
    rw [stalkLinear_germ, pullback_map_app_pullbackSections,
      GlobalTheory.CorankOne.coord_pullback f.f hη (hx' _) hU₂ (he' _) 0 (gen_mem (hx'' γ)) hγ]
    change _ = fnMap f.f _ (l' (stalkLinear w₂ _ _))
    rw [stalkLinear_germ]
  have hQ := GlobalTheory.CorankOne.isVB_cokernel_ofGeneric (F := (Scheme.Modules.pullback f.f).obj E) m fun y => by
    obtain ⟨α, hα⟩ := Opens.mem_iSup.1 (hT.ge (Set.mem_univ (f.f y)))
    obtain ⟨i, hi, hj⟩ := hdiv y (.inl α)
    have hy : y ∈ f.f ⁻¹ᵁ U α := hα
    have c (j) := cE α j (gen_mem hy)
    refine ⟨_, hy, _, i, (he α).pullback f.f, fun h0 => hi ?_, fun j => ?_⟩
    · exact (map_eq_zero _).1 ((c i).symm.trans h0)
    · obtain ⟨g', hg', e₀⟩ := hj j
      exact ⟨g', hg', ((congrArg (g' * ·) (c i)).trans e₀).trans (c j).symm⟩
  have hQ' := GlobalTheory.CorankOne.isVB_cokernel_ofGeneric (F := (Scheme.Modules.pullback f.f).obj E') m' fun y => by
    obtain ⟨β, hβ⟩ := Opens.mem_iSup.1 (hT'.ge (Set.mem_univ (f.f y)))
    obtain ⟨i, hi, hj⟩ := hdiv y (.inr (.inl β))
    have hy : y ∈ f.f ⁻¹ᵁ U' β := hβ
    have c (j) := cE' β j (gen_mem hy)
    refine ⟨_, hy, _, i, (he' β).pullback f.f, fun h0 => hi ?_, fun j => ?_⟩
    · exact (map_eq_zero _).1 ((c i).symm.trans h0)
    · obtain ⟨g', hg', e₀⟩ := hj j
      exact ⟨g', hg', ((congrArg (g' * ·) (c i)).trans e₀).trans (c j).symm⟩
  have hQ'' := GlobalTheory.CorankOne.isVB_cokernel_ofGeneric (F := (Scheme.Modules.pullback f.f).obj E'') m'' fun y => by
    obtain ⟨γ, hγ⟩ := Opens.mem_iSup.1 (hT''.ge (Set.mem_univ (f.f y)))
    obtain ⟨i, hi, hj⟩ := hdiv y (.inr (.inr γ))
    have hy : y ∈ f.f ⁻¹ᵁ U'' γ := hγ
    have c (j) := cE'' γ j (gen_mem hy)
    refine ⟨_, hy, _, i, (he'' γ).pullback f.f, fun h0 => hi ?_, fun j => ?_⟩
    · exact (map_eq_zero _).1 ((c i).symm.trans h0)
    · obtain ⟨g', hg', e₀⟩ := hj j
      exact ⟨g', hg', ((congrArg (g' * ·) (c i)).trans e₀).trans (c j).symm⟩
  let N := Sub.ofGeneric (LinearMap.ker m)
  let N' := Sub.ofGeneric (LinearMap.ker m')
  let N'' := Sub.ofGeneric (LinearMap.ker m'')
  have hS : (ShortComplex.mk _ (cokernel.π N.incl) (cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  have hS' : (ShortComplex.mk _ (cokernel.π N'.incl) (cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  have hS'' : (ShortComplex.mk _ (cokernel.π N''.incl) (cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  have hK := isVB_X₁_of_shortExact B'.X _ r 1 hS hF hQ
  have hK' := isVB_X₁_of_shortExact B'.X _ r 1 hS' hF' hQ'
  have hK'' := isVB_X₁_of_shortExact B'.X _ r 1 hS'' hF'' hQ''
  have hc (c : O) : f.f.appTop (B.const c) = B'.const c := GlobalTheory.Vert.Model.appTop_const f.comp_str c
  have hu₂u : u₂f ≫ uf = smulHom _ (B'.const g₂) ≫ smulHom _ (B'.const g) := by
    rw [← Functor.map_comp, huu, Functor.map_comp, VB.pullback_map_smulHom, VB.pullback_map_smulHom, hc, hc]
  have huu₂f : uf ≫ u₂f = smulHom _ (B'.const g) ≫ smulHom _ (B'.const g₂) := by
    rw [← Functor.map_comp, huu₂, Functor.map_comp, VB.pullback_map_smulHom, VB.pullback_map_smulHom, hc, hc]
  have hw₂w₁ : w₂f ≫ w₁f = smulHom _ (B'.const k₂) ≫ smulHom _ (B'.const k) := by
    rw [← Functor.map_comp, hww, Functor.map_comp, VB.pullback_map_smulHom, VB.pullback_map_smulHom, hc, hc]
  have hw₁w₂ : w₁f ≫ w₂f = smulHom _ (B'.const k) ≫ smulHom _ (B'.const k₂) := by
    rw [← Functor.map_comp, hww₂, Functor.map_comp, VB.pullback_map_smulHom, VB.pullback_map_smulHom, hc, hc]
  obtain ⟨ψ, hψ⟩ := exists_genIso_ofGeneric (φ.pull f.comp_str) uf u₂f g g₂ hg hg₂
    (genRes_pullback_map f φ u g hu) huu₂f hu₂u (LinearMap.ker m) (LinearMap.ker m')
    (fun t ht => LinearMap.mem_ker.2 (LinearMap.mem_ker.1 ht)) fun t ht => by
      refine LinearMap.mem_ker.2 ?_
      change m' ((stalkLinear uf _ ∘ₗ stalkLinear u₂f _) t) = 0
      rw [← stalkLinear_comp, hu₂u, stalkLinear_comp, LinearMap.comp_apply, stalk_smul, stalk_smul,
        map_smul, map_smul, LinearMap.mem_ker.1 ht, smul_zero, smul_zero]
  obtain ⟨ψ', hψ'⟩ := exists_genIso_ofGeneric (φ'.pull f.comp_str) w₁f w₂f k k₂ hk hk₂
    (genRes_pullback_map f φ' w₁ k hw₁) hw₁w₂ hw₂w₁ (LinearMap.ker m') (LinearMap.ker m'')
    (fun t ht => by
      refine LinearMap.mem_ker.2 ?_
      change m' ((stalkLinear w₂f _ ∘ₗ stalkLinear w₁f _) t) = 0
      rw [← stalkLinear_comp, hw₁w₂, stalkLinear_comp, LinearMap.comp_apply, stalk_smul, stalk_smul,
        map_smul, map_smul, LinearMap.mem_ker.1 ht, smul_zero, smul_zero])
    fun t ht => LinearMap.mem_ker.2 (LinearMap.mem_ker.1 ht)
  exact ⟨B', f, N.toMod, N'.toMod, N''.toMod, N.incl, N'.incl, N''.incl, ψ, ψ', hB', hrel,
    ⟨inferInstance, 1, hQ⟩, ⟨inferInstance, 1, hQ'⟩, ⟨inferInstance, 1, hQ''⟩, hK, hK', hK'', hψ, hψ'⟩

end GlobalTheory.CorankTriple
