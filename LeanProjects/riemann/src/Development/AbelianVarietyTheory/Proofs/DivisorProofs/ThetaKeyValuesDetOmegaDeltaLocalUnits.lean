import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumAbelianLocusPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumFibreOfComposableBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueHomogOfFibres
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenRingNormalCharZeroFiniteTypeOverIntStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricRigidifiedBundleBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedAlongAllTraitsRestrictAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOnAbLocusGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOnAbLocusRestrictAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroOnEveryFibreLocalFormBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFormOfTensorSectionInChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualTangentBasisPulledCotangentChartFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualTangentBasisPulledFrameCompatiblePointChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDatumBaseChangeToCoarserPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFormsTensorSectionGenericFibreTransitionGerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualTangentVectorsGenericFibreDetEqDetOmegaTransStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open Classical

namespace GlobalTheory.KeyValsPf

theorem smooth_bG : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension g (KeyVals.bG G ξ).hom := by
  intro S G _ g R _ ξ h
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange g
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) (isGrpPullback_pullback G ξ).1 h

theorem semi_bG : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    IsSemiAbelian G → IsSemiAbelian (KeyVals.bG G ξ) := by
  intro S G _ R _ ξ h
  exact IsSemiAbelian.pullback ξ G h

theorem mem_abLocus_bG {S : Scheme.{0}} (G : Over S) {R : Type} [CommRing R] (ξ : Sp R ⟶ S) (q : Sp R)
    (h : ξ q ∈ abLocus G) : q ∈ abLocus (KeyVals.bG G ξ) := by
  intro K _ _ t ⟨z, hz⟩
  have := h K (t ≫ ξ) ⟨z, by rw [← hz]; rfl⟩
  have P := (IsPullback.of_hasPullback (pullback.snd G.hom ξ) t).paste_horiz (IsPullback.of_hasPullback G.hom ξ)
  have e := P.isoPullback_hom_snd
  show IsProper (pullback.snd (pullback.snd G.hom ξ) t)
  rw [← e]
  infer_instance

theorem mem_abLocus_of_bG {S : Scheme.{0}} (G : Over S) {R : Type} [CommRing R] (ξ : Sp R ⟶ S) [IsOpenImmersion ξ] (q : Sp R)
    (h : q ∈ abLocus (KeyVals.bG G ξ)) : ξ q ∈ abLocus G := by
  intro K _ _ t ⟨z, hz⟩
  have hr : Set.range t ⊆ Set.range ξ := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim w z]
    exact ⟨q, hz.symm⟩
  obtain ⟨u, rfl⟩ : ∃ u : Sp K ⟶ Sp R, u ≫ ξ = t := ⟨IsOpenImmersion.lift ξ t hr, IsOpenImmersion.lift_fac _ _ _⟩
  have : IsProper (pullback.snd (pullback.snd G.hom ξ) u) := h K u ⟨z, ξ.isOpenEmbedding.injective hz⟩
  have P := (IsPullback.of_hasPullback (pullback.snd G.hom ξ) u).paste_horiz (IsPullback.of_hasPullback G.hom ξ)
  rw [← P.isoPullback_inv_snd]
  infer_instance

theorem abLocus_generic : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G], genericPoint S ∈ abLocus G →
    abLocus (KeyVals.bG G (KeyVals.genPt S)) = Set.univ := by
  intro S _ G _ h
  refine Set.eq_univ_of_forall fun q => mem_abLocus_bG G _ q ?_
  have hp : KeyVals.genPt S q ∈ Set.range (S.fromSpecStalk (genericPoint S)) := ⟨q, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hp
  rwa [(hp.antisymm (genericPoint_specializes _)).eq]

theorem abLocus_affine : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] (W : S.Opens) (hW : IsAffineOpen W), (W : Set S).Nonempty →
    IsOpen (abLocus G) → genericPoint S ∈ abLocus G → IsOpen (abLocus (KeyVals.bG G hW.fromSpec)) ∧
      Set.range (spMap (algebraMap Γ(S, W) (FractionRing Γ(S, W)))).base ⊆ abLocus (KeyVals.bG G hW.fromSpec) := by
  intro S _ G _ W hW hne hop h
  haveI : Nonempty W := ⟨⟨hne.some, hne.some_mem⟩⟩
  have e : abLocus (KeyVals.bG G hW.fromSpec) = hW.fromSpec ⁻¹' abLocus G :=
    Set.ext fun q => ⟨mem_abLocus_of_bG (R := Γ(S, W)) G hW.fromSpec q, mem_abLocus_bG (R := Γ(S, W)) G hW.fromSpec q⟩
  have ho : IsOpen (hW.fromSpec ⁻¹' abLocus G) := hop.preimage hW.fromSpec.continuous
  rw [e]
  refine ⟨ho, ?_⟩
  rintro _ ⟨z, rfl⟩
  obtain ⟨q, hq⟩ : genericPoint S ∈ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    exact ((genericPoint_spec S).mem_open_set_iff W.isOpen).2 ⟨hne.some, trivial, hne.some_mem⟩
  refine Specializes.mem_open (y := q) ?_ ho (show hW.fromSpec q ∈ abLocus G from hq ▸ h)
  refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
  intro a ha
  have ha' : algebraMap Γ(S, W) (FractionRing Γ(S, W)) a ∈ (show PrimeSpectrum (FractionRing Γ(S, W)) from z).asIdeal := ha
  have hz : (show PrimeSpectrum (FractionRing Γ(S, W)) from z).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [hz, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at ha'
  exact ha' ▸ Ideal.zero_mem _

theorem exists_keyVal : ∀ κ : Rule, ∀ (S : Scheme.{0}) [IsIntegral S] [CharZero (KeyVals.FF S)] (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    ∀ (c : VB.Chart (LieVB.omega G) g) (i : δ.ι), genericPoint S ∈ c.U ⊓ δ.U i → ∃ v, KeyVals.IsKeyVal κ g L σ c i v := by
  intro κ S _ _ s G _ _ g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz c i hgen
  have hgab : genericPoint S ∈ abLocus G := by
    obtain ⟨p, hp⟩ := hne
    exact ((genericPoint_spec S).mem_open_set_iff hop).2 ⟨p, trivial, hp⟩
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_localFormOfTensorSection_in_chart S G L δ σ i _ (KeyVals.genPt S) hδ (KeyVals.genPt_le _ hgen.2)
  obtain ⟨y, hy, hyb⟩ := GlobalTheory.T.exists_dualTangentBasis_pulledCotangentChartFrame S G g c _ (KeyVals.genPt S) hsa hsm (KeyVals.genPt_le _ hgen.1)
  have hab := abLocus_generic S G hgab
  obtain ⟨x, hxg, hx⟩ := GlobalTheory.KeyDatumAb.exists_keyOn (KeyVals.FF S) (KeyVals.FF S) (RingHom.id _)
    (KeyVals.bG G (KeyVals.genPt S)) (KeyVals.bL L (KeyVals.genPt S)) t g y hg (semi_bG S G _ _ hsa)
    (smooth_bG S G g _ _ hsm) (by rw [hab]; exact isOpen_univ) (GlobalTheory.T.isSymmetric_rigidifiedBundleBaseChange S G L _ _ hsym) (GlobalTheory.T.principalPolarisationOnAbLocus_genericFibre S G L hop hgab hpol) hyb
    (GlobalTheory.T.sectionNonzeroOnEveryFibre_localFormBaseChange S G L δ σ i _ _ t (KeyVals.genPt_le _ hgen.2) ht hnz) (by rw [hab]; exact Set.subset_univ _)
  exact ⟨_, t, y, x, hxg, ht, hy, hx, rfl⟩

theorem keyVal_unit : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ → ∀ (S : Scheme.{0}) [IsIntegral S] [CharZero (KeyVals.FF S)] (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    ∀ (c : VB.Chart (LieVB.omega G) g) (i : δ.ι) (v : KeyVals.FF S), KeyVals.IsKeyVal κ g L σ c i v → ∀ p ∈ c.U ⊓ δ.U i,
      ∃ (V : S.Opens) (_ : V ≤ c.U ⊓ δ.U i) (_ : p ∈ V) (u : Γ(S, V)ˣ), ∀ h : genericPoint S ∈ V,
        S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = v := by
  intro κ hH hF hL S _ _ s G _ _ g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz c i v hv p hp
  obtain ⟨t', y', x, hxg, ht', hy', hx, rfl⟩ := hv
  have hgab : genericPoint S ∈ abLocus G := by
    obtain ⟨p, hp⟩ := hne
    exact ((genericPoint_spec S).mem_open_set_iff hop).2 ⟨p, trivial, hp⟩
  obtain ⟨W, hW, hpW, hle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens) hp
  have hW : IsAffineOpen W := hW
  haveI : Nonempty W := ⟨⟨p, hpW⟩⟩
  obtain ⟨hic, hcz, hft⟩ := GlobalTheory.T.affineOpen_ring_normal_charZero_finiteType_over_int S s W hW ⟨p, hpW⟩ hN hs h0
  haveI : IsNoetherianRing Γ(S, W) := Algebra.FiniteType.isNoetherianRing ℤ _
  have hr : ∀ U : S.Opens, W ≤ U → ⊤ ≤ hW.fromSpec ⁻¹ᵁ U := fun U h q _ =>
    h (show hW.fromSpec q ∈ (W : Set S) from hW.range_fromSpec ▸ ⟨q, rfl⟩)
  have hri := hr _ (hle.trans inf_le_right)
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_localFormOfTensorSection_in_chart S G L δ σ i Γ(S, W) hW.fromSpec hδ hri
  obtain ⟨y, hy, hyb⟩ := GlobalTheory.T.exists_dualTangentBasis_pulledCotangentChartFrame S G g c Γ(S, W) hW.fromSpec hsa hsm (hr _ (hle.trans inf_le_left))
  obtain ⟨hopW, habW⟩ := abLocus_affine S G W hW ⟨p, hpW⟩ hop hgab
  have hsaW := semi_bG S G Γ(S, W) hW.fromSpec hsa
  have hsmW := smooth_bG S G g Γ(S, W) hW.fromSpec hsm
  have hsyW := GlobalTheory.T.isSymmetric_rigidifiedBundleBaseChange S G L Γ(S, W) hW.fromSpec hsym
  have hpoW := GlobalTheory.T.principalPolarisationOnAbLocus_restrict_affineOpen S G L W hW hop hpol
  have hnzW := GlobalTheory.T.sectionNonzeroOnEveryFibre_localFormBaseChange S G L δ σ i Γ(S, W) hW.fromSpec t hri ht hnz
  obtain ⟨z, hzg, hz⟩ := GlobalTheory.KeyDatumAb.exists_keyOn Γ(S, W) (FractionRing Γ(S, W)) (algebraMap _ _)
    (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec) t g y hg hsaW hsmW hopW hsyW hpoW hyb hnzW habW
  subst hzg
  obtain ⟨u, hu⟩ := hL Γ(S, W) (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec) t z y hsaW hsmW hopW hsyW hpoW
    (GlobalTheory.T.uniformisedAlongAllTraits_restrict_affineOpen S G L W hW hsa hunif) hyb hnzW hz
  refine ⟨W, hle, hpW, u, fun h => ?_⟩
  let r : Γ(S, W) →+* KeyVals.FF S := (S.presheaf.germ W (genericPoint S) h).hom
  have hinj : Function.Injective r := germ_injective_of_isIntegral S (genericPoint S) h
  let e : FractionRing Γ(S, W) →+* KeyVals.FF S := IsFractionRing.lift hinj
  have he : (RingHom.id _).comp r = e.comp (algebraMap _ _) := RingHom.ext fun a => (IsFractionRing.lift_algebraMap hinj a).symm
  have hξ := KeyVals.spMap_germ_fromSpec W hW h
  have hx' := GlobalTheory.T.fibreDatum_baseChange_to_coarserPoint S G _ L δ σ i Γ(S, W) (KeyVals.FF S) (KeyVals.FF S) hW.fromSpec r (KeyVals.genPt S) (RingHom.id _)
    t y t' y' x hxg hξ hri ht ht' (GlobalTheory.T.dualTangentBasis_pulledFrame_compatible_pointChange S G _ c Γ(S, W) (KeyVals.FF S) hW.fromSpec r (KeyVals.genPt S) y y' hξ hsa hsm hy hy') hx
  rw [he] at hx'
  have hpb := GlobalTheory.KeyEven.keyPB_of_keyOn_comp Γ(S, W) (FractionRing Γ(S, W)) (KeyVals.FF S) (algebraMap _ _) e
    (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec) t _ y z x rfl hxg hz hx'
  rw [hF _ _ e z x hpb, hu]
  exact (IsFractionRing.lift_algebraMap hinj _).symm

theorem keyVal_compat : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → ∀ (S : Scheme.{0}) [IsIntegral S] [CharZero (KeyVals.FF S)]
    (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S) (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec),
    IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → δ.IsLB →
    ∀ (c c' : VB.Chart (LieVB.omega G) g) (i i' : δ.ι) (v v' : KeyVals.FF S)
      (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
      (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i'),
      KeyVals.IsKeyVal κ g L σ c i v → KeyVals.IsKeyVal κ g L σ c' i' v' →
      v * S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) ^ 8 =
        S.presheaf.germ _ (genericPoint S) h1
          ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) ^ 4 * v' := by
  intro κ hH hF S _ _ G _ _ g L δ σ hsa hsm hδ c c' i i' v v' h1 h2 hv hv'
  obtain ⟨t, y, x, hg, ht, hy, hk, rfl⟩ := hv
  obtain ⟨t', y', x', hg', ht', hy', hk', rfl⟩ := hv'
  obtain ⟨M, hM, hdet⟩ := GlobalTheory.T.dualTangentVectors_genericFibre_det_eq_detOmegaTrans S G g hsa hsm c c' h1 y y' hy hy'
  have hs := GlobalTheory.T.localFormsTensorSection_genericFibre_transitionGerm S G L δ σ hδ i i' h2 t t' ht ht'
  have := GlobalTheory.KeyEven.keyValue_homog_of_fibres κ hH hF (KeyVals.FF S) (KeyVals.bG G (KeyVals.genPt S)) (KeyVals.bL L (KeyVals.genPt S)) t' t g y' y
    x' x hg' hg _ M hk' hk hs hM
  rw [← hdet, mul_comm]
  exact this

theorem keyVals : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ →
  ∀ (S : Scheme.{0}) [IsIntegral S] (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    ∃ f : (VB.det (LieVB.omega G) g).ι → δ.ι → S.presheaf.stalk (genericPoint S),
      (∀ c i, ∀ x ∈ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i, ∃ (V : S.Opens) (_ : V ≤ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i)
        (_ : x ∈ V) (u : Γ(S, V)ˣ), ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f c i) ∧
      (∀ c c' i i' (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
        (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i'),
        f c i * S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) ^ 8 =
          S.presheaf.germ _ (genericPoint S) h1
            ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) ^ 4 * f c' i') := by
  intro κ hH hF hL S _ s G _ _ g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz
  haveI : CharZero (KeyVals.FF S) :=
    charZero_of_injective_ringHom (f := (S.presheaf.germ ⊤ (genericPoint S) trivial).hom)
      (germ_injective_of_isIntegral S (U := ⊤) (genericPoint S) trivial)
  let f : (VB.det (LieVB.omega G) g).ι → δ.ι → S.presheaf.stalk (genericPoint S) := fun c i =>
    if h : ∃ v, KeyVals.IsKeyVal κ g L σ c i v then h.choose else 1
  have hf : ∀ c i, genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i → KeyVals.IsKeyVal κ g L σ c i (f c i) := by
    intro c i h
    have ex := exists_keyVal κ S s G g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz c i h
    simp only [f, dif_pos ex]
    exact ex.choose_spec
  have hgen : ∀ U : S.Opens, (U : Set S).Nonempty → genericPoint S ∈ U := fun U ⟨p, hp⟩ =>
    ((genericPoint_spec S).mem_open_set_iff U.isOpen).2 ⟨p, trivial, hp⟩
  refine ⟨f, fun c i p hp => ?_, fun c c' i i' h1 h2 => ?_⟩
  · exact keyVal_unit κ hH hF hL S s G g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz c i (f c i)
      (hf c i (hgen _ ⟨p, hp⟩)) p hp
  · exact keyVal_compat κ hH hF S G g L δ σ hsa hsm hδ c c' i i' (f c i) (f c' i') h1 h2
      (hf c i ⟨h1.1, h2.1⟩) (hf c' i' ⟨h1.2, h2.2⟩)

end GlobalTheory.KeyValsPf
