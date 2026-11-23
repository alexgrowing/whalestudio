import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianExtensionNormalModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models GlobalTheory.CechPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.HodgeGenDesc

theorem isIso_fromNormalization {U X : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X)
    (hX : Geo.Tor.IsNormalScheme X) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] :
    IsIso j.fromNormalization := by
  obtain ⟨h, ⟨h₁, h₂⟩, -⟩ := GlobalTheory.existsUnique_lift_of_densePart X U X _ j hX ‹_› ‹_› ‹_› ‹_›
    j.fromNormalization (𝟙 X) j.toNormalization inferInstance (by simp)
  refine ⟨h, ?_, h₂⟩
  refine GlobalTheory.normalization_hom_ext j j.fromNormalization ?_ ?_
  · rw [Scheme.Hom.toNormalization_fromNormalization_assoc, h₁, Category.comp_id]
  · simp [h₂]

theorem bijective_app {U N X : Scheme.{0}} (hX : Geo.Tor.IsNormalScheme X) [IsLocallyNoetherian X] (u : U ⟶ N)
    (p : N ⟶ X) [QuasiCompact u] [IsSchemeTheoreticallyDominant u] [UniversallyClosed p] [IsPreimmersion (u ≫ p)]
    [Flat (u ≫ p)] [IsDominant (u ≫ p)] (V : X.Opens) : Function.Bijective (p.app V).hom := by
  have := GlobalTheory.IsNormalScheme.of_pred hX
  have : IsDominant p := .of_comp u p
  have : IsSchemeTheoreticallyDominant p := .of_isDominant p
  have hI := (isIso_fromNormalization_iff (u ≫ p)).1 (isIso_fromNormalization (u ≫ p) hX)
  refine ⟨p.app_injective V, fun t => mem_range_app_of_forall_isAffineOpen p V t fun W hW _ => ?_⟩
  generalize N.presheaf.map _ t = t
  have ht : (p.app W).hom.IsIntegralElem t := GenPush.isIntegral_app_of_universallyClosed p W hW t
  have hs : ((u ≫ p).app W).hom.IsIntegralElem (u.app (p ⁻¹ᵁ W) t) := by
    change ((u.app (p ⁻¹ᵁ W)).hom.comp (p.app W).hom).IsIntegralElem _
    exact RingHom.IsIntegralElem.map ht _
  obtain ⟨h, hh⟩ := (hI W hW).2 _ hs
  refine ⟨h, u.app_injective (p ⁻¹ᵁ W) ?_⟩
  rw [← hh]
  rfl

theorem exists_iso_of_extensions {U X : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X)
    (hX : Geo.Tor.IsNormalScheme X) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j]
    {A : Over U} [GrpObj A] {G G' : Over X} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    {φ : A.left ⟶ G.left} {ψ : A.left ⟶ G'.left} (hφ : IsGrpPullback A G j φ) (hψ : IsGrpPullback A G' j ψ) :
    ∃ e : G ≅ G', IsMonHom e.hom := by
  have := GlobalTheory.IsNormalScheme.of_pred hX
  have : IsSchemeTheoreticallyDominant j := .of_isDominant j
  have := hG.smooth
  have := hG'.smooth
  have := hG.separated
  have := hG'.separated
  obtain ⟨a, ha, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback G j)
  obtain ⟨b, hb, -⟩ := grpPullback_iso hψ (isGrpPullback_pullback G' j)
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.HomExtProOpen.existsUnique_hom_extension_of_dvr
    GlobalTheory.homExtension_semiAbelian_dvr X U j hX G G' hG hG' (a.inv ≫ b.hom) inferInstance
  obtain ⟨F₁, ⟨-, hF₁⟩, -⟩ := GlobalTheory.HomExtProOpen.existsUnique_hom_extension_of_dvr
    GlobalTheory.homExtension_semiAbelian_dvr X U j hX G' G hG' hG (b.inv ≫ a.hom) inferInstance
  obtain ⟨h₁, h₂⟩ := ExtUnique.comp_eq_id_of_pullback j (a.symm ≪≫ b) F F₁ hF' hF₁
  exact ⟨⟨F, F₁, h₁, h₂⟩, hF⟩

theorem lbIso_hodge_pull {S T : Scheme.{0}} {G : Over S} {G' : Over T} [GrpObj G] [GrpObj G'] [QuasiSeparated G.hom]
    {f : T ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {g : ℕ} (hg : GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega G) g) :
    LBIso ((hodge G g).pull f) (hodge G' g) :=
  (hg.lbIso_det_pullback f).trans (pull_isLB hg.isLB_det f) (hg.pullback f).isLB_det
    (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback h hg).isLB_det
    ((hg.pullback f).lbIso_det_of_iso (asIso (GlobalTheory.LieVB.omegaBase h)))

theorem isGenerated_of_pull {N X : Scheme.{0}} [CompactSpace X] (p : N ⟶ X) [Surjective p]
    (hp : ∀ V, Function.Bijective (p.app V).hom) {L : LB X} (h : IsGenerated (L.pull p)) : IsGenerated L := by
  refine isGenerated_iff_forall.2 fun x => ?_
  obtain ⟨n, rfl⟩ := p.surjective x
  obtain ⟨s', hs'⟩ := h.exists_mem n
  obtain ⟨s, rfl⟩ := (bijective_lbSecPull p hp _).2 s'
  exact ⟨s, by rwa [HodgeDominates.nonzeroLocus_lbSecPull] at hs'⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {R : Type} [CommRing R] {ω : R →+* c.F}

theorem j_s (Y : Model Xo c ω) : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap ω := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

theorem exists_common_modification (hω : IsDedFrac ω) (Y C : Model Xo c ω) :
    ∃ (N : Scheme.{0}) (p : N ⟶ Y.X) (p' : N ⟶ C.X) (G : Over N) (_ : GrpObj G) (φ : G.left ⟶ Y.t.G.left)
      (ψ : G.left ⟶ C.t.G.left), Surjective p ∧ (∀ V, Function.Bijective (p.app V).hom) ∧
      IsGrpPullback G Y.t.G p φ ∧ IsGrpPullback G C.t.G p' ψ := by
  obtain ⟨_, _, _, _, _, _, _⟩ := ModelRelCompare.densePart Y hω
  obtain ⟨⟨_, _⟩, hi, -⟩ := hω
  have : CharZero R := ω.charZero
  have := Y.flat
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver C.proj
  have := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks Y.j
  have : GlobalTheory.IsNormalScheme (Xo.XF c) := GlobalTheory.IsNormalScheme.of_isIso_stalkMap Y.j
  have : IsLocallyNoetherian (Xo.XF c) := AmpUniq.isLocallyNoetherian_of_isPreimmersion Y.j
  let f : Xo.XF c ⟶ pullback Y.s C.s := pullback.lift Y.j C.j ((j_s Y).trans (j_s C).symm)
  have hf₁ : f ≫ pullback.fst Y.s C.s = Y.j := pullback.lift_fst _ _ _
  have hf₂ : f ≫ pullback.snd Y.s C.s = C.j := pullback.lift_snd _ _ _
  have : IsPreimmersion (f ≫ pullback.fst Y.s C.s) := hf₁ ▸ inferInstance
  have : QuasiCompact (f ≫ pullback.fst Y.s C.s) := hf₁ ▸ inferInstance
  have : IsPreimmersion f := AmpUniq.isPreimmersion_of_comp f (pullback.fst Y.s C.s)
  have : QuasiCompact f := .of_comp f (pullback.fst Y.s C.s)
  have : Flat (f ≫ pullback.fst Y.s C.s ≫ Y.s) := by
    rw [reassoc_of% hf₁]; infer_instance
  have : IsFinite f.fromNormalization := AmpUniq.isFinite_fromNormalization_graph f (pullback.fst Y.s C.s ≫ Y.s)
  let u := f.toNormalization
  let p := f.fromNormalization ≫ pullback.fst Y.s C.s
  let p' := f.fromNormalization ≫ pullback.snd Y.s C.s
  have hu₁ : u ≫ p = Y.j := by simp [u, p, hf₁]
  have hu₂ : u ≫ p' = C.j := by simp [u, p', hf₂]
  have : IsPreimmersion (u ≫ p) := hu₁ ▸ inferInstance
  have : Flat (u ≫ p) := hu₁ ▸ inferInstance
  have : IsDominant (u ≫ p) := hu₁ ▸ inferInstance
  have : IsPreimmersion u := AmpUniq.isPreimmersion_of_comp u p
  have : Flat u := AmpUniq.flat_of_isPreimmersion u
  have hN := GlobalTheory.IsNormalScheme.pred f.normalization
  have : IsLocallyNoetherian f.normalization := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsDominant p := .of_comp u p
  obtain ⟨_, _, _, _, _, n₁, -⟩ := sabPull Out.CubePf.cubePull p Y.t
  obtain ⟨_, _, _, _, _, n₂, -⟩ := sabPull Out.CubePf.cubePull p' C.t
  obtain ⟨m₀, -⟩ := ObjMaps.exists_sab_cancel (g := 𝟙 _) C.m0.toSABMap
    (by rw [Category.id_comp]; exact Y.m0.toSABMap : SABMap Y.oF.t Xo.univ.t (𝟙 _ ≫ pullback.fst _ _))
  obtain ⟨m₂, -⟩ := ObjMaps.exists_sab_comp C.m m₀
  obtain ⟨a₁, -⟩ := ObjMaps.exists_sab_cancel n₁ (hu₁ ▸ Y.m : SABMap Y.oF.t Y.t (u ≫ p))
  obtain ⟨a₂, -⟩ := ObjMaps.exists_sab_cancel n₂
    ((((Category.id_comp _).trans hu₂.symm : 𝟙 _ ≫ C.j = u ≫ p')) ▸ m₂ : SABMap Y.oF.t C.t (u ≫ p'))
  obtain ⟨e, _⟩ := exists_iso_of_extensions u hN (IsSemiAbelian.pullback p Y.t.G Y.t.semi)
    (IsSemiAbelian.pullback p' C.t.G C.t.semi) a₁.cart a₂.cart
  exact ⟨f.normalization, p, p', (Over.pullback p).obj Y.t.G, inferInstance, _, _,
    surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range, bijective_app Y.normal u p, n₁.cart,
    ((isGrpPullback_of_iso e).comp n₂.cart).congr (Category.id_comp _) rfl⟩

theorem isGenerated_of_isGenerated (hω : IsDedFrac ω) (Y C : Model Xo c ω) {g N : ℕ}
    (hY : GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega Y.t.G) g) (hC : GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega C.t.G) g)
    (h : IsGenerated (lbPow (hodge C.t.G g) N)) : IsGenerated (lbPow (hodge Y.t.G g) N) := by
  obtain ⟨Z, p, p', G, _, φ, ψ, _, hp, h₁, h₂⟩ := exists_common_modification hω Y C
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  have := Y.t.semi.separated
  have := C.t.semi.separated
  have l₁ : (hodge Y.t.G g).IsLB := hY.isLB_det
  have l₂ : (hodge C.t.G g).IsLB := hC.isLB_det
  have l₃ : (hodge G g).IsLB := (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback h₁ hY).isLB_det
  have e₁ := (cls_eq_iff (pull_isLB l₁ p) l₃).2 (lbIso_hodge_pull h₁ hY)
  have e₂ := (cls_eq_iff (pull_isLB l₂ p') l₃).2 (lbIso_hodge_pull h₂ hC)
  rw [cls_pull l₁] at e₁
  rw [cls_pull l₂] at e₂
  refine isGenerated_of_pull p hp ((h.pull p').of_lbIso (pull_isLB (isLB_lbPow l₁ N) p)
    ((cls_eq_iff (pull_isLB (isLB_lbPow l₁ N) p) (pull_isLB (isLB_lbPow l₂ N) p')).1 ?_))
  rw [cls_pull (isLB_lbPow l₁ N), cls_pull (isLB_lbPow l₂ N), cls_lbPow l₁, cls_lbPow l₂, map_nsmul, map_nsmul, e₁, e₂]

theorem main : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (R : Type) [CommRing R] (ω : R →+* c.F) (Y C : Model Xo c ω) (g N : ℕ), IsDedFrac ω → GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega Y.t.G) g → GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega C.t.G) g → IsGenerated (lbPow (hodge C.t.G g) N) → IsGenerated (lbPow (hodge Y.t.G g) N) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ Y C _ _ hω hY hC h => isGenerated_of_isGenerated hω Y C hY hC h

end GlobalTheory.HodgeGenDesc

end
