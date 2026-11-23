import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralAppOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDiv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.HodgeDominates

theorem exists_sec_div {X : Scheme.{0}} [CompactSpace X] [QuasiSeparatedSpace X] {L A : LB X} (hL : L.IsLB)
    (hA : A.IsLB) (t : L.Sec) (i : A.ι) (hi : nonzeroLocus t ≤ A.U i) :
    ∃ r : ℕ, 0 < r ∧ ∀ (M : LB X) (hM : M.IsLB), cls M hM = r • cls L hL - cls A hA →
      ∃ s : M.Sec, nonzeroLocus t ≤ nonzeroLocus s := by
  have hA' := isLB_dual hA
  obtain ⟨N, u, hu⟩ := TwistGen.exists_sec_of_le_chart hA' hL 1 t.f
    (fun y j j' hj hj' => by rw [pow_one]; exact gs_compat t (𝟙 X) y hj hj')
    (nonzeroLocus t) (fun y j hj => mem_nonzeroLocus_iff_isUnit t hj) i hi
  obtain ⟨v, hv⟩ := TwistGen.exists_mul_pow (1 * N) 1 u t
  refine ⟨1 * N + 1, Nat.succ_pos _, fun M hM e => ?_⟩
  have hT := AbLaw.isLB_tw hA' hL ((1 * N + 1 : ℕ) : ℤ)
  have e' : cls _ hT = cls _ hA' - cls _ (AbLaw.isLB_pw hL (-((1 * N + 1 : ℕ) : ℤ))) :=
    cls_div hA' (AbLaw.isLB_pw hL _) _
  obtain ⟨s, hs⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hM hT ((cls_eq_iff hM hT).1 (by
    rw [e, e', AmpleStabFinite.cls_pw hL, cls_dual hA]
    module)) v
  exact ⟨s, fun y hy => hs.ge (hv ⟨hu hy, hy⟩)⟩

theorem nonzeroLocus_lbSecPull {X Y : Scheme.{0}} (L : LB X) (s : L.Sec) (f : Y ⟶ X) :
    nonzeroLocus (lbSecPull L s f) = f ⁻¹ᵁ nonzeroLocus s := Cartier.nonzeroLocus_secPull _ _

theorem exists_sec_of_common {N X X' : Scheme.{0}} [CompactSpace N] [QuasiSeparatedSpace N] (p : N ⟶ X) (p' : N ⟶ X')
    (hp : ∀ V, Function.Bijective (p.app V).hom) (n₀ : N)
    (hn : ∀ W : X.Opens, p n₀ ∈ W → ∃ W' : X'.Opens, p' n₀ ∈ W' ∧ p' ⁻¹ᵁ W' ≤ p ⁻¹ᵁ W)
    {ω : LB X} {ω' P B : LB X'} (hω : ω.IsLB) (hω' : ω'.IsLB) (hP : IsAmpleLB P) (hB : B.IsLB)
    (e : LBIso (ω.pull p) (ω'.pull p')) {k : ℕ} (hk : 0 < k) (ek : cls P hP.isLB + cls B hB = k • cls ω' hω')
    (b : B.Sec) (hb : p' n₀ ∈ nonzeroLocus b) {A : LB X} (hA : A.IsLB) :
    ∃ m : ℕ, 0 < m ∧ ∃ s : (LB.div (lbPow ω m) A).Sec, p n₀ ∈ nonzeroLocus s := by
  obtain ⟨i, hi⟩ := exists_chart hA (p n₀)
  obtain ⟨W', hW', hle⟩ := hn _ hi
  obtain ⟨n, hn, t, h₁, h₂, -⟩ := hP.exists_affine_le hW'
  have hT := isLB_tens hP.isLB hB
  obtain ⟨t', ht'⟩ := exists_sec_pow_nonzeroLocus_eq_inf hP.isLB hB hT
    ((cls_eq_iff hB (LB.isLB_div hT hP.isLB)).1 (by
      rw [cls_div hT hP.isLB, cls_tens hP.isLB hB]; abel)) t (secToPow b n)
  rw [nonzeroLocus_secToPow b hn] at ht'
  have hL := pull_isLB (isLB_lbPow hT n) p'
  obtain ⟨r, hr, H⟩ := exists_sec_div hL (pull_isLB hA p) (lbSecPull _ t' p') (fun _ => i) (by
    rw [nonzeroLocus_lbSecPull, ht', lb_pull_U]
    exact fun y hy => hle (h₂ hy.2))
  have hD := LB.isLB_div (isLB_lbPow hω (r * (n * k))) hA
  obtain ⟨s', hs'⟩ := H _ (pull_isLB hD p) (by
    have e' := (cls_eq_iff (pull_isLB hω p) (pull_isLB hω' p')).2 e
    rw [cls_pull hω, cls_pull hω'] at e'
    rw [cls_pull hD, cls_pull (isLB_lbPow hT n), cls_pull hA, cls_div (isLB_lbPow hω _) hA, cls_lbPow hω,
      cls_lbPow hT, cls_tens hP.isLB hB, ek, map_sub, map_nsmul, map_nsmul, map_nsmul, e', smul_smul, smul_smul,
      mul_assoc])
  obtain ⟨s, rfl⟩ := (bijective_lbSecPull p hp _).2 s'
  refine ⟨_, Nat.mul_pos hr (Nat.mul_pos hn hk), s, ?_⟩
  have := hs' (show n₀ ∈ _ by rw [nonzeroLocus_lbSecPull, ht']; exact ⟨hb, h₁⟩)
  rwa [nonzeroLocus_lbSecPull] at this

theorem bijective_app {U N X : Scheme.{0}} [GlobalTheory.IsNormalScheme X] [IsLocallyNoetherian X] (u : U ⟶ N) (p : N ⟶ X)
    [QuasiCompact u] [IsSchemeTheoreticallyDominant u] [UniversallyClosed p] [IsOpenImmersion (u ≫ p)]
    [IsDominant (u ≫ p)] (V : X.Opens) :
    Function.Bijective (p.app V).hom := by
  have : IsDominant p := .of_comp u p
  have : IsSchemeTheoreticallyDominant p := .of_isDominant p
  refine ⟨p.app_injective V, fun t => mem_range_app_of_forall_isAffineOpen p V t fun W hW _ => ?_⟩
  generalize N.presheaf.map _ t = t
  have ht : (p.app W).hom.IsIntegralElem t := GenPush.isIntegral_app_of_universallyClosed p W hW t
  have hs : ((u ≫ p).app W).hom.IsIntegralElem (u.app (p ⁻¹ᵁ W) t) := by
    change ((u.app (p ⁻¹ᵁ W)).hom.comp (p.app W).hom).IsIntegralElem _
    exact RingHom.IsIntegralElem.map ht _
  obtain ⟨h, hh⟩ := GenPush.exists_app_eq_of_isIntegralElem (u ≫ p) (u ≫ p).denseRange W _ hs
  refine ⟨h, u.app_injective (p ⁻¹ᵁ W) ?_⟩
  rw [← hh]
  rfl

theorem apply_eq_of_apply_eq {U N X X' : Scheme.{0}} [IsReduced N] [X.IsSeparated] (u : U ⟶ N) (p : N ⟶ X)
    (p' : N ⟶ X') [IsDominant u] [IsOpenImmersion (u ≫ p')] (n : N) (w : U) (h : p' n = (u ≫ p') w) :
    p n = (u ≫ p) w := by
  let O : N.Opens := p' ⁻¹ᵁ (u ≫ p').opensRange
  have h₁ : Set.range (O.ι ≫ p') ⊆ Set.range (u ≫ p') := by
    rintro _ ⟨z, rfl⟩
    exact z.2
  have h₂ : Set.range u ⊆ Set.range O.ι := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨u z, z, rfl⟩, rfl⟩
  let q := IsOpenImmersion.lift (u ≫ p') (O.ι ≫ p') h₁
  let u' := IsOpenImmersion.lift O.ι u h₂
  have hq : q ≫ u ≫ p' = O.ι ≫ p' := IsOpenImmersion.lift_fac _ _ _
  have hu : u' ≫ O.ι = u := IsOpenImmersion.lift_fac _ _ _
  have : IsDominant u' := ⟨by
    refine (u.denseRange.preimage O.ι.isOpenEmbedding.isOpenMap).mono ?_
    rintro z ⟨y, hy⟩
    refine ⟨y, O.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hu, hy]⟩
  have hid : u' ≫ q = 𝟙 U := by
    rw [← cancel_mono (u ≫ p'), Category.assoc, hq, reassoc_of% hu, Category.id_comp]
  have key : q ≫ u ≫ p = O.ι ≫ p := ext_of_isDominant u' (by rw [reassoc_of% hid, reassoc_of% hu])
  let z : O.toScheme := (⟨n, w, h.symm⟩ : O)
  have hz : q z = w := (u ≫ p').isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hq]; exact h)
  rw [← hz, ← Scheme.Hom.comp_apply q, key]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem j_s (Y : Model Xo c (RingHom.id c.F)) : Y.j ≫ Y.s = pullback.snd _ _ := by
  have h1 : spMap (RingHom.id c.F) = 𝟙 _ := by
    unfold spMap; rw [CommRingCat.ofHom_id, Spec.map_id]
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over, h1, Category.comp_id]

theorem exists_common_modification (hE : GlobalTheory.Published.SemiAbelianHomExtension) (Y Y' : Model Xo c (RingHom.id c.F))
    (hY : (FlagMod.detOm Y).IsLB) (hY' : (FlagMod.detOm Y').IsLB) :
    ∃ (N : Scheme.{0}) (_ : CompactSpace N) (_ : QuasiSeparatedSpace N) (u : Xo.XF c ⟶ N) (p : N ⟶ Y.X) (p' : N ⟶ Y'.X),
      u ≫ p = Y.j ∧ u ≫ p' = Y'.j ∧ (∀ V, Function.Bijective (p.app V).hom) ∧ (∀ n w, p' n = Y'.j w → p n = Y.j w) ∧
      LBIso ((FlagMod.detOm Y).pull p) ((FlagMod.detOm Y').pull p') := by
  have := c.fin
  have := Y.flat
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y'.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  have : AlgebraicGeometry.IsNoetherian Y.X := {}
  have := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have : Y.X.IsSeparated := ⟨by rw [← terminal.comp_from Y.s]; infer_instance⟩
  have : IsDominant Y.j := ⟨LogKS.dense_interior Y⟩
  have : QuasiCompact Y.j := inferInstance
  have : GlobalTheory.IsNormalScheme (Xo.XF c) := GlobalTheory.IsNormalScheme.of_isIso_stalkMap Y.j
  have : IsLocallyNoetherian (Xo.XF c) := isLocallyNoetherian_of_isOpenImmersion Y.j
  let f : Xo.XF c ⟶ pullback Y.s Y'.s := pullback.lift Y.j Y'.j ((j_s Y).trans (j_s Y').symm)
  have hf₁ : f ≫ pullback.fst Y.s Y'.s = Y.j := pullback.lift_fst _ _ _
  have hf₂ : f ≫ pullback.snd Y.s Y'.s = Y'.j := pullback.lift_snd _ _ _
  have : IsImmersion (f ≫ pullback.fst Y.s Y'.s) := hf₁ ▸ inferInstance
  have : QuasiCompact (f ≫ pullback.fst Y.s Y'.s) := hf₁ ▸ inferInstance
  have : IsImmersion f := .of_comp f (pullback.fst Y.s Y'.s)
  have : QuasiCompact f := .of_comp f (pullback.fst Y.s Y'.s)
  have : Flat (f ≫ pullback.fst Y.s Y'.s ≫ Y.s) := by
    rw [reassoc_of% hf₁]; infer_instance
  have : IsFinite f.fromNormalization := AmpUniq.isFinite_fromNormalization_graph f (pullback.fst Y.s Y'.s ≫ Y.s)
  let u := f.toNormalization
  let p := f.fromNormalization ≫ pullback.fst Y.s Y'.s
  let p' := f.fromNormalization ≫ pullback.snd Y.s Y'.s
  have hu₁ : u ≫ p = Y.j := by simp [u, p, hf₁]
  have hu₂ : u ≫ p' = Y'.j := by simp [u, p', hf₂]
  have : IsOpenImmersion u := inferInstance
  have hN := GlobalTheory.IsNormalScheme.pred f.normalization
  have : IsLocallyNoetherian f.normalization := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace f.normalization := QuasiCompact.compactSpace_of_compactSpace p
  have : AlgebraicGeometry.IsNoetherian f.normalization := {}
  have : IsOpenImmersion (u ≫ p) := hu₁ ▸ inferInstance
  have : IsDominant (u ≫ p) := hu₁ ▸ inferInstance
  have : IsOpenImmersion (u ≫ p') := hu₂ ▸ inferInstance
  refine ⟨f.normalization, inferInstance, inferInstance, u, p, p', hu₁, hu₂, bijective_app u p,
    fun n w h => hu₁ ▸ apply_eq_of_apply_eq u p p' n w (hu₂ ▸ h), ?_⟩
  obtain ⟨_, _, _, _, _, n₁, -⟩ := sabPull Out.CubePf.cubePull p Y.t
  obtain ⟨_, _, _, _, _, n₂, -⟩ := sabPull Out.CubePf.cubePull p' Y'.t
  obtain ⟨m₀, -⟩ := ObjMaps.exists_sab_cancel (g := 𝟙 _) Y'.m0.toSABMap
    (by rw [Category.id_comp]; exact Y.m0.toSABMap : SABMap Y.oF.t Xo.univ.t (𝟙 _ ≫ pullback.fst _ _))
  obtain ⟨m₂, -⟩ := ObjMaps.exists_sab_comp Y'.m m₀
  obtain ⟨a₁, -⟩ := ObjMaps.exists_sab_cancel n₁ (hu₁ ▸ Y.m : SABMap Y.oF.t Y.t (u ≫ p))
  obtain ⟨a₂, -⟩ := ObjMaps.exists_sab_cancel n₂
    ((((Category.id_comp _).trans hu₂.symm : 𝟙 _ ≫ Y'.j = u ≫ p')) ▸ m₂ : SABMap Y.oF.t Y'.t (u ≫ p'))
  obtain ⟨e, ⟨_, -⟩, -⟩ := hE.existsUnique_iso_of_extensions hN (IsSemiAbelian.pullback p Y.t.G Y.t.semi)
    (IsSemiAbelian.pullback p' Y'.t.G Y'.t.semi) a₁.cart a₂.cart
  have h₂ := ((isGrpPullback_of_iso e).comp n₂.cart).congr (Category.id_comp _) rfl
  have hdet := PolExt.lbIso_detLie_pull (G := (Over.pullback p).obj Y.t.G) n₁.cart h₂ fun U U' hU hU' =>
    (PolExt.isAffineOpen_snd_inf_fst Y.s Y'.s hU' hU).preimage f.fromNormalization
  have hL : (FlagMod.detLie Y).IsLB :=
    FlagMod.isLB_of_ev _ hY.cover fun i j k _ _ z => FlagMod.ev_detChg_mul i j k z
  have hL' : (FlagMod.detLie Y').IsLB :=
    FlagMod.isLB_of_ev _ hY'.cover fun i j k _ _ z => FlagMod.ev_detChg_mul i j k z
  have e₁ := (cls_eq_iff (pull_isLB hL p) (pull_isLB hL' p')).2 hdet
  rw [cls_pull hL, cls_pull hL'] at e₁
  refine (cls_eq_iff (pull_isLB hY p) (pull_isLB hY' p')).1 ?_
  rw [cls_pull hY, cls_pull hY', show cls _ hY = _ from cls_dual hL hY, show cls _ hY' = _ from cls_dual hL' hY',
    map_neg, map_neg, e₁]

end GlobalTheory.HodgeDominates
