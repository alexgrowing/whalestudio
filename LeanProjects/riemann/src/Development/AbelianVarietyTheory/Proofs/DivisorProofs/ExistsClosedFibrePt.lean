import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupNonzeroLocusEmbH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToProjSecPullOfSval
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb.ThetaPt

theorem exists_trait_pt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (x : M.S),
    M.π x = closedPoint R → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W)
      (ξ : Sp W ⟶ M.S), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧
      ξ (closedPoint W) = x := by
  intro R _ _ _ hR M x hx
  obtain ⟨⟨hRn, -, -, -⟩, hR0⟩ := hR
  haveI := M.integral
  haveI := M.proper
  haveI : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  let A := M.S.presheaf.stalk x
  let ψc : CommRingCat.of R ⟶ A :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ M.π.appTop ≫ M.S.presheaf.germ ⊤ x trivial
  have hcomp : M.S.fromSpecStalk x ≫ M.π = Spec.map ψc := by
    simp only [ψc]
    rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hπinj : Function.Injective M.π.appTop.hom := fun a b h => GlobalTheory.Mum.jK_appTop_injective R (by
    rw [← M.appTop_comp, ← M.appTop_comp, h])
  have hψi : Function.Injective ψc.hom := by
    simp only [ψc, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (germ_injective_of_isIntegral M.S (U := ⊤) x trivial).comp
      (hπinj.comp (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective)
  have hψl : IsLocalHom ψc.hom := by
    refine ((IsLocalRing.local_hom_TFAE ψc.hom).out 0 4).2 ?_
    have e1 : (Spec.map ψc) (closedPoint A) = closedPoint R := by
      have h0 := congrArg M.π (Scheme.fromSpecStalk_closedPoint (x := x))
      rw [hx] at h0
      rw [← hcomp]
      exact h0
    exact congrArg PrimeSpectrum.asIdeal e1
  haveI : CharZero A := charZero_of_injective_ringHom hψi
  obtain ⟨V, _, _, _, φ₀, hV, hφ₀i, hφ₀l⟩ : ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V)
      (φ₀ : A →+* V), GlobalTheory.LN.CDvr V ∧ Function.Injective φ₀ ∧ IsLocalHom φ₀ := by
    by_cases h : IsField A
    · letI := h.toField
      refine ⟨PowerSeries A, inferInstance, inferInstance, inferInstance, PowerSeries.C, ⟨inferInstance, ?_, ?_⟩,
        PowerSeries.C_injective, inferInstance⟩
      · rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
      · exact charZero_of_injective_ringHom (f := PowerSeries.C (R := A)) PowerSeries.C_injective
    · obtain ⟨O, _, _, _, _, φ, h1, h2⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating A h
      exact ⟨O, inferInstance, inferInstance, inferInstance, φ,
        ⟨inferInstance, inferInstance, charZero_of_injective_ringHom h1⟩, h1, h2⟩
  refine ⟨V, inferInstance, inferInstance, inferInstance, φ₀.comp ψc.hom, spMap φ₀ ≫ M.S.fromSpecStalk x, hV,
    hφ₀i.comp hψi, RingHom.isLocalHom_comp _ _, ?_, ?_⟩
  · rw [Category.assoc, hcomp]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom]
  · exact (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (M.S.fromSpecStalk x) (IsLocalRing.comap_closedPoint φ₀)) Scheme.fromSpecStalk_closedPoint)

theorem isLocalHom_of_finite {W W' : Type} [CommRing W] [IsLocalRing W] [CommRing W'] [IsLocalRing W']
    (io : W →+* W') (hf : io.Finite) : IsLocalHom io := by
  letI := io.toAlgebra
  haveI : Module.Finite W W' := hf
  have hmax : (maximalIdeal W').comap (algebraMap W W') = maximalIdeal W :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal W'))
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have : a ∈ (maximalIdeal W').comap (algebraMap W W') := hmax ▸ (IsLocalRing.mem_maximalIdeal a).2 h
  exact (IsLocalRing.mem_maximalIdeal _).1 (Ideal.mem_comap.1 this) ha

theorem exists_closedFibre_pt {W W' : Type} [CommRing W] [IsLocalRing W] [CommRing W'] [IsLocalRing W']
    (io : W →+* W') [IsLocalHom io] {S : Scheme.{0}} (G : Over S) (G' : Over (Sp W')) (ξ : Sp W ⟶ S)
    (β : G'.left ⟶ G.left) (h : IsPullback β G'.hom G.hom (spMap io ≫ ξ)) (g : G.left)
    (hg : G.hom g = ξ (closedPoint W)) :
    ∃ q : ((Over.pullback (spMap (residue W'))).obj G').left, (pullback.fst G'.hom (spMap (residue W')) ≫ β) q = g := by
  have h1 : (spMap io) (closedPoint W') = closedPoint W := IsLocalRing.comap_closedPoint io
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := spMap io ≫ ξ) g
    (closedPoint W') (by rw [hg]; exact (congrArg ξ h1).symm)
  have hg1 : β (h.isoPullback.inv z) = g := by
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz1]
  have hg2 : G'.hom (h.isoPullback.inv z) = closedPoint W' := by
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hz2]
  have h2 : (spMap (residue W')) (closedPoint (ResidueField W')) = closedPoint W' :=
    IsLocalRing.comap_closedPoint (residue W')
  obtain ⟨q, hq1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G'.hom) (g := spMap (residue W'))
    (h.isoPullback.inv z) (closedPoint _) (hg2.trans h2.symm)
  exact ⟨q, by rw [Scheme.Hom.comp_apply, hq1, hg1]⟩

theorem toProj_congr {R : Type} [CommRing R] {M : ℕ} {Y : Scheme.{0}} {L : LB Y} {f f' : Y ⟶ Sp R}
    (e : f = f') (s : Fin (M + 1) → L.Sec) (hs hs' : ⨆ i, nonzeroLocus (s i) = ⊤) :
    GlobalTheory.ProjSpace.toProj f s hs = GlobalTheory.ProjSpace.toProj f' s hs' := by
  subst e; rfl

theorem mem_basicOpen_theta : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (G : Over M.S) [GrpObj G],
    IsSemiAbelian G → ∀ (B L : LB G.left), B.IsLB → L.IsLB → ∀ (N : ℕ) (s : Fin (N + 1) → B.Sec) (θ : L.Sec)
    (Y : Over (Sp (ResidueField R))) [GrpObj Y], Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N),
    j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → IsImmersion j → ∀ (O : Y.left.Opens),
    GlobalTheory.Mum.SecEmb.TraitRed M G s θ Y j O →
    ∀ (g : (GlobalTheory.Mum.SecEmb.embH s).toScheme) (y : Y.left), y ∈ O →
    M.π (G.hom ((GlobalTheory.Mum.SecEmb.embH s).ι g)) = closedPoint R → GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s g = j y →
    ∃ i : L.ι, (GlobalTheory.Mum.SecEmb.embH s).ι g ∈ G.left.basicOpen (θ.f i) := by
  intro R _ _ _ hR M G _ hG B L hB hL N s θ Y _ hY j hj hji O hT g y hy hgc hgj
  obtain ⟨W, _, _, _, φ, ξ, hW, hφi, hφl, hξ, hξx⟩ := exists_trait_pt R hR M _ hgc
  obtain ⟨W', _, _, _, io, G', _, β, κ, e, hW', hio, hiof, hpb, hκ, he, H⟩ := hT W hW φ ξ hφi hφl hξ
  haveI := isLocalHom_of_finite io hiof
  obtain ⟨q, hq⟩ := exists_closedFibre_pt io G G' ξ β hpb.1 _ hξx.symm
  let Ω : Type := (((Over.pullback (spMap (residue W'))).obj G').left).residueField q
  let p : Sp Ω ⟶ ((Over.pullback (spMap (residue W'))).obj G').left :=
    (((Over.pullback (spMap (residue W'))).obj G').left).fromSpecResidueField q
  haveI : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  obtain ⟨p', hp'⟩ : ∃ p', p' = p ≫ pullback.fst G'.hom (spMap (residue W')) := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y', y' = p ≫ e.hom.left ≫ pullback.fst Y.hom (spMap κ) := ⟨_, rfl⟩
  obtain ⟨⟨hs, hproj⟩, hnz⟩ := H Ω p p' y' hp' hy'
  let pt : Sp Ω := closedPoint Ω
  have hpt : ∀ z : Sp Ω, z = pt := fun z => Subsingleton.elim _ _
  have hppt : p pt = q := Scheme.fromSpecResidueField_apply q pt
  have hg' : (p' ≫ β) pt = (embH s).ι g := by
    rw [hp', Category.assoc, Scheme.Hom.comp_apply, hppt]
    exact hq
  have hrange : Set.range (p' ≫ β) ⊆ Set.range (embH s).ι := by
    rintro _ ⟨z, rfl⟩
    rw [hpt z, hg']
    exact ⟨g, rfl⟩
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : Sp Ω ⟶ (embH s).toScheme, l₀ ≫ (embH s).ι = p' ≫ β :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
  have hl₀pt : l₀ pt = g := by
    apply (embH s).ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hl₀, hg']
  obtain ⟨-, hs2, e2⟩ := GlobalTheory.Mum.toProj_secPull_of_gs (Z := Sp Ω) s (fun i => GlobalTheory.secPull (s i) (embH s).ι)
    ((embH s).ι ≫ G.hom ≫ M.π) (iSup_nonzeroLocus_embH s) (p' ≫ β) l₀ (fun z => by
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hB.cover.ge (Set.mem_univ ((p' ≫ β) z)))
      have hla : l₀ z ∈ (B.pull (embH s).ι).U (fun _ => a) := Set.mem_iInter.2 fun _ => by
        show (embH s).ι (l₀ z) ∈ B.U a
        rw [← Scheme.Hom.comp_apply, hl₀]; exact ha
      refine ⟨a, fun _ => a, 1, ha, hla, fun i => ?_⟩
      rw [Units.val_one, _root_.one_mul]
      refine Eq.trans ?_ (GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull B (embH s).ι) (s i) l₀ z (fun _ => a) hla).symm
      rw [hl₀]; rfl)
  have hstr : p' ≫ G'.hom ≫ spMap (io.comp φ) = l₀ ≫ (embH s).ι ≫ G.hom ≫ M.π := by
    have hw : β ≫ G.hom ≫ M.π = G'.hom ≫ spMap io ≫ ξ ≫ M.π := by
      rw [← Category.assoc, hpb.1.w]; simp only [Category.assoc]
    have hc : spMap (io.comp φ) = spMap io ≫ spMap φ := by
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [reassoc_of% hl₀, hw, hξ, hc]
  have key : y' ≫ j = l₀ ≫ embF (G.hom ≫ M.π) s := by
    rw [← hproj, toProj_congr hstr _ hs hs2]
    exact e2
  have hyy : y' pt = y := by
    apply hji.isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, key, Scheme.Hom.comp_apply, hl₀pt, hgj]
  have hθ := hnz pt (hyy ▸ hy)
  rw [hg'] at hθ
  exact TopologicalSpace.Opens.mem_iSup.1 hθ

end GlobalTheory.Mum.SecEmb.ThetaPt

end
