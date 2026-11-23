import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpLawAndUnitAgreeOfOpenInDescentModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldPt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLawAbelianSchemeProperClosure
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsCommMonObjOfDominant

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.UnionFib

theorem exists_ringHom_extend {A R Ω : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [Field Ω]
    [IsAlgClosed Ω] (φ : A →+* R) [IsLocalHom φ] (hφ : ((residue R).comp φ).Finite) (ψ : A →+* Ω) [IsLocalHom ψ] :
    ∃ u : R →+* Ω, u.comp φ = ψ := by
  letI : Algebra (ResidueField A) (ResidueField R) := (ResidueField.map φ).toAlgebra
  letI : Algebra (ResidueField A) Ω := (ResidueField.lift ψ).toAlgebra
  have hf : (ResidueField.map φ).Finite := by
    rw [← ResidueField.map_comp_residue] at hφ
    exact RingHom.Finite.of_comp_finite hφ
  haveI : Module.Finite (ResidueField A) (ResidueField R) := hf
  let l : ResidueField R →ₐ[ResidueField A] Ω := IsAlgClosed.lift
  refine ⟨l.toRingHom.comp (residue R), RingHom.ext fun a => ?_⟩
  exact l.commutes (residue A a)

theorem exists_geom_lift {X S : Scheme.{0}} {j : X ⟶ S} {A : Over X} [GrpObj A] {x : S} (C : Chart j A x) (Ω : Type)
    [Field Ω] [IsAlgClosed Ω] (p : Sp Ω ⟶ S) (hp : p (closedPoint Ω) = x) : ∃ q : Sp Ω ⟶ Sp C.R, q ≫ C.ξ = p := by
  obtain ⟨ψ, hl, hψ⟩ : ∃ ψ : S.presheaf.stalk (C.ξ (closedPoint C.R)) ⟶ CommRingCat.of Ω,
      IsLocalHom ψ.hom ∧ Spec.map ψ ≫ S.fromSpecStalk _ = p := by
    rw [C.centre, ← hp]
    exact ⟨Scheme.stalkClosedPointTo p, inferInstance, Scheme.Spec_stalkClosedPointTo_fromSpecStalk p⟩
  obtain ⟨u, hu⟩ := exists_ringHom_extend (Scheme.stalkClosedPointTo C.ξ).hom C.etc.2.2 ψ.hom
  refine ⟨spMap u, ?_⟩
  have e : Scheme.stalkClosedPointTo C.ξ ≫ CommRingCat.ofHom u = ψ := CommRingCat.hom_ext hu
  rw [← hψ, ← e, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

theorem isPullback_of_mono {A P G S X : Scheme.{0}} {i : A ⟶ P} {a : A ⟶ S} {p : P ⟶ X} {j : S ⟶ X} (κ : G ⟶ P)
    [Mono κ] {e : A ⟶ G} (h : IsPullback i a p j) (he : e ≫ κ = i) : IsPullback e a (κ ≫ p) j := by
  have w : e ≫ κ ≫ p = a ≫ j := by rw [← h.w, ← he, Category.assoc]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => h.lift (s.fst ≫ κ) s.snd (by rw [Category.assoc]; exact s.condition))
    (fun s => ?_) (fun s => h.lift_snd _ _ _) (fun s t h₁ h₂ => ?_)⟩⟩
  · rw [← cancel_mono κ, Category.assoc, he]
    exact h.lift_fst _ _ _
  · apply h.hom_ext
    · rw [h.lift_fst, ← h₁, Category.assoc, he]
    · rw [h.lift_snd, h₂]

variable {σ : Setup} (E : Emb σ)

theorem rho_closedPoint (x : Sp σ.R) : spMap (σ.ρ x) (closedPoint _) = x := by
  rw [← σ.hρ]; exact (σ.C x).centre

theorem range_subset : Set.range E.ιA ⊆ E.U := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨v, h1, h2⟩ := Scheme.exists_preimage_of_isPullback (σ.cart ((σ.A.hom ≫ awayMap σ.f) a)) a (closedPoint _)
    (rho_closedPoint _).symm
  refine ⟨_, (σ.V _).ι v, h2, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← E.onV, Scheme.Hom.comp_apply, h1]

theorem isPullback_chart (hC : σ.Common) {G : Scheme.{0}} (κ : G ⟶ E.P) [IsOpenImmersion κ] (hκ : Set.range κ = E.U)
    (x : Sp σ.R) : ∃ m : (σ.C x).G.left ⟶ G, m ≫ κ = E.emb x ∧
      IsPullback m (σ.C x).G.hom (κ ≫ E.p) (spMap (σ.ρ x)) := by
  obtain ⟨w, hw⟩ := E.openIn x
  let l := pullback.lift (E.emb x) (σ.C x).G.hom w
  have l1 : l ≫ pullback.fst _ _ = E.emb x := pullback.lift_fst _ _ _
  have l2 : l ≫ pullback.snd _ _ = (σ.C x).G.hom := pullback.lift_snd _ _ _
  have hr : Set.range (E.emb x) ⊆ Set.range κ := by
    rintro _ ⟨y, rfl⟩
    have e1 : pullback.fst E.p (spMap (σ.ρ x)) (l y) = E.emb x y := by rw [← Scheme.Hom.comp_apply, l1]
    rw [hκ, ← e1]
    exact (Emb.fst_mem_U_iff σ E hC x (l y)).2 ⟨y, e1.symm, by rw [← Scheme.Hom.comp_apply, l2]⟩
  refine ⟨IsOpenImmersion.lift κ _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  have sq : IsPullback (IsOpenImmersion.lift κ _ hr) l κ (pullback.fst E.p (spMap (σ.ρ x))) := by
    refine IsOpenImmersion.isPullback _ _ _ _ (by rw [l1, IsOpenImmersion.lift_fac]) ?_
    ext z
    constructor
    · intro hz
      have hz' : pullback.fst E.p (spMap (σ.ρ x)) z ∈ E.U := hκ ▸ hz
      obtain ⟨x', y', hy', e⟩ := hz'
      obtain ⟨Ω, _, s, t', o, hst, hs, ht⟩ :=
        Sat.exists_field_pt (pullback.fst E.p (spMap (σ.ρ x))) (E.emb x') z y' e.symm
      obtain ⟨w', -⟩ := E.openIn x'
      obtain ⟨t, h1, h2⟩ := (Sat.transfer σ E hC x x' Ω (s ≫ pullback.snd _ _) (t' ≫ (σ.C x').G.hom) o
        (by rw [Scheme.Hom.comp_apply, ht]; exact hy')
        (by rw [Category.assoc, Category.assoc, ← pullback.condition, ← w', reassoc_of% hst])).2 t' rfl
      have : t ≫ l = s := by
        apply pullback.hom_ext
        · rw [Category.assoc, l1, h2, hst]
        · rw [Category.assoc, l2, h1]
      exact ⟨t o, by rw [← Scheme.Hom.comp_apply, this, hs]⟩
    · rintro ⟨y, rfl⟩
      exact hr ⟨y, by rw [← Scheme.Hom.comp_apply, l1]⟩
  have := sq.paste_vert (IsPullback.of_hasPullback E.p (spMap (σ.ρ x)))
  rwa [l2] at this

theorem alpha_comp (x : Sp σ.R) :
    (σ.C x).α ≫ E.ιA = pullback.fst (σ.C x).G.hom (jK (σ.C x).R) ≫ E.emb x := by
  have hr : Set.range (pullback.fst (σ.C x).G.hom (jK (σ.C x).R)) ⊆ Set.range (σ.V x).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine (σ.hV x _).2 ?_
    have e : spMap (σ.ρ x) ((σ.C x).G.hom (pullback.fst (σ.C x).G.hom (jK (σ.C x).R) z)) =
        awayMap σ.f ((σ.C x).y (pullback.snd (σ.C x).G.hom (jK (σ.C x).R) z)) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        pullback.condition_assoc, (σ.C x).hy, σ.hρ]
    intro hm
    have h1 : σ.f ∈ (spMap (σ.ρ x) ((σ.C x).G.hom (pullback.fst (σ.C x).G.hom (jK (σ.C x).R) z))).asIdeal := hm
    rw [e] at h1
    have h2 : algebraMap σ.R (Localization.Away σ.f) σ.f ∈
      ((σ.C x).y (pullback.snd (σ.C x).G.hom (jK (σ.C x).R) z)).asIdeal := h1
    exact (PrimeSpectrum.isPrime _).ne_top (Ideal.eq_top_of_isUnit_mem _ h2 (IsLocalization.Away.algebraMap_isUnit σ.f))
  have h := σ.compat x _ (𝟙 _) (IsOpenImmersion.lift (σ.V x).ι _ hr)
    (by rw [Category.id_comp, IsOpenImmersion.lift_fac])
  rw [Category.id_comp] at h
  rw [h, Category.assoc, E.onV, IsOpenImmersion.lift_fac_assoc]

theorem isSemiAbelian_of_ext (hC : σ.Common) (G : Over (Sp σ.R)) [GrpObj G] (κ : G.left ⟶ E.P) [IsOpenImmersion κ]
    (hκ : Set.range κ = E.U) (hG : G.hom = κ ≫ E.p) [Smooth G.hom] [QuasiCompact G.hom] {e : σ.A.left ⟶ G.left}
    (he : e ≫ κ = E.ιA) (h : IsGrpPullback σ.A G (awayMap σ.f) e) : IsSemiAbelian G := by
  have := E.sep
  have hsep : IsSeparated G.hom := by rw [hG]; infer_instance
  have key : ∀ x, ∃ m, IsGrpPullback (σ.C x).G G (σ.C x).ξ m := fun x => by
    obtain ⟨m, hm, sq⟩ := isPullback_chart E hC κ hκ x
    rw [← hG, ← σ.hρ] at sq
    obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing (σ.C x).R (FractionRing (σ.C x).R)
    have := (σ.C x).semi.smooth
    refine ⟨m, ZJ.isGrpPullback_of_dominant (jK (σ.C x).R) sq (((σ.C x).gen.comp h).congr (σ.C x).hy ?_)⟩
    rw [← cancel_mono κ, Category.assoc, Category.assoc, he, hm]
    exact alpha_comp E x
  have fib : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Sp Ω ⟶ Sp σ.R), ∃ (x : Sp σ.R) (q : Sp Ω ⟶ Sp (σ.C x).R)
      (i : (Over.pullback q).obj (σ.C x).G ≅ (Over.pullback p).obj G), IsMonHom i.hom := fun Ω _ _ p => by
    obtain ⟨q, hq⟩ := exists_geom_lift (σ.C (p (closedPoint Ω))) Ω p rfl
    obtain ⟨m, hm⟩ := key (p (closedPoint Ω))
    obtain ⟨i, hi, -⟩ := grpPullback_iso (((isGrpPullback_pullback _ q).comp hm).congr hq rfl)
      (isGrpPullback_pullback G p)
    exact ⟨_, q, i, hi⟩
  refine ⟨?_, ‹_›, hsep, ‹_›, SemiAbelianCompare.geometricallyConnected_of_isAlgClosed _ fun Ω _ _ p => ?_,
    fun Ω _ _ p => ?_⟩
  · have := σ.ab.comm
    have : IsSchemeTheoreticallyDominant (awayMap σ.f) :=
      ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _
        (IsLocalization.injective (Localization.Away σ.f) (powers_le_nonZeroDivisors_of_noZeroDivisors σ.hf))
    exact SplitExtComm.isCommMonObj_of_dominant h
  · obtain ⟨x, q, i, -⟩ := fib Ω p
    have := (σ.C x).semi.geomConnected
    have : ConnectedSpace ((Over.pullback q).obj (σ.C x).G).left :=
      GeometricallyConnected.geometrically_connectedSpace (f := (σ.C x).G.hom) q _ _ (IsPullback.of_hasPullback _ _)
    have := isIso_inv_left i.symm
    exact (i.symm.inv.left).surjective.connectedSpace (i.symm.inv.left).continuous
  · obtain ⟨x, q, i, hi⟩ := fib Ω p
    obtain ⟨T⟩ := (σ.C x).semi.fibres Ω q
    exact ⟨torusExtOfIso i T⟩

end GlobalTheory.Desc.UnionFib

namespace GlobalTheory.Desc

open UnionFib GroupGlue in

theorem Emb.hasExt_of_locGrp : ∀ (σ : Setup) (E : Emb σ), σ.Common → (∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ Set.range h = E.U ∩ E.p ⁻¹' {z : Sp σ.R | g ∉ z.asIdeal}) → HasExt (awayMap σ.f) σ.A := by
  intro σ E hC hloc
  choose g hg H iH h hL hr using hloc
  have oi : ∀ x, IsOpenImmersion (h x) := fun x => (hL x).2.2.1
  have ra : ∀ a : σ.R, Set.range (awayMap a) = {z : Sp σ.R | a ∉ z.asIdeal} := fun a =>
    PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
  have hU : IsOpen E.U := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    exact ⟨Set.range (h (E.p z)), by rw [hr]; exact Set.inter_subset_left, (h _).isOpenEmbedding.isOpen_range,
      by rw [hr]; exact ⟨hz, hg _⟩⟩
  let U : E.P.Opens := ⟨E.U, hU⟩
  have hι : Set.range U.ι = E.U := Scheme.Opens.range_ι U
  let G : Over (Sp σ.R) := Over.mk (U.ι ≫ E.p)
  let 𝒰 : (Sp σ.R).OpenCover := Scheme.Cover.mkOfCovers (Sp σ.R) (fun x => Sp (Localization.Away (g x)))
    (fun x => awayMap (g x)) (fun x => by
      obtain ⟨y, hy⟩ : x ∈ Set.range (awayMap (g x)) := by rw [ra]; exact hg x
      exact ⟨x, y, hy⟩)
  have hs : ∀ x, Set.range (h x) ⊆ Set.range U.ι := fun x => by rw [hι, hr]; exact Set.inter_subset_left
  let H' : ∀ i : 𝒰.I₀, Over (𝒰.X i) := H
  letI iH' : ∀ i : 𝒰.I₀, GrpObj (H' i) := iH
  let ψ : ∀ i : 𝒰.I₀, (H' i).left ⟶ G.left := fun x => IsOpenImmersion.lift U.ι (h x) (hs x)
  have hψι : ∀ x : Sp σ.R, ψ x ≫ U.ι = h x := fun x => IsOpenImmersion.lift_fac _ _ _
  have hψ : ∀ i, IsPullback (ψ i) (H' i).hom G.hom (𝒰.f i) := fun (x : Sp σ.R) => by
    have : IsOpenImmersion (ψ x ≫ U.ι) := by rw [hψι]; exact oi x
    have : IsOpenImmersion (ψ x) := IsOpenImmersion.of_comp _ U.ι
    refine (IsOpenImmersion.isPullback (H x).hom (ψ x) (awayMap (g x)) (U.ι ≫ E.p) ?_ ?_).flip
    · rw [reassoc_of% (hψι x)]; exact (hL x).2.2.2.1
    · ext z
      constructor
      · intro hz
        have hz' : E.p (U.ι z) ∈ Set.range (awayMap (g x)) := hz
        rw [ra] at hz'
        obtain ⟨y, hy⟩ : U.ι z ∈ Set.range (h x) := by rw [hr]; exact ⟨z.2, hz'⟩
        refine ⟨y, U.ι.isOpenEmbedding.injective ?_⟩
        rw [← hy, ← hψι]; rfl
      · rintro ⟨y, rfl⟩
        refine ⟨(H x).hom y, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← (hL x).2.2.2.1, ← hψι]; rfl
  have op : ∀ x, OpenIn (h x) (H x).hom E.p (awayMap (g x)) := fun x => by
    refine ⟨(hL x).2.2.2.1, ?_⟩
    have : IsOpenImmersion (pullback.lift (h x) (H x).hom (hL x).2.2.2.1 ≫ pullback.fst _ _) := by
      rw [pullback.lift_fst]; exact oi x
    exact IsOpenImmersion.of_comp _ (pullback.fst E.p (awayMap (g x)))
  have hm : MulCompat ψ := fun (x y : Sp σ.R) S u v a a' b b' e₁ e₂ => by
    have := (hL x).1
    have := (hL y).1
    have k := (GlobalTheory.T.grpLaw_and_unit_agree_of_openIn_descentModel σ E _ _ (awayMap (g x)) (awayMap (g y)) (H x) (H y) (h x) (h y) inferInstance inferInstance
      inferInstance inferInstance (op x) (op y) (hL x).2.2.2.2 (hL y).2.2.2.2).1 S u v a a' b b'
      (by rw [← hψι, ← hψι, reassoc_of% e₁]) (by rw [← hψι, ← hψι, reassoc_of% e₂])
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hψι, hψι]
    exact k
  obtain ⟨iG, hG⟩ := exists_grpObj hm hψ
  have hA : Set.range E.ιA ⊆ Set.range U.ι := by rw [hι]; exact range_subset E
  let e : σ.A.left ⟶ G.left := IsOpenImmersion.lift U.ι _ hA
  have he : e ≫ U.ι = E.ιA := IsOpenImmersion.lift_fac _ _ _
  have hp : IsGrpPullback σ.A G (awayMap σ.f) e := by
    refine ⟨isPullback_of_mono U.ι E.cartA he, fun T a b a₀ b₀ ha hb => ?_⟩
    refine ext_small 𝒰 (T.hom ≫ awayMap σ.f) fun (x : Sp σ.R) S k u hu => ?_
    obtain ⟨c, hc⟩ := exists_rep hψ (T := Over.mk (T.hom ≫ awayMap σ.f)) hu a₀
    obtain ⟨d, hd⟩ := exists_rep hψ (T := Over.mk (T.hom ≫ awayMap σ.f)) hu b₀
    rw [← rep_mul hG (T := Over.mk (T.hom ≫ awayMap σ.f)) hu hc hd]
    let r : Over.mk (k ≫ T.hom) ⟶ T := Over.homMk k rfl
    have k' := (hL x).2.2.2.2 S u (k ≫ T.hom) c d (r ≫ a) (r ≫ b)
      (by rw [← hψι, reassoc_of% hc, ha, ← he]; simp [r]) (by rw [← hψι, reassoc_of% hd, hb, ← he]; simp [r])
    rw [← MonObj.comp_mul] at k'
    rw [← cancel_mono U.ι, Category.assoc, hψι, Category.assoc, Category.assoc, he]
    exact k'.trans (Category.assoc _ _ _)
  have : IsZariskiLocalAtTarget @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
  have : IsZariskiLocalAtTarget @QuasiCompact.{0} := by
    set_option backward.isDefEq.respectTransparency.types false in exact inferInstance
  have : Smooth G.hom := of_charts @Smooth hψ fun x => (hL x).1
  have : QuasiCompact G.hom := of_charts @QuasiCompact hψ fun x => (hL x).2.1
  exact ⟨G, iG, e, isSemiAbelian_of_ext E hC G U.ι hι rfl he hp, hp⟩

end GlobalTheory.Desc
