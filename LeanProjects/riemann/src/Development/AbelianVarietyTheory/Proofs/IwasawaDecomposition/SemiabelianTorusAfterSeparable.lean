import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoveringAndSmoothnessIffOfSeparableSplitting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothTorusQuotientOfGoodOpenCover
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDvrTorusExtensionSpecialFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackKernelBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableOfSurjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS GlobalTheory.UU GlobalTheory.TorusGrading GlobalTheory.TorusQuotientLift GlobalTheory.SplitTorus

noncomputable section
namespace GlobalTheory.InsepDescent

theorem torus_eq {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over (Sp R)} [GrpObj G] (Q₁ Q₂ : TQ G X) {S₀ : Scheme.{0}}
    [Nonempty S₀] (δ : S₀ ⟶ Sp R) (h : bcMap δ X ≫ Q₁.i.left = bcMap δ X ≫ Q₂.i.left) : Q₁.i = Q₂.i := by
  have := Q₁.i_hom
  have := Q₂.i_hom
  have := Q₁.q_hom
  have := Q₁.isAb.proper
  have : ConnectedSpace (Sp R) := connectedSpace_of_isLocalRing R
  have h₀ := splitTorus_hom_proper_trivial_local R X Q₁.B (Q₂.i ≫ Q₁.q) inferInstance
  have : Mono (η[Q₁.B]) := ⟨fun a b _ => toUnit_unique a b⟩
  have : Mono Q₁.i := Q₁.isKernel.mono_fst_of_mono
  obtain ⟨e, he, -⟩ := Q₁.isKernel.exists_lift Q₂.i (toUnit _) h₀
  have : IsMonHom e := ⟨by rw [← cancel_mono Q₁.i, Category.assoc, he, IsMonHom.one_hom, IsMonHom.one_hom], by
    rw [← cancel_mono Q₁.i, Category.assoc, he, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, he]⟩
  obtain ⟨φ, rfl⟩ := exists_eq_torusMap e
  rw [← he, Over.comp_left, ← Category.assoc, cancel_mono, ← torusMap_bcMap] at h
  have h₁ : torusMap S₀ φ = torusMap S₀ (AddMonoidHom.id X) := by
    rw [torusMap_id]
    refine Over.OverMorphism.ext ((isPullback_bcMap δ X).hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [← h, Over.id_left, Category.id_comp]
  rw [← he, torusMap_injective h₁, torusMap_id, Category.id_comp]

theorem exists_torus {S S' : Scheme.{0}} [Nonempty S'] {f : S' ⟶ S} [Flat f] [Surjective f] [QuasiCompact f]
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {p₁ p₂ : Sp R ⟶ S'} (hp : IsPullback p₁ p₂ f f)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G] {G' : Over S'}
    [GrpObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) (Q : TQ G' X) :
    ∃ i : splitTorus S X ⟶ G, IsMonHom i ∧ TorusCompat f F Q.i i := by
  have HR := isGrpPullback_pullback G (p₁ ≫ f)
  have lift : ∀ p : Sp R ⟶ S', p₁ ≫ f = p ≫ f → ∃ Q' : TQ ((Over.pullback (p₁ ≫ f)).obj G) X,
      Q'.i.left ≫ pullback.fst G.hom (p₁ ≫ f) = bcMap p X ≫ Q.i.left ≫ F := fun p e => by
    have w : pullback.fst G.hom (p₁ ≫ f) ≫ G.hom = pullback.snd G.hom (p₁ ≫ f) ≫ p ≫ f := by
      rw [pullback.condition, e]
    obtain ⟨φ, h₁, h₂⟩ := hF.1.exists_lift _ (pullback.snd G.hom (p₁ ≫ f) ≫ p) (w.trans (Category.assoc _ _ _).symm)
    obtain ⟨Q', hQ'⟩ := exists_tq_baseChange _ _ p X G' _ φ (hF.cancel (HR.congr e h₁.symm) h₂) Q
    refine ⟨Q', ?_⟩
    rw [← Category.assoc, torusCompat_iff.1 hQ', Category.assoc, h₁]
  obtain ⟨Q₁, h₁⟩ := lift p₁ rfl
  obtain ⟨Q₂, h₂⟩ := lift p₂ hp.w
  obtain ⟨δ, d₁, d₂⟩ := hp.exists_lift (𝟙 _) (𝟙 _) rfl
  have e : Q₁.i = Q₂.i := torus_eq Q₁ Q₂ δ (HR.1.hom_ext (by
    rw [Category.assoc, Category.assoc]
    erw [h₁, h₂]
    rw [← Category.assoc, ← Category.assoc _ (bcMap p₂ X), ← bcMap_comp, ← bcMap_comp, d₁, d₂]) (by
    rw [Category.assoc, Category.assoc, Over.w, Over.w]))
  rw [e, h₂] at h₁
  have hT := isPullback_bcMap f X
  have : Flat (bcMap f X) := MorphismProperty.of_isPullback hT.flip ‹Flat f›
  have : Surjective (bcMap f X) := MorphismProperty.of_isPullback hT.flip ‹Surjective f›
  have : QuasiCompact (bcMap f X) := MorphismProperty.of_isPullback hT.flip ‹QuasiCompact f›
  have hc : ∀ {Z : Scheme.{0}} (a b : Z ⟶ (splitTorus S' X).left), a ≫ bcMap f X = b ≫ bcMap f X →
      a ≫ Q.i.left ≫ F = b ≫ Q.i.left ≫ F := by
    intro Z a b h
    obtain ⟨z, z₁, z₂⟩ := hp.exists_lift (a ≫ (splitTorus S' X).hom) (b ≫ (splitTorus S' X).hom) (by
      rw [Category.assoc, Category.assoc, ← hT.w, reassoc_of% h])
    obtain ⟨c, c₁, c₂⟩ := (isPullback_bcMap p₁ X).exists_lift a z z₁.symm
    have c₃ : c ≫ bcMap p₂ X = b := hT.hom_ext
      (by rw [Category.assoc, ← bcMap_comp, ← hp.w, bcMap_comp, reassoc_of% c₁, h])
      (by rw [Category.assoc, bcMap_hom, reassoc_of% c₂, z₂])
    rw [← c₁, ← c₃, Category.assoc, Category.assoc, h₁]
  have hfac := EffectiveEpi.fac (bcMap f X) (Q.i.left ≫ F) hc
  let i : splitTorus S X ⟶ G := Over.homMk (EffectiveEpi.desc (bcMap f X) (Q.i.left ≫ F) hc) (by
    rw [← cancel_epi (bcMap f X), ← Category.assoc, hfac, Category.assoc, hF.1.w, Over.w_assoc, bcMap_hom])
  exact ⟨i, (FieldBaseChange.isMonHom_iff_of_isGrpPullback (isGrpPullback_bcMap f X) hF Q.i i hfac).1 Q.i_hom,
    torusCompat_iff.2 hfac⟩

theorem isLocalRing_tensor (k K : Type) [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K] :
    IsLocalRing (K ⊗[k] K) := by
  have h := (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k K K).bijective
  have : Subsingleton (PrimeSpectrum (K ⊗[k] K)) := h.1.subsingleton
  refine IsLocalRing.of_unique_max_ideal ?_
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[k] K)
  exact ⟨m, hm, fun n hn => congrArg PrimeSpectrum.asIdeal
    (Subsingleton.elim (⟨n, hn.isPrime⟩ : PrimeSpectrum _) ⟨m, hm.isPrime⟩)⟩

theorem universallyInjective_spMap (k K : Type) [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K] :
    UniversallyInjective (spMap (algebraMap k K)) := by
  suffices h : ∀ (L : Type) [Field L],
      Function.Injective (fun g : Spec (.of L) ⟶ Sp K ↦ g ≫ spMap (algebraMap k K)) from
    ((tfae_universallyInjective _).out 1 0).1 h
  intro L _ g₁ g₂ h
  obtain ⟨g₁, rfl⟩ := Spec.map_surjective g₁
  obtain ⟨g₂, rfl⟩ := Spec.map_surjective g₂
  simp only [← Spec.map_comp, Spec.map_inj] at h
  congr 1
  exact CommRingCat.hom_ext (IsPurelyInseparable.injective_comp_algebraMap k K L (congrArg CommRingCat.Hom.hom h))

section Opens

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {G' : Over S'}
  [GrpObj G'] {F : G'.left ⟶ G.left} {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'}

theorem exists_isWt [IsAffine S] [IsAffine S'] (hF : IsGrpPullback G' G f F) (hi : TorusCompat f F i' i)
    {V : G.left.Opens} (hV : IsAffineOpen V) (h : Graded i V) (h' : Graded i' (F ⁻¹ᵁ V)) {χ : X}
    {u : Γ(G'.left, F ⁻¹ᵁ V)} (hu : IsWt i' _ u χ) {x : G'.left} (hx : x ∈ G'.left.basicOpen u) :
    ∃ a : Γ(G.left, V), IsWt i V a χ ∧ F x ∈ G.left.basicOpen a := by
  by_contra! H
  have hxV : x ∈ F ⁻¹ᵁ V := G'.left.basicOpen_le u hx
  let 𝔪 : Ideal Γ(G'.left, F ⁻¹ᵁ V) :=
    (IsLocalRing.maximalIdeal _).comap (G'.left.presheaf.germ (F ⁻¹ᵁ V) x hxV).hom
  have h𝔪 : ∀ w, w ∈ 𝔪 ↔ x ∉ G'.left.basicOpen w := fun w => (G'.left.mem_basicOpen w x hxV).not.symm
  have po := (isIso_pushoutSection_iff hF.1 (US := ⊤) (UT := ⊤) (UX := V) le_top le_top (UY := F ⁻¹ᵁ V) (by simp)).1
    (isIso_pushoutSection_of_isAffineOpen hF.1 _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hV)
  have hm := (CommRingCat.closure_range_union_range_eq_top_of_isPushout po).ge (Subring.mem_top u)
  rw [Subring.mem_closure_iff] at hm
  have key : ∃ a : X →₀ Γ(G'.left, F ⁻¹ᵁ V), (∀ ψ, IsWt i' _ (a ψ) ψ) ∧ a χ ∈ 𝔪 ∧ u = a.sum fun _ y => y := by
    clear hu hx
    induction hm using AddSubgroup.closure_induction with
    | mem w hw =>
      have : ∃ a c, IsWt i' _ c 0 ∧ w = (F.appLE V (F ⁻¹ᵁ V) le_rfl).hom a * c := by
        induction hw using Submonoid.closure_induction with
        | mem w hw =>
          rcases hw with ⟨a, rfl⟩ | ⟨c, rfl⟩
          · exact ⟨a, 1, isWt_one, (_root_.mul_one _).symm⟩
          · exact ⟨1, _, isWt_appLE_of_invariant G'.hom (fun Z t g => by rw [Over.w, Over.w]) ⊤ le_top c,
              by rw [map_one, _root_.one_mul]⟩
        | one => exact ⟨1, 1, isWt_one, by simp⟩
        | mul _ _ _ _ h₁ h₂ =>
          obtain ⟨a, c, hc, rfl⟩ := h₁
          obtain ⟨a', c', hc', rfl⟩ := h₂
          exact ⟨a * a', c * c', _root_.add_zero (0 : X) ▸ hc.mul hc', by rw [map_mul]; ring⟩
      obtain ⟨a, c, hc, rfl⟩ := this
      obtain ⟨d, hd, rfl⟩ := h.1 a
      refine ⟨d.mapRange (fun y => (F.appLE V (F ⁻¹ᵁ V) le_rfl).hom y * c) (by simp), fun ψ => ?_, ?_, ?_⟩
      · simpa using ((hd ψ).pull hF hi le_rfl).mul hc
      · refine 𝔪.mul_mem_right _ ((h𝔪 _).2 fun hy => H _ (hd χ) ?_)
        rw [Scheme.basicOpen_appLE] at hy
        exact hy.2
      · rw [Finsupp.sum_mapRange_index fun _ => rfl, map_finsuppSum, Finsupp.sum_mul]
    | zero => exact ⟨0, fun ψ => isWt_zero ψ, 𝔪.zero_mem, by simp⟩
    | add _ _ _ _ h₁ h₂ =>
      obtain ⟨a, ha, hb, rfl⟩ := h₁
      obtain ⟨a', ha', hb', rfl⟩ := h₂
      exact ⟨a + a', fun ψ => (ha ψ).add (ha' ψ), 𝔪.add_mem hb hb',
        (Finsupp.sum_add_index' (fun _ => rfl) fun _ _ _ => rfl).symm⟩
    | neg _ _ h₁ =>
      obtain ⟨a, ha, hb, rfl⟩ := h₁
      exact ⟨-a, fun ψ => (wtSub i' _ ψ).neg_mem (ha ψ), 𝔪.neg_mem hb, by
        rw [Finsupp.sum_neg_index fun _ => rfl, Finsupp.sum_neg]⟩
  obtain ⟨a, ha, hb, rfl⟩ := key
  have e : a χ = a.sum fun _ y => y := h'.map_eq (RingHom.id _) (fun _ _ h => h) ha hu
  exact (h𝔪 _).1 hb (e ▸ hx)

theorem stable_basicOpen {V : G.left.Opens}
    (hV : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    {a : Γ(G.left, V)} {χ : X} (ha : IsWt i V a χ) :
    (snd (splitTorus S X) G).left ⁻¹ᵁ G.left.basicOpen a ≤
      ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ G.left.basicOpen a := by
  let U := (snd (splitTorus S X) G).left ⁻¹ᵁ G.left.basicOpen a
  let c : Over.mk (U.ι ≫ (splitTorus S X ⊗ G).hom) ⟶ splitTorus S X ⊗ G := Over.homMk U.ι rfl
  have h : ⊤ ≤ (c ≫ snd _ _).left ⁻¹ᵁ G.left.basicOpen a := fun y _ => y.2
  have k := h.trans ((c ≫ snd _ _).left.preimage_mono (G.left.basicOpen_le a))
  have e := congrArg (Scheme.basicOpen _) (ha _ (c ≫ fst _ _) (c ≫ snd _ _) (top_le_act hV _ k) k)
  rw [← chV_val, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (Units.isUnit _), Scheme.basicOpen_appLE,
    Scheme.basicOpen_appLE] at e
  have h' := ((le_inf le_rfl (le_inf le_rfl h)).trans e.ge).trans inf_le_right
  rw [Category.assoc, ← MonObj.comp_mul] at h'
  exact fun y hy => h' (x := ⟨y, hy⟩) trivial

theorem exists_goodOpen [IsAffine S] [IsAffine S'] [Flat f] [Surjective f] [LocallyOfFinitePresentation f]
    [UniversallyInjective f] [Module.Free ℤ X] [Module.Finite ℤ X] (hF : IsGrpPullback G' G f F) (Q : TQ G' X)
    [hm : IsMonHom i] (hi : TorusCompat f F Q.i i) (y : G.left) : ∃ W, y ∈ W ∧ GoodOpen i W := by
  classical
  have : Flat F := MorphismProperty.of_isPullback hF.1.flip ‹Flat f›
  have : Surjective F := MorphismProperty.of_isPullback hF.1.flip ‹Surjective f›
  have : LocallyOfFinitePresentation F := MorphismProperty.of_isPullback hF.1.flip ‹LocallyOfFinitePresentation f›
  have : UniversallyInjective F := MorphismProperty.of_isPullback hF.1.flip ‹UniversallyInjective f›
  have := Q.q_affine
  obtain ⟨x, rfl⟩ := F.surjective y
  obtain ⟨U, ⟨hU, hu⟩, hx⟩ := exists_affine_unitWts Q (Q.q.left x)
  let V : G.left.Opens := ⟨F '' (Q.q.left ⁻¹ᵁ U), F.isOpenMap _ (Q.q.left ⁻¹ᵁ U).isOpen⟩
  have e : Q.q.left ⁻¹ᵁ U = F ⁻¹ᵁ V := by
    ext1
    exact (Set.preimage_image_eq _ F.injective).symm
  have hst : (snd (splitTorus S' X) G').left ⁻¹ᵁ Q.q.left ⁻¹ᵁ U ≤
      ((fst (splitTorus S' X) G' ≫ Q.i) * snd (splitTorus S' X) G').left ⁻¹ᵁ Q.q.left ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, ← Over.comp_left, ← Over.comp_left, act_comp_q]
  have hA := hU.preimage Q.q.left
  have hx' : x ∈ Q.q.left ⁻¹ᵁ U := hx
  rw [e] at hu hst hA hx'
  have hV : IsAffineOpen V :=
    have : IsAffine (F ⁻¹ᵁ V).toScheme := hA
    isAffine_of_isPullback_of_flat_surjective ((isPullback_morphismRestrict F V).paste_vert hF.1)
  have hs := torus_stable_of_surjective f X G G' F hF Q.i i hi V hst
  have ex : ∀ χ, ∃ a : Γ(G.left, V), IsWt i V a χ ∧ F x ∈ G.left.basicOpen a := fun χ => by
    obtain ⟨u, hu⟩ := hu χ
    exact exists_isWt hF hi hV (functions_graded_by_weights S G X i hm V hV hs)
      (functions_graded_by_weights S' G' X Q.i Q.i_hom _ hA hst) hu
      (by rw [G'.left.basicOpen_of_isUnit u.isUnit]; exact hx')
  choose a ha hxa using ex
  have fin : ∀ s : Finset X, ∃ (c : Γ(G.left, V)) (ψ : X), IsWt i V c ψ ∧ F x ∈ G.left.basicOpen c ∧
      ∀ χ ∈ s, G.left.basicOpen c ≤ G.left.basicOpen (a χ) := fun s => by
    induction s using Finset.induction_on with
    | empty => exact ⟨a 0, 0, ha 0, hxa 0, by simp⟩
    | insert χ s _ ih =>
      obtain ⟨c, ψ, h₁, h₂, h₃⟩ := ih
      refine ⟨a χ * c, _, (ha χ).mul h₁, ?_, fun φ hφ => ?_⟩
      · rw [Scheme.basicOpen_mul]; exact ⟨hxa χ, h₂⟩
      · rw [Scheme.basicOpen_mul]
        rcases Finset.mem_insert.1 hφ with rfl | hφ
        · exact inf_le_left
        · exact inf_le_right.trans (h₃ φ hφ)
  obtain ⟨s, hspan⟩ := (Module.finite_def.1 ‹Module.Finite ℤ X›)
  obtain ⟨c, ψ, h₁, h₂, h₃⟩ := fin s
  refine ⟨_, h₂, hV.basicOpen c, stable_basicOpen hs h₁, exists_units_hom fun χ => ?_⟩
  have hle : Submodule.span ℤ (s : Set X) ≤ (unitWts i (G.left.basicOpen c)).toIntSubmodule :=
    Submodule.span_le.2 fun φ hφ => unitWts_mono (h₃ φ hφ)
      ⟨(RingedSpace.isUnit_res_basicOpen G.left.toRingedSpace (a φ)).unit, (ha φ).res (G.left.basicOpen_le _)⟩
  exact hle (hspan.ge Submodule.mem_top)

end Opens

theorem nonempty_torusExtension {k K : Type} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    [IsPurelyInseparable k K] {G : Over (Sp k)} [GrpObj G] (hG : SmConn G) {G' : Over (Sp K)} [GrpObj G']
    {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G (spMap (algebraMap k K)) F) {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (Q : TQ G' X) : Nonempty (TorusExtension G) := by
  have := FieldBaseChange.flat_spMap (algebraMap k K)
  have := FieldBaseChange.surjective_spMap (algebraMap k K)
  have := universallyInjective_spMap k K
  have : IsFinite (spMap (algebraMap k K)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  have : LocallyOfFinitePresentation (spMap (algebraMap k K)) := inferInstance
  have := isLocalRing_tensor k K
  have : IsNoetherianRing (K ⊗[k] K) := isNoetherian_of_tower K inferInstance
  obtain ⟨i, hm, hi⟩ := exists_torus
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct k K K)) hF Q
  obtain ⟨B, _, q, ⟨-, hq, hf, hs, ha, hk, hc, hsm, hsep, hqc, hgc⟩, -⟩ :=
    TorusQuotientGlue.main k G hG X i hm (exists_goodOpen hF Q hi)
  have hB := isGrpPullback_pullback B (spMap (algebraMap k K))
  have w : (F ≫ q.left) ≫ B.hom = G'.hom ≫ spMap (algebraMap k K) := by rw [Category.assoc, Over.w, hF.1.w]
  let q' : G' ⟶ (Over.pullback (spMap (algebraMap k K))).obj B :=
    Over.homMk (hB.1.lift _ _ w) (hB.1.lift_snd _ _ w)
  have hq' : q'.left ≫ pullback.fst B.hom _ = F ≫ q.left := hB.1.lift_fst _ _ w
  have := isMonHom_of_over_isMonHom hF hB q q' hq'
  have := Q.q_hom
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  have := Q.isAb.proper
  obtain ⟨β, -, hβ⟩ := FlatQuotient.exists_desc Q.q Q.i q' Q.isKernel (by
    refine Over.OverMorphism.ext (hB.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hq', eSec_comp_of_isGrpPullback hB,
      ← Category.assoc, ← torusCompat_iff.1 hi, Category.assoc, ← Over.comp_left, hk.w, Over.comp_left,
      Rosenlicht.toUnit_left, Rosenlicht.toUnit_left, bcMap_hom_assoc])
  have : Surjective F := MorphismProperty.of_isPullback hF.1.flip ‹Surjective (spMap (algebraMap k K))›
  have e₁ : Q.q.left ≫ β.left ≫ pullback.fst B.hom _ = F ≫ q.left := by
    rw [← hq', ← hβ, Over.comp_left, Category.assoc]
  have : Surjective (Q.q.left ≫ β.left ≫ pullback.fst B.hom _) := by rw [e₁]; infer_instance
  have : Surjective (β.left ≫ pullback.fst B.hom _) := Surjective.of_comp Q.q.left _
  have e₂ : (β.left ≫ pullback.fst B.hom _) ≫ B.hom = Q.B.hom ≫ spMap (algebraMap k K) := by
    rw [Category.assoc, hB.1.w, Over.w_assoc]
  have : UniversallyClosed ((β.left ≫ pullback.fst B.hom _) ≫ B.hom) := by rw [e₂]; infer_instance
  have : UniversallyClosed B.hom := UniversallyClosed.of_comp_surjective (β.left ≫ pullback.fst B.hom _) _
  exact ⟨{ X := X, B := B, isAbelian := ⟨hc, hsm, {}, hgc⟩, q := q, q_hom := hq, q_flat := hf, q_surjective := hs,
           q_quasiCompact := inferInstance, i := i, i_hom := hm, isKernel := hk }⟩

end GlobalTheory.InsepDescent

namespace GlobalTheory

theorem exists_finite_separable_torusExtension : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G],
    IsSemiAbelian G → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
      Algebra.IsSeparable k k' ∧ Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap k k'))).obj G)) := by
  intro k _ G _ hG
  have := hG.smooth
  have := hG.comm
  obtain ⟨K, hK, T⟩ := exists_finite_torusExtension k (AlgebraicClosure k) G inferInstance hG.quasiCompact
    hG.separated (hG.fibres _ _)
  obtain ⟨E, ⟨d⟩⟩ := exists_splitExt_isGt_of_torusExtension _ _ T
  have := E.free
  have := E.finite
  let k' := separableClosure k K
  have h' := IsSemiAbelian.pullback (spMap (algebraMap k k')) G hG
  have : FiniteDimensional k' K := Module.Finite.of_restrictScalars_finite k k' K
  have e := FieldModel.spMap_comp (IsScalarTower.algebraMap_eq k k' K).symm
  have HG := isGrpPullback_pullback G (spMap (algebraMap k K))
  obtain ⟨F, h₁, h₂⟩ := FieldModel.exists_baseChange (X := (Over.pullback (spMap (algebraMap k K))).obj G) (X₀ := G)
    e HG.1
  exact ⟨k', inferInstance, inferInstance, inferInstance, inferInstance,
    InsepDescent.nonempty_torusExtension ⟨h'.comm, h'.smooth, h'.separated, h'.quasiCompact, h'.geomConnected⟩
      ((isGrpPullback_pullback G (spMap (algebraMap k k'))).cancel (HG.congr e.symm h₁.symm) h₂.w)
      (TQ.ofGtDatum d)⟩

end GlobalTheory

end
