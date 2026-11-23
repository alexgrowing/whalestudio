import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRankOneNonproperPowerSeries
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataUniformisationUnconditiona

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SplitMultiplicative

open IsLocalRing

section Curve

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.WeierstrassCurve GlobalTheory.MultiplicativeReduction

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem isUnit_one_sub {a : V} (ha : a ∈ maximalIdeal V) : IsUnit (1 - 64 * a) :=
  isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_left (maximalIdeal V) 64 ha)

theorem isElliptic_generic {a : V} (ha : a ∈ maximalIdeal V) (ha0 : a ≠ 0) :
    ((⟨1, 0, 0, a, 0⟩ : WeierstrassCurve V).map (algebraMap _ (FractionRing V))).IsElliptic := by
  refine ⟨?_⟩
  rw [WeierstrassCurve.map_Δ, isUnit_iff_ne_zero, map_ne_zero_iff _ (IsFractionRing.injective _ _)]
  have : (⟨1, 0, 0, a, 0⟩ : WeierstrassCurve V).Δ = a ^ 2 * (1 - 64 * a) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  rw [this]
  exact mul_ne_zero (pow_ne_zero _ ha0) (isUnit_one_sub ha).ne_zero

theorem isSemiAbelian_and_specialFibre {a : V} (ha : a ∈ maximalIdeal V) : ∀ (W : WeierstrassCurve V), W = ⟨1, 0, 0, a, 0⟩ → ∀ (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : V →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → QuasiCompact (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∀ [GrpObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))] [IsCommMonObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))], (∀ (k : Type) [Field k] (ρ : V →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) → IsSemiAbelian (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ∧ ∃ i : splitTorus (Spec (CommRingCat.of (IsLocalRing.ResidueField V))) ℤ ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))).obj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)), IsMonHom i.hom := by
  intro W hW U hU hsm hgi hqc _ _ hmul
  have hgc : GeometricallyConnected (U.ι ≫ toSpec W) := by
    refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
    have : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
    exact inferInstanceAs (ConnectedSpace Z)
  have htor : ∀ (K : Type) [Field K] (f : V →+* K), f a = 0 →
      ∃ i : splitTorus (Spec (CommRingCat.of K)) ℤ ≅
        (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj (Over.mk (U.ι ≫ toSpec W)),
        IsMonHom i.hom := by
    intro K _ f hf
    obtain ⟨U', _, e, he, -, hU', hmul'⟩ :=
      GlobalTheory.SmoothLocusBaseChange.main _ K f W U hU hsm hgi hmul
    have hl : U'.ι ≫ toSpec (W.map f) =
        e.hom.left ≫ pullback.snd (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f)) :=
      (Over.w e.hom).symm
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    obtain ⟨i, hi⟩ := GlobalTheory.NodalCubic.exists_splitTorus_iso K (W.map f)
      (by subst hW; ext <;> simp [hf]) U' hU' (by rw [hl]; infer_instance)
      (by
        rw [hl]
        exact MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
          (IsPullback.of_horiz_isIso (fst := e.hom.left) (g := 𝟙 _) ⟨(Category.comp_id _).symm⟩)
          (inferInstanceAs (GeometricallyIntegral
            (pullback.snd (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f)))))) hmul'
    exact ⟨i ≪≫ e, by rw [Iso.trans_hom]; infer_instance⟩
  refine ⟨⟨inferInstance, hsm, inferInstanceAs (IsSeparated (U.ι ≫ toSpec W)), hqc,
    hgc, fun Ω _ _ p => ?_⟩,
    htor _ _ ?_⟩
  · obtain ⟨g, rfl⟩ := Spec.map_surjective p
    obtain ⟨f, rfl⟩ : ∃ f : V →+* Ω, g = CommRingCat.ofHom f := ⟨g.hom, rfl⟩
    by_cases hf : f a = 0
    · obtain ⟨i, hi⟩ := htor Ω f hf
      obtain ⟨T⟩ := nonempty_torusExtension_splitTorus Ω
      exact ⟨Geo.Tor.torusExtOfIso i T⟩
    · have hΔ : W.Δ = a ^ 2 * (1 - 64 * a) := by
        subst hW
        simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        ring
      have hu : IsUnit (1 - 64 * a : V) := isUnit_one_sub ha
      have hΔ' : f W.Δ ≠ 0 := by
        rw [hΔ, map_mul, map_pow]
        exact mul_ne_zero (pow_ne_zero _ hf) (hu.map f).ne_zero
      refine ⟨GlobalTheory.torusExtensionOfAbelian _ ⟨inferInstance, ?_, ?_, ?_⟩⟩
      · exact inferInstanceAs (Smooth (pullback.snd (U.ι ≫ toSpec W) _))
      · exact isProper_pullback_snd W U hU f hΔ'
      · exact inferInstanceAs (GeometricallyConnected (pullback.snd (U.ι ≫ toSpec W) _))
  · exact (IsLocalRing.residue_eq_zero_iff a).2 ha

theorem exists_semiAbelian_polarised {a : V} (ha : a ∈ maximalIdeal V) (ha0 : a ≠ 0) : ∃ (G : Over (Spec (CommRingCat.of V))) (_ : GrpObj G) (_ : IsCommMonObj G) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (eA : (Over.pullback (jK V)).obj G ≅ A.A) (i : splitTorus (Spec (CommRingCat.of (IsLocalRing.ResidueField V))) ℤ ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))).obj G), IsSemiAbelian G ∧ IsMonHom eA.hom ∧ IsMonHom i.hom ∧ A.g = 1 ∧ ∃ (LG : RigLB G) (_c : CubicalStr G LG) (s : LB.Gen (LB.LinComb LG.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen ∧ LB.Gen.Corr LG.L _ _ _ _ (LB.pullGen LG.L _ _ s (eSec G)) (LB.oneGen LG.L) ∧ (∃ w : LB.Iso (A.L.pull eA.hom.left) (LG.L.pull (pullback.fst G.hom (jK V))), w.IsGen) ∧ ∃ θ : H0 LG.L 1, ∀ x : G.left, G.hom x = IsLocalRing.closedPoint V → x ∈ nonzeroLocus θ := by
  have hL := GlobalTheory.allSixLaws.1
  obtain ⟨W, hW⟩ : ∃ W : WeierstrassCurve V, W = ⟨1, 0, 0, a, 0⟩ := ⟨_, rfl⟩
  obtain ⟨U, hU, hsm, hqc, hgi⟩ := exists_smoothLocus _ W
  have hs : Smooth (U.ι ≫ toSpec W) := SmoothOfRelativeDimension.smooth 1 _
  obtain ⟨_, _, hη, hmul⟩ := GlobalTheory.exists_grpObj_smoothLocus _ W U hU hs hgi
  obtain ⟨hG, i, hi⟩ := isSemiAbelian_and_specialFibre ha W hW U hU hs hgi hqc hmul
  let f := algebraMap V (FractionRing V)
  have : (W.map f).IsElliptic := hW ▸ isElliptic_generic ha ha0
  obtain ⟨φ, hφ⟩ := exists_iso_schemeOver f W U hU
  let G := Over.mk (U.ι ≫ toSpec W)
  let j := pullback.fst G.hom (jK V)
  have hη' : (η[(Over.pullback (jK V)).obj G]).left ≫ j ≫ U.ι = jK _ ≫ zero W := by
    rw [← hη, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ U.ι) (one_pullback_fst _ G)
  have hP : IsUnimodularSol (W.map f) ![0, 0, 1] := hW ▸ isUnimodularSol_twoPt _ _
  have hX : f a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha0
  have hPU := (hU _ f _ hP).2 (hW ▸ (nonsingular_twoPt _ f).2 hX)
  have hr : Set.range (ptHom W f _ hP) ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hPU (Set.mem_univ y)
  have hb := IsOpenImmersion.lift_fac U.ι (ptHom W f _ hP) hr
  have hb' : IsOpenImmersion.lift U.ι (ptHom W f _ hP) hr ≫ U.ι ≫ toSpec W = jK _ := by
    rw [← Category.assoc, hb, ptHom_toSpec]
  let b : Over.mk (jK V) ⟶ G := Over.homMk _ hb'
  let x : 𝟙_ _ ⟶ (Over.pullback (jK V)).obj G :=
    Over.homMk (pullback.lift b.left (𝟙 _) (hb'.trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _)
  have hxa : x.left ≫ j = b.left := pullback.lift_fst _ _ _
  have hx : x * x = 1 := by
    have h₁ : (1 : 𝟙_ _ ⟶ (Over.pullback (jK V)).obj G) = η[_] := by rw [Hom.one_def]; simp
    rw [h₁]
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have h₂ := SmoothLocusBaseChange.lift_mul_pullback_fst (jK V) G x x (𝟙 _) b b
      (hxa.symm.trans (Category.id_comp _).symm) (hxa.symm.trans (Category.id_comp _).symm)
    obtain ⟨h, h₃⟩ := hmul _ f b b _ _ hP hP hb hb
    refine (cancel_mono U.ι).1 ?_
    refine Eq.trans ?_ (hη'.symm.trans (Category.assoc _ _ _).symm)
    refine (congrArg (· ≫ U.ι) (h₂.trans (Category.id_comp _))).symm.trans (h₃.trans ?_)
    rw [SpecMap_zero, ptHom_eq_ptHom_iff_minors]
    obtain ⟨h₄, h₅⟩ := add_twoPt a f
    rw [← hW] at h₄ h₅
    intro m l
    fin_cases m <;> fin_cases l <;> simp [h₄, h₅]
  have hz : (η[(Over.pullback (jK V)).obj G]).left ≫ φ.hom.left = zero (W.map f) := by
    apply (isPullback_mapHom W f rfl).hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hφ).trans (hη'.trans (zero_mapHom W f rfl).symm))
    · exact (Over.w (η[(Over.pullback (jK V)).obj G] ≫ φ.hom)).trans (zero_toSpec _).symm
  obtain ⟨A, eA, θ, heA, hg, hθ⟩ := exists_pol_twoTorsion hL (W.map f) _ φ hz x hx
  obtain ⟨LG, c, s, hs₁, hs₂, w, hw⟩ := PolExtension.exists_cubical_symmetric_extension hL _ G hG A eA heA
  refine ⟨G, inferInstance, inferInstance, A, eA, i, hG, heA, hi, hg, LG, c, s, hs₁, hs₂, ⟨w, hw⟩, ?_⟩
  obtain ⟨t, ht⟩ := exists_sec_of_iso A.isLB (pull_isLB LG.isLB j) eA.hom.left ⟨w, hw⟩ θ
  have ht' : ∀ z, z ∈ nonzeroLocus t ↔ z ∉ Set.range x.left := fun z => (ht z).trans (hθ z)
  refine exists_sec_generates_specialFibre _ G hG LG.L LG.isLB t
    ⟨(η[(Over.pullback (jK V)).obj G]).left (IsLocalRing.closedPoint _), (ht' _).2 ?_⟩ ?_
  · rintro ⟨p, hp⟩
    have h₁ : ptHom W f _ hP p ∈ coordOpen W 2 := (ptHom_preimage_coordOpen W f _ hP 2).ge
      (PrimeSpectrum.basicOpen_one.ge (Set.mem_univ p))
    have h₂ : ptHom W f _ hP p = zero W (jK _ (IsLocalRing.closedPoint _)) :=
      (congrArg (fun q => q p) ((congrArg (· ≫ U.ι) hxa).trans hb)).symm.trans
        ((congrArg (j ≫ U.ι) hp).trans (congrArg (fun q => q (IsLocalRing.closedPoint _)) hη'))
    rw [h₂] at h₁
    exact (zero_preimage_coordOpen_two W).le h₁
  · have e : j '' {z | z ∉ nonzeroLocus t} = Set.range b.left := by
      rw [← hxa]
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨p, rfl⟩ := not_not.1 (mt (ht' z).2 hz)
        exact ⟨p, rfl⟩
      · rintro ⟨p, rfl⟩
        exact ⟨x.left p, fun h => (ht' _).1 h ⟨p, rfl⟩, rfl⟩
    exact e ▸ isClosed_twoPt ha W hW U hU b.left hP hb

end Curve

open GlobalTheory.UU GlobalTheory.MultiplicativeTorusSetting GlobalTheory.TateUnif

theorem not_isProper_torus_of_infinite (k : Type) [Field k] [Infinite k] :
    ¬ IsProper (splitTorus (Spec (CommRingCat.of k)) ℤ).hom := fun h => by
  let e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  obtain ⟨p, hp, h0⟩ := isIntegral_appTop_of_universallyClosed (splitTorus (Spec (CommRingCat.of k)) ℤ).hom
    (charUnit (Spec (CommRingCat.of k)) ℤ 1).val
  have root : ∀ a : kˣ, (p.map e.symm.toRingHom).IsRoot a.val := fun a => by
    let t : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ splitTorus (Spec (CommRingCat.of k)) ℤ :=
      (splitTorusPointsEquiv _ ℤ _).symm (zpowersHom _ (Units.map e.toMonoidHom a))
    have h₁ : t.left.appTop.hom (charUnit (Spec (CommRingCat.of k)) ℤ 1).val = e a.val := by
      rw [← chV_val, chV, MulEquiv.apply_symm_apply]
      exact congrArg Units.val (zpow_one (Units.map e.toMonoidHom a))
    have h₂ : t.left.appTop.hom.comp (splitTorus (Spec (CommRingCat.of k)) ℤ).hom.appTop.hom = RingHom.id _ := by
      rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, Over.w]
      exact congrArg CommRingCat.Hom.hom Scheme.Hom.id_appTop
    have h₃ := congrArg t.left.appTop.hom h0
    rw [Polynomial.hom_eval₂, h₂, h₁, map_zero] at h₃
    have h₄ := congrArg e.symm.toRingHom h₃
    rw [Polynomial.hom_eval₂, map_zero] at h₄
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    simpa using h₄
  have inf : Set.Infinite {x | (p.map e.symm.toRingHom).IsRoot x} :=
    (Set.finite_singleton (0 : k)).infinite_compl.mono fun x hx => root (Units.mk0 x hx)
  exact (hp.map _).ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ inf)

theorem not_isProper_torus (k : Type) [Field k] :
    ¬ IsProper (splitTorus (Spec (CommRingCat.of k)) ℤ).hom := fun h =>
  not_isProper_torus_of_infinite (AlgebraicClosure k) (MorphismProperty.of_isPullback (P := @IsProper)
    (SplitTorus.isGrpPullback_bcMap (spMap (algebraMap k (AlgebraicClosure k))) ℤ).1 h)

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]

theorem exists_setting (hV : CDVR V) : ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) (_ : GrpObj G) (_ : IsCommMonObj G) (s : HidaSetting V A G), A.g = 1 ∧ Module.finrank ℤ s.X = 1 ∧ ¬ IsProper (thickObj V (IsLocalRing.maximalIdeal V) 0 G).hom := by
  obtain ⟨laws, laws₂, -⟩ := GlobalTheory.allSixLaws
  have := hV.1
  obtain ⟨a, ha'⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨G, _, _, A, eA, i, hG, hA, hi, hg, L, -, -, -, -, hw, θ, hθ⟩ :=
    exists_semiAbelian_polarised (a := a) ha'.not_isUnit ha'.ne_zero
  obtain ⟨P, rfl⟩ := CubicalPackage.exists_package laws _ hV A G hG eA hA L hw
  have := hG.smooth
  have : IsMonHom eA.symm.hom := inferInstanceAs (IsMonHom eA.inv)
  have gp : IsGrpPullback A.A G (jK _) (eA.inv.left ≫ pullback.fst G.hom (jK _)) :=
    ((isGrpPullback_of_iso eA.symm).comp (isGrpPullback_pullback G (jK _))).congr (Category.id_comp _) rfl
  have hinv : eA.inv.left ≫ eA.hom.left = 𝟙 _ := by rw [← Over.comp_left, eA.inv_hom_id, Over.id_left]
  obtain ⟨s, hs⟩ := exists_even_sec laws₂.secTwist A gp P
    (LBIso.chartPull (chartPullSec A.L _ eA.inv.left hinv) (chartPullSame P.L.L _ _ _ eA.inv.left fun _ => rfl) hw) θ
    (hθ _ (congrArg (fun q => q (IsLocalRing.closedPoint V)) (Over.w η[G])))
  obtain ⟨r, hr⟩ := thick_zero_factor V
  obtain ⟨i₀, hi₀, -⟩ := grpPullback_iso
    (((SplitTorus.isGrpPullback_bcMap r ℤ).comp ((isGrpPullback_of_iso i).comp (isGrpPullback_pullback G _))).congr
      ((congrArg (r ≫ ·) (Category.id_comp _)).trans hr.symm) rfl)
    (isGrpPullback_pullback G (thick _ (IsLocalRing.maximalIdeal V) 0))
  obtain ⟨P₀, w₀, h₀⟩ := exists_isLevelCP (IsLocalRing.maximalIdeal V) 0 P
  have hm : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  let _ : Field (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := Ideal.Quotient.field _
  obtain ⟨wA, hwA⟩ := hw
  refine ⟨A, G, inferInstance, inferInstance, ⟨hV, hG, eA, hA, P, wA, hwA, ℤ, tqOfIso i₀, P₀, ⟨w₀, h₀⟩,
    exists_even_cubTriv i₀ h₀ s (fun y J hJ => (hs _ _ y J hJ).1 (hθ _ ?_)) fun Z r z J hJ => (hs Z r z J hJ).2⟩,
    hg, Module.finrank_self ℤ, fun h => not_isProper_torus
      (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) ?_⟩
  · exact (congrArg (fun q => q y) (pullback.condition.trans (congrArg (_ ≫ ·) hr))).trans
      (IsLocalRing.PrimeSpectrum.comap_residue _ (r (pullback.snd G.hom _ y)))
  · have : IsIso i₀.hom.left := inferInstanceAs (IsIso ((Over.forget _).map i₀.hom))
    rw [← Over.w i₀.hom]
    infer_instance

theorem exists_unif_rank_one (hV : CDVR V) : ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) (_ : GrpObj G) (_ : IsCommMonObj G) (D : DegData V (IsLocalRing.maximalIdeal V)) (_ : Unif (IsLocalRing.maximalIdeal V) D A G), IsSemiAbelian G ∧ A.g = 1 ∧ Module.finrank ℤ D.toPre.X = 1 ∧ D.toPre.P.g = 0 := by
  obtain ⟨A, G, _, _, s, hA, -, hnp⟩ := exists_setting hV
  obtain ⟨D, U, -⟩ := GlobalTheory.UU.exists_degData_unif_unconditional V A G s
  have hR : AdmBase V (IsLocalRing.maximalIdeal V) :=
    have := hV.1
    ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have h := rank_add_dim hR s.semi U
  have h0 : Module.finrank ℤ D.toPre.X ≠ 0 := fun h0 => by
    have : Subsingleton D.toPre.X := Module.finrank_zero_iff.1 h0
    exact hnp (isProper_of_subsingleton (U.gt 0))
  exact ⟨A, G, inferInstance, inferInstance, D, U, s.semi, hA, by omega, by omega⟩

end GlobalTheory.SplitMultiplicative

end
