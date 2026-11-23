import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsoUniqueOfRig

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

theorem ext_of_schDom {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  have hΔ : IsClosedImmersion (pullback.diagonal s) := inferInstance
  have hi : IsClosedImmersion (pullback.snd (pullback.diagonal s) (pullback.lift f g h)) :=
    inferInstance
  have hj : (ι ≫ f) ≫ pullback.diagonal s = ι ≫ pullback.lift f g h := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd, hU]
  have hji : pullback.lift (ι ≫ f) ι hj ≫ pullback.snd (pullback.diagonal s) (pullback.lift f g h) = ι :=
    pullback.lift_snd _ _ _
  have hker : (pullback.snd (pullback.diagonal s) (pullback.lift f g h)).ker = ⊥ := by
    apply le_bot_iff.mp
    have h0 := Scheme.Hom.le_ker_comp (pullback.lift (ι ≫ f) ι hj)
      (pullback.snd (pullback.diagonal s) (pullback.lift f g h))
    rw [hji, (inferInstance : IsSchemeTheoreticallyDominant ι).1] at h0
    exact h0
  have hiso : IsIso (pullback.snd (pullback.diagonal s) (pullback.lift f g h)) :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  have hc := pullback.condition (f := pullback.diagonal s) (g := pullback.lift f g h)
  have h1 : pullback.fst (pullback.diagonal s) (pullback.lift f g h) =
      pullback.snd (pullback.diagonal s) (pullback.lift f g h) ≫ f := by
    simpa only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd] using congrArg (· ≫ pullback.fst s s) hc
  have h2 : pullback.fst (pullback.diagonal s) (pullback.lift f g h) =
      pullback.snd (pullback.diagonal s) (pullback.lift f g h) ≫ g := by
    simpa only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd] using congrArg (· ≫ pullback.snd s s) hc
  exact (cancel_epi _).mp (h1.symm.trans h2)

theorem schDom_spec_map {A B : Type} [CommRing A] [CommRing B] [IsReduced A] (φ : A →+* B)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom φ)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (f := φ)).mpr (by
      rw [(RingHom.injective_iff_ker_eq_bot φ).mp hφ]; exact bot_le)⟩
  exact IsSchemeTheoreticallyDominant.of_isDominant _

set_option maxHeartbeats 800000 in

theorem over_ext_of_points {F : Type} [Field F] [IsAlgClosed F] {K Y : Over (Spec (CommRingCat.of F))}
    [LocallyOfFiniteType K.hom] [FormallyUnramified Y.hom] [LocallyOfFiniteType Y.hom] (u v : K ⟶ Y)
    (h : ∀ p : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ K, p ≫ u = p ≫ v) : u = v := by
  have hop : IsOpenImmersion (equalizer.ι u v).left := by
    refine MorphismProperty.of_isPullback ((Limits.isPullback_equalizer_prod u v).map (Over.forget _)).flip ?_
    show IsOpenImmersion (prod.lift (𝟙 Y) (𝟙 Y)).left
    rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _ (Over.prodLeftIsoPullback Y Y).hom]
    convert! (inferInstance : IsOpenImmersion (pullback.diagonal Y.hom))
    ext1 <;> simp [← Over.comp_left] <;> first | rw [prod.lift_fst, Over.id_left] | rw [prod.lift_snd, Over.id_left]
  have : JacobsonSpace K.left := LocallyOfFiniteType.jacobsonSpace K.hom
  have hcl : closedPoints K.left ⊆ Set.range (equalizer.ι u v).left := by
    intro x hx
    let p : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ K :=
      Over.homMk (pointOfClosedPoint K.hom x hx) (pointOfClosedPoint_comp K.hom x hx)
    let q := equalizer.lift p (h p)
    let pt : (𝟙_ (Over (Spec (CommRingCat.of F)))).left := IsLocalRing.closedPoint F
    refine ⟨q.left pt, ?_⟩
    have e : q.left ≫ (equalizer.ι u v).left = p.left := by rw [← Over.comp_left, equalizer.lift_ι]
    have e' : (q.left ≫ (equalizer.ι u v).left) pt = p.left pt := by rw [e]
    exact e'.trans (pointOfClosedPoint_apply K.hom x hx pt)
  have hsurj : Function.Surjective (equalizer.ι u v).left := by
    by_contra hns
    obtain ⟨x, hx⟩ := not_forall.1 hns
    have hC : IsClosed (Set.range (equalizer.ι u v).left)ᶜ :=
      (equalizer.ι u v).left.isOpenEmbedding.isOpen_range.isClosed_compl
    obtain ⟨y, hy1, hy2⟩ := nonempty_inter_closedPoints ⟨x, hx⟩ hC.isLocallyClosed
    exact hy1 (hcl hy2)
  have : Surjective (equalizer.ι u v).left := ⟨hsurj⟩
  have : IsIso (equalizer.ι u v).left := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hop, this⟩
  have h0 : IsIso ((Over.forget _).map (equalizer.ι u v)) := (inferInstance : IsIso (equalizer.ι u v).left)
  have : IsIso (equalizer.ι u v) := isIso_of_reflects_iso _ (Over.forget _)
  exact (cancel_epi (equalizer.ι u v)).1 (equalizer.condition u v)

open MonObj in
set_option maxHeartbeats 1600000 in

theorem fix_torsion (hMul : Out.MulNSt) {F : Type} [Field F] [IsAlgClosed F] (P : Out.PolAV (Spec (CommRingCat.of F)))
    (M : ℕ) (hM1 : 1 ≤ M) (hM : (M : F) ≠ 0) (σ : P.A ⟶ P.A) [IsMonHom σ]
    (hσ : ∀ x : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ P.A, x ^ M = 1 → x ≫ σ = x)
    (T : Over (Spec (CommRingCat.of F))) (x : T ⟶ P.A) (hx : x ^ M = 1) : x ≫ σ = x := by
  obtain ⟨-, -, -, het, -⟩ := hMul _ P M hM1
  have hunit : IsUnit ((M : ℕ) : Γ(Spec (CommRingCat.of F), ⊤)) := by
    have e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
    have : IsUnit (e.symm (M : F)) := (isUnit_iff_ne_zero.2 hM).map e.symm
    rwa [map_natCast] at this
  have : Etale (Out.mulA P.A M).left := het hunit
  have hpow : ∀ {Z : Over (Spec (CommRingCat.of F))} (z : Z ⟶ P.A), z ^ M = z ≫ Out.mulA P.A M := fun z =>
    (congrArg (· ^ M) (Category.comp_id z).symm).trans (MonObj.comp_pow (𝟙 P.A) M z).symm
  have hcomm : σ ≫ Out.mulA P.A M = Out.mulA P.A M ≫ σ := by
    rw [← hpow, Out.mulA, MonObj.pow_comp, Category.id_comp]
  let m := (Out.mulA P.A M).left
  let e := (η[P.A]).left
  let K : Over (Spec (CommRingCat.of F)) := Over.mk (show pullback m e ⟶ Spec (CommRingCat.of F) from pullback.snd m e)
  have hw : pullback.fst m e ≫ P.A.hom = pullback.snd m e := by
    rw [← Over.w (Out.mulA P.A M), ← Category.assoc, pullback.condition, Category.assoc, Over.w η[P.A]]
    exact Category.comp_id _
  have hσm : (pullback.fst m e ≫ σ.left) ≫ m = pullback.snd m e ≫ e := by
    have h1 : σ.left ≫ m = m ≫ σ.left := congrArg CommaMorphism.left hcomm
    have h2 : e ≫ σ.left = e := congrArg CommaMorphism.left (IsMonHom.one_hom σ)
    rw [Category.assoc, h1, ← Category.assoc, pullback.condition, Category.assoc, h2]
  let τ : K ⟶ K := Over.homMk (pullback.lift _ _ hσm) (pullback.lift_snd _ _ _)
  have hKe : Etale K.hom := by show Etale (pullback.snd m e); infer_instance
  have : LocallyOfFinitePresentation K.hom := inferInstance
  have : LocallyOfFiniteType K.hom := inferInstance
  have : FormallyUnramified K.hom := inferInstance
  have hτ : τ = 𝟙 K := by
    refine over_ext_of_points τ (𝟙 K) fun p => ?_
    rw [Category.comp_id]
    ext1
    apply pullback.hom_ext
    · show p.left ≫ pullback.lift _ _ hσm ≫ pullback.fst m e = p.left ≫ pullback.fst m e
      rw [pullback.lift_fst]
      have hp1 : p.left ≫ pullback.snd m e = 𝟙 _ := Over.w p
      let q : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ P.A := Over.homMk (p.left ≫ pullback.fst m e) (by
        rw [Category.assoc, hw, hp1]; rfl)
      have hq : q ^ M = 1 := by
        rw [hpow]
        ext1
        show (p.left ≫ pullback.fst m e) ≫ m = (toUnit _ ≫ η[P.A]).left
        rw [Category.assoc, pullback.condition, ← Category.assoc, hp1, Category.id_comp, Over.comp_left]
        have : toUnit (𝟙_ (Over (Spec (CommRingCat.of F)))) = 𝟙 _ := Subsingleton.elim _ _
        rw [this, Over.id_left, Category.id_comp]
      have := congrArg CommaMorphism.left (hσ q hq)
      rw [← Category.assoc]
      exact this
    · show p.left ≫ pullback.lift _ _ hσm ≫ pullback.snd m e = p.left ≫ pullback.snd m e
      rw [pullback.lift_snd]
  have hxm : x.left ≫ m = T.hom ≫ e := by
    have := congrArg CommaMorphism.left ((hpow x).symm.trans hx)
    exact this
  let κ : T ⟶ K := Over.homMk (pullback.lift x.left T.hom hxm) (pullback.lift_snd _ _ _)
  have hτl : pullback.lift _ _ hσm = 𝟙 _ := congrArg CommaMorphism.left hτ
  ext1
  show x.left ≫ σ.left = x.left
  have k1 : x.left = κ.left ≫ pullback.fst m e := (pullback.lift_fst _ _ _).symm
  rw [k1, Category.assoc, ← pullback.lift_fst (pullback.fst m e ≫ σ.left) (pullback.snd m e) hσm, hτl,
    Category.id_comp]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
