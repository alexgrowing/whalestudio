import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.GalV
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.G3

namespace UpperTheory.Gal.Seam

private theorem sq_up {A B A' B' S S' : Scheme.{0}} {f : A ⟶ B} {qB : B ⟶ S} {qA : A ⟶ S} (hA : f ≫ qB = qA) {g : S' ⟶ S}
    {fA : A' ⟶ A} {pA : A' ⟶ S'} (hA' : IsPullback fA pA qA g) {w : B' ⟶ B} {pB : B' ⟶ S'} (hB : IsPullback w pB qB g)
    {f' : A' ⟶ B'} (h1 : f' ≫ w = fA ≫ f) (h2 : f' ≫ pB = pA) : IsPullback fA f' f w := by
  subst hA; subst h2
  have s : IsPullback (f' ≫ pB) fA g (f ≫ qB) := hA'.flip
  exact (IsPullback.of_right s h1 hB.flip).flip

private abbrev spf {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : sp B ⟶ sp A := Spec.map (CommRingCat.ofHom f)

private theorem fEt_bc : FEtBasic := pFEtBasic pPtsOfSplits

private theorem splits_bc : SplitsBasic := pSplitsBasic (pSplitsPts pIsoPts) pPtsOfSplits

section

variable {k K O O' L : Type} [Field k] [Field K] [CommRing O] [CommRing O'] [Algebra O k] [Algebra O' K] [Field L]
  (τ : k →+* K) (φ : O →+* O')

private theorem gen_sq (hφ : ∀ x, algebraMap O' K (φ x) = τ (algebraMap O k x)) :
    gen O' K ≫ spf φ = spf τ ≫ gen O k := by
  simp only [gen, spf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact hφ x

variable {H : HTower k} {θ : H.Γ → L} (C : Cover H θ O) (hφ : ∀ x, algebraMap O' K (φ x) = τ (algebraMap O k x))

include hφ in
private theorem pullback_square_commutes : (pullback.fst H.q (spf τ) ≫ C.π) ≫ C.p = (pullback.snd H.q (spf τ) ≫ gen O' K) ≫ spf φ := by
  rw [Category.assoc, C.ov, Category.assoc, gen_sq τ φ hφ, ← Category.assoc, pullback.condition, Category.assoc]

private def piY : pullback H.q (spf τ) ⟶ pullback C.p (spf φ) :=
  pullback.lift (pullback.fst H.q (spf τ) ≫ C.π) (pullback.snd H.q (spf τ) ≫ gen O' K) (pullback_square_commutes τ φ C hφ)

private theorem piY_fst : piY τ φ C hφ ≫ pullback.fst C.p (spf φ) = pullback.fst H.q (spf τ) ≫ C.π := pullback.lift_fst _ _ _

private theorem piY_snd : piY τ φ C hφ ≫ pullback.snd C.p (spf φ) = pullback.snd H.q (spf τ) ≫ gen O' K := pullback.lift_snd _ _ _

private def wG : pullback (pullback.snd C.p (spf φ)) (gen O' K) ⟶ pullback C.p (gen O k) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ spf τ) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, gen_sq τ φ hφ])

private theorem wG_fst : wG τ φ C hφ ≫ pullback.fst C.p (gen O k) =
    pullback.fst (pullback.snd C.p (spf φ)) (gen O' K) ≫ pullback.fst C.p (spf φ) := pullback.lift_fst _ _ _

private theorem wG_snd : wG τ φ C hφ ≫ pullback.snd C.p (gen O k) =
    pullback.snd (pullback.snd C.p (spf φ)) (gen O' K) ≫ spf τ := pullback.lift_snd _ _ _

private theorem sqG : IsPullback (wG τ φ C hφ) (pullback.snd (pullback.snd C.p (spf φ)) (gen O' K))
    (pullback.snd C.p (gen O k)) (spf τ) := by
  have a := IsPullback.of_hasPullback (pullback.snd C.p (spf φ)) (gen O' K)
  have b := IsPullback.of_hasPullback C.p (spf φ)
  have c : IsPullback (pullback.fst (pullback.snd C.p (spf φ)) (gen O' K) ≫ pullback.fst C.p (spf φ))
      (pullback.snd (pullback.snd C.p (spf φ)) (gen O' K)) C.p (gen O' K ≫ spf φ) := a.paste_horiz b
  rw [gen_sq τ φ hφ, ← wG_fst τ φ C hφ] at c
  exact IsPullback.of_right c (wG_snd τ φ C hφ) (IsPullback.of_hasPullback C.p (gen O k))

private def piK' : pullback H.q (spf τ) ⟶ pullback (pullback.snd C.p (spf φ)) (gen O' K) :=
  pullback.lift (piY τ φ C hφ) (pullback.snd H.q (spf τ)) (piY_snd τ φ C hφ)

private theorem piK'_fst : piK' τ φ C hφ ≫ pullback.fst (pullback.snd C.p (spf φ)) (gen O' K) = piY τ φ C hφ := pullback.lift_fst _ _ _

private theorem piK'_snd : piK' τ φ C hφ ≫ pullback.snd (pullback.snd C.p (spf φ)) (gen O' K) = pullback.snd H.q (spf τ) :=
  pullback.lift_snd _ _ _

private theorem sqPi : IsPullback (pullback.fst H.q (spf τ)) (piK' τ φ C hφ) (piK C) (wG τ φ C hφ) := by
  refine sq_up (piK_snd C) (IsPullback.of_hasPullback H.q (spf τ)) (sqG τ φ C hφ) ?_ (piK'_snd τ φ C hφ)
  apply pullback.hom_ext
  · rw [Category.assoc, wG_fst, ← Category.assoc, piK'_fst, piY_fst, Category.assoc, pullback.lift_fst]
  · rw [Category.assoc, wG_snd, ← Category.assoc, piK'_snd, Category.assoc, piK_snd, pullback.condition]

private theorem a_q (δ : C.Δ) : C.a δ ≫ H.q = H.q := by
  obtain ⟨h, -⟩ := id C.spl
  have := congrArg (· ≫ pullback.snd C.p (gen O k)) (h δ)
  simpa only [Category.assoc, pullback.lift_snd] using this

variable (H) in

private abbrev sB (g : H.Γ) : pullback (H.s g ≫ H.q) (spf τ) ⟶ pullback H.q (spf τ) := bcMap (spf τ) (H.s g) rfl

variable (H) in

private abbrev tB (g : H.Γ) : pullback (H.s g ≫ H.q) (spf τ) ⟶ pullback H.q (spf τ) := bcMap (spf τ) (H.t g) (H.comm g)

private abbrev aB (δ : C.Δ) : pullback H.q (spf τ) ⟶ pullback H.q (spf τ) := bcMap (spf τ) (C.a δ) (a_q C δ)

private theorem a_spl : Splits (piK' τ φ C hφ) (piK' τ φ C hφ) (aB τ C) := by
  haveI := C.finπ
  haveI := C.etπ
  have h0 := splits_bc.1 (piK C) (piK C) C.Δ C.a (pullback.fst H.q (spf τ)) C.spl
  have hσ : ∀ δ, aB τ C δ ≫ piK' τ φ C hφ = piK' τ φ C hφ := by
    intro δ
    obtain ⟨ha, -⟩ := id C.spl
    have e1 : piK' τ φ C hφ ≫ wG τ φ C hφ = pullback.fst H.q (spf τ) ≫ piK C := (sqPi τ φ C hφ).w.symm
    apply (sqG τ φ C hφ).hom_ext
    · rw [Category.assoc, e1, ← Category.assoc, bcMap_fst, Category.assoc, ha δ]
    · rw [Category.assoc, piK'_snd, bcMap_snd]
  refine (splits_bc.2 _ _ _ _ (sqPi τ φ C hφ) (piK' τ φ C hφ) C.Δ (aB τ C) hσ).2 ?_
  have e1 : piK' τ φ C hφ ≫ wG τ φ C hφ = pullback.fst H.q (spf τ) ≫ piK C := (sqPi τ φ C hφ).w.symm
  have e2 : (fun δ => aB τ C δ ≫ pullback.fst H.q (spf τ)) = fun δ => pullback.fst H.q (spf τ) ≫ C.a δ :=
    funext fun δ => bcMap_fst _ _ _
  rw [e1, e2]
  exact h0

private def bcC : Cover (bcAlong H τ) θ O' where
  Y := pullback C.p (spf φ)
  p := pullback.snd C.p (spf φ)
  smooth := MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback C.p (spf φ)) C.smooth
  proj := GlobalTheory.ProjSpace.isProjOver_pullback_snd φ C.proj
  π := piY τ φ C hφ
  ov := piY_snd τ φ C hφ
  Δ := C.Δ
  grp := C.grp
  fin := C.fin
  a := aB τ C
  finπ := MorphismProperty.of_isPullback (P := @IsFinite) (sqPi τ φ C hφ) C.finπ
  etπ := MorphismProperty.of_isPullback (P := @Etale) (sqPi τ φ C hφ) C.etπ
  one := by
    apply pullback.hom_ext
    · erw [bcMap_fst, C.one, Category.comp_id]
    · erw [bcMap_snd, Category.id_comp]
  mul x y := by
    apply pullback.hom_ext
    · erw [bcMap_fst, Category.assoc, bcMap_fst, ← Category.assoc, bcMap_fst, Category.assoc, C.mul]
    · erw [bcMap_snd, Category.assoc, bcMap_snd, bcMap_snd]
  spl := a_spl τ φ C hφ
  fix δ := by
    obtain ⟨g, hi, ht, hθ⟩ := C.fix δ
    have sq : IsPullback (pullback.fst (H.s g ≫ H.q) (spf τ)) (sB τ H g) (H.s g) (pullback.fst H.q (spf τ)) :=
      sq_up rfl (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback H.q (spf τ)) (bcMap_fst _ _ _) (bcMap_snd _ _ _)
    refine ⟨g, sq.isIso_snd_of_isIso, ?_, hθ⟩
    change tB τ H g = sB τ H g ≫ aB τ C δ
    apply pullback.hom_ext
    · rw [bcMap_fst, Category.assoc, bcMap_fst, ← Category.assoc, bcMap_fst, Category.assoc, ht]
    · rw [bcMap_snd, Category.assoc, bcMap_snd, bcMap_snd]
  dim := by
    obtain ⟨d, hd⟩ := C.dim
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange d
    exact ⟨d, MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) (IsPullback.of_hasPullback C.p (spf φ)) hd⟩

private theorem bcC_onto (h : C.Onto) : (bcC τ φ C hφ).Onto :=
  MorphismProperty.of_isPullback (P := @Surjective) (sqPi τ φ C hφ) h

private theorem bcC_lies (g : H.Γ) {T : Scheme.{0}} (s t : T ⟶ C.Y) (m : ℕ) (hL : C.Lies g s t m) {T' : Scheme.{0}}
    (v : T' ⟶ T) (s' t' : T' ⟶ pullback C.p (spf φ)) (hv : IsPullback v s' s (pullback.fst C.p (spf φ)))
    (ht : t' ≫ pullback.fst C.p (spf φ) = v ≫ t) (hp : t' ≫ pullback.snd C.p (spf φ) = s' ≫ pullback.snd C.p (spf φ)) :
    (bcC τ φ C hφ).Lies g s' t' m := by
  obtain ⟨hm, κ, h, h2, hF⟩ := hL
  have hsf : sB τ H g ≫ pullback.fst H.q (spf τ) = pullback.fst (H.s g ≫ H.q) (spf τ) ≫ H.s g := bcMap_fst _ _ _
  have htf : tB τ H g ≫ pullback.fst H.q (spf τ) = pullback.fst (H.s g ≫ H.q) (spf τ) ≫ H.t g := bcMap_fst _ _ _
  have hss : sB τ H g ≫ pullback.snd H.q (spf τ) = pullback.snd (H.s g ≫ H.q) (spf τ) := bcMap_snd _ _ _
  have hts : tB τ H g ≫ pullback.snd H.q (spf τ) = pullback.snd (H.s g ≫ H.q) (spf τ) := bcMap_snd _ _ _
  have l1 : (pullback.fst (H.s g ≫ H.q) (spf τ) ≫ κ) ≫ s = (sB τ H g ≫ piY τ φ C hφ) ≫ pullback.fst C.p (spf φ) := by
    rw [Category.assoc, Category.assoc, piY_fst, ← Category.assoc (sB τ H g), hsf, Category.assoc, h]
  have k1 : hv.lift _ _ l1 ≫ v = pullback.fst (H.s g ≫ H.q) (spf τ) ≫ κ := hv.lift_fst _ _ _
  have k2 : hv.lift _ _ l1 ≫ s' = sB τ H g ≫ piY τ φ C hφ := hv.lift_snd _ _ _
  generalize hv.lift _ _ l1 = κ' at k1 k2
  have e1 : κ' ≫ t' = tB τ H g ≫ piY τ φ C hφ := by
    apply pullback.hom_ext
    · rw [Category.assoc, ht, ← Category.assoc, k1, Category.assoc, Category.assoc, piY_fst, h2, ← Category.assoc (tB τ H g), htf,
        Category.assoc]
    · rw [Category.assoc, hp, ← Category.assoc, k2, Category.assoc, Category.assoc, piY_snd, ← Category.assoc, ← Category.assoc, hss, hts]

  let b : pullback (piY τ φ C hφ) s' ⟶ pullback C.π s :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst H.q (spf τ)) (pullback.snd _ _ ≫ v) (by
      rw [Category.assoc, ← piY_fst τ φ C hφ, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, hv.w])
  have b1 : b ≫ pullback.fst C.π s = pullback.fst (piY τ φ C hφ) s' ≫ pullback.fst H.q (spf τ) := pullback.lift_fst _ _ _
  have b2 : b ≫ pullback.snd C.π s = pullback.snd (piY τ φ C hφ) s' ≫ v := pullback.lift_snd _ _ _
  have sA : IsPullback (pullback.fst (piY τ φ C hφ) s') (b ≫ pullback.snd C.π s) (pullback.fst H.q (spf τ) ≫ C.π) s := by
    rw [b2, ← piY_fst τ φ C hφ]
    exact (IsPullback.of_hasPullback (piY τ φ C hφ) s').paste_vert hv.flip
  have sB' : IsPullback (pullback.fst (piY τ φ C hφ) s') b (pullback.fst H.q (spf τ)) (pullback.fst C.π s) :=
    IsPullback.of_bot sA b1.symm (IsPullback.of_hasPullback C.π s)
  have sC : IsPullback b (pullback.fst (piY τ φ C hφ) s' ≫ pullback.snd H.q (spf τ)) (pullback.fst C.π s ≫ H.q) (spf τ) :=
    sB'.flip.paste_vert (IsPullback.of_hasPullback H.q (spf τ))
  have h' : sB τ H g ≫ piY τ φ C hφ = κ' ≫ s' := k2.symm
  have sq : IsPullback (pullback.fst (H.s g ≫ H.q) (spf τ)) (pullback.lift (sB τ H g) κ' h') (pullback.lift (H.s g) κ h) b := by
    refine sq_up (by rw [pullback.lift_fst_assoc]) (IsPullback.of_hasPullback _ _) sC ?_ ?_
    · apply pullback.hom_ext
      · rw [Category.assoc, b1, ← Category.assoc, pullback.lift_fst, hsf, Category.assoc, pullback.lift_fst]
      · rw [Category.assoc, b2, ← Category.assoc, pullback.lift_snd, k1, Category.assoc, pullback.lift_snd]
    · rw [← Category.assoc, pullback.lift_fst, hss]
  exact ⟨hm, κ', h', e1, fEt_bc.1 _ _ _ _ m sq hF⟩

private theorem bcC_good (h : C.Good) : (bcC τ φ C hφ).Good := by
  intro g
  obtain ⟨T, s, t, d, m, hs, hst, hL⟩ := h g
  have hv := IsPullback.of_hasPullback s (pullback.fst C.p (spf φ))
  have c : (pullback.fst s (pullback.fst C.p (spf φ)) ≫ t) ≫ C.p =
      (pullback.snd s (pullback.fst C.p (spf φ)) ≫ pullback.snd C.p (spf φ)) ≫ spf φ := by
    rw [Category.assoc, hst, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, pullback.condition]
  have sq := IsPullback.of_hasPullback C.p (spf φ)
  exact ⟨pullback s (pullback.fst C.p (spf φ)), pullback.snd _ _, sq.lift _ _ c, d, m, fEt_bc.1 _ _ _ _ d hv hs,
    sq.lift_snd _ _ _, bcC_lies τ φ C hφ g s t m hL _ _ _ hv (sq.lift_fst _ _ _) (sq.lift_snd _ _ _)⟩

end

theorem bcCover : BcCover := by
  intro k K O O' L _ _ _ _ _ _ _ τ φ hφ H θ C
  refine ⟨bcC τ φ C hφ, pullback.fst C.p (spf φ), IsPullback.of_hasPullback C.p (spf φ), piY_fst τ φ C hφ,
    bcC_onto τ φ C hφ, bcC_good τ φ C hφ, ?_⟩
  intro g T s t m _ hL T' v s' t' hv ht hp
  exact bcC_lies τ φ C hφ g s t m hL v s' t' hv ht hp

end UpperTheory.Gal.Seam

end
