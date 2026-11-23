import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

theorem etale_reindex {R S : Type} [CommRing R] [CommRing S] {σ τ : Type} (f : R →+* S) (g : τ → S) (e : σ ≃ τ)
    (h : (MvPolynomial.eval₂Hom f g).Etale) : (MvPolynomial.eval₂Hom f (g ∘ e)).Etale := by
  have heq : MvPolynomial.eval₂Hom f (g ∘ e) =
      (MvPolynomial.eval₂Hom f g).comp (MvPolynomial.renameEquiv R e).toRingEquiv.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp
  rw [heq]
  exact RingHom.Etale.respectsIso.2 _ _ h

def BChart.coordV {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {d : ℕ} {V : Z.Opens} (c : BChart q i π d V) : Coord q V (c.n + d) where
  affine := c.affine
  t := Sum.elim c.x c.t ∘ finSumFinEquiv.symm
  etale := etale_reindex _ _ _ c.etale

theorem etale_of_quot {A A' B B' : Type} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    (φ : A →+* B) (ρ : A →+* A') (σ : B →+* B') (ψ : A' →+* B') (hφ : φ.Etale) (hρ : Function.Surjective ρ)
    (hσ : Function.Surjective σ) (hsq : σ.comp φ = ψ.comp ρ) (hker : RingHom.ker σ ≤ (RingHom.ker ρ).map φ) :
    ψ.Etale := by
  classical
  have hJ : RingHom.ker σ = (RingHom.ker ρ).map φ := by
    refine le_antisymm hker ?_
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [RingHom.mem_ker] at ha
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hsq, RingHom.comp_apply, ha, map_zero]
  let _ := φ.toAlgebra
  have : Algebra.Etale A B := hφ
  let I := RingHom.ker ρ
  let eA : A ⧸ I ≃+* A' := RingHom.quotientKerEquivOfSurjective hρ
  let eB : B ⧸ I.map (algebraMap A B) ≃+* B' :=
    (Ideal.quotEquivOfEq hJ.symm).trans (RingHom.quotientKerEquivOfSurjective hσ)
  let T : TensorProduct A (A ⧸ I) B ≃+* B' :=
    ((Algebra.TensorProduct.comm A (A ⧸ I) B).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm.toRingEquiv).trans eB
  have hE : (algebraMap (A ⧸ I) (TensorProduct A (A ⧸ I) B)).Etale := by
    rw [RingHom.etale_algebraMap]
    infer_instance
  have key : ψ = (T.toRingHom.comp (algebraMap (A ⧸ I) (TensorProduct A (A ⧸ I) B))).comp eA.symm.toRingHom := by
    ext a'
    obtain ⟨a, rfl⟩ := hρ a'
    have h1 : eA.symm (ρ a) = Ideal.Quotient.mk I a := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, h1]
    change ψ (ρ a) = eB ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm
      (TensorProduct.tmul A (1 : B) (Ideal.Quotient.mk I a)))
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul, Algebra.smul_def, mul_one]
    have h2 : σ (φ a) = ψ (ρ a) := by
      rw [← RingHom.comp_apply, hsq, RingHom.comp_apply]
    rw [← h2]
    rfl
  rw [key]
  exact RingHom.Etale.respectsIso.2 _ _ (RingHom.Etale.respectsIso.1 _ _ hE)

theorem strV_comp {K : Type} [CommRing K] {W Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) (V : Z.Opens) :
    strV (i ≫ q) (i ⁻¹ᵁ V) = (i.app V).hom.comp (strV q V) := by
  simp only [strV]
  rw [← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

def BChart.coordI {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    [IsClosedImmersion i] {π : Y ⟶ Z} {d : ℕ} {V : Z.Opens} (c : BChart q i π d V) :
    Coord (i ≫ q) (i ⁻¹ᵁ V) c.n where
  affine := IsAffineHom.isAffine_preimage V c.affine
  t j := (i.app V).hom (c.x j)
  etale := by
    refine etale_of_quot (MvPolynomial.eval₂Hom (strV q V) (Sum.elim c.x c.t))
      (MvPolynomial.eval₂Hom MvPolynomial.C (Sum.elim MvPolynomial.X 0)) (i.app V).hom _ c.etale ?_
      (Scheme.Hom.app_surjective i V c.affine) ?_ ?_
    · intro p
      refine ⟨MvPolynomial.rename Sum.inl p, ?_⟩
      simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename, Sum.elim_comp_inl]
      exact MvPolynomial.eval₂_eta p
    · have ht : ∀ j, (i.app V).hom (c.t j) = 0 := fun j => by
        rw [← RingHom.mem_ker, c.ker]; exact Ideal.subset_span ⟨j, rfl⟩
      apply MvPolynomial.ringHom_ext
      · intro a; simp [strV_comp]
      · rintro (j | j) <;> simp [ht]
    · rw [c.ker, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      refine Ideal.subset_span ⟨MvPolynomial.X (Sum.inr j), ?_, by simp⟩
      simp

theorem pushout_res {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens} (hU : IsAffineOpen U)
    (hU' : IsAffineOpen U') (hV : IsAffineOpen V) (h : U' ≤ U) (e : V ≤ f ⁻¹ᵁ U) :
    IsAffineOpen (V ⊓ f ⁻¹ᵁ U') ∧
    IsPushout (f.appLE U V e) (Y.presheaf.map (homOfLE h).op)
      (X.presheaf.map (homOfLE (inf_le_left : V ⊓ f ⁻¹ᵁ U' ≤ V)).op)
      (f.appLE U' (V ⊓ f ⁻¹ᵁ U') inf_le_right) := by
  have H : IsPullback (𝟙 X) f f (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have hpb0 := Scheme.Hom.isPullback_resLE H (US := U) (UT := U') (UX := V)
    (by simpa using h) e (UY := V ⊓ f ⁻¹ᵁ U') (by simp)
  simp only [Scheme.Hom.resLE_id] at hpb0
  have hpb : IsPullback (X.homOfLE (inf_le_left : V ⊓ f ⁻¹ᵁ U' ≤ V))
      (f.resLE U' (V ⊓ f ⁻¹ᵁ U') inf_le_right) (f.resLE U V e) (Y.homOfLE h) := hpb0
  have : IsAffine V.toScheme := hV
  have : IsAffine U.toScheme := hU
  have : IsAffine U'.toScheme := hU'
  have hW : IsAffineOpen (V ⊓ f ⁻¹ᵁ U') := IsAffine.of_isIso hpb.isoPullback.hom
  refine ⟨hW, ?_⟩
  have : IsAffine (V ⊓ f ⁻¹ᵁ U').toScheme := hW
  have hS : IsPullback (Spec.map (X.homOfLE (inf_le_left : V ⊓ f ⁻¹ᵁ U' ≤ V)).appTop)
      (Spec.map (f.resLE U' (V ⊓ f ⁻¹ᵁ U') inf_le_right).appTop)
      (Spec.map (f.resLE U V e).appTop) (Spec.map (Y.homOfLE h).appTop) :=
    hpb.of_iso (Scheme.isoSpec _) (Scheme.isoSpec _) (Scheme.isoSpec _) (Scheme.isoSpec _)
      (Scheme.isoSpec_hom_naturality _).symm (Scheme.isoSpec_hom_naturality _).symm
      (Scheme.isoSpec_hom_naturality _).symm (Scheme.isoSpec_hom_naturality _).symm
  have hR : IsPullback (X.homOfLE (inf_le_left : V ⊓ f ⁻¹ᵁ U' ≤ V)).appTop.op
      (f.resLE U' (V ⊓ f ⁻¹ᵁ U') inf_le_right).appTop.op (f.resLE U V e).appTop.op
      (Y.homOfLE h).appTop.op := by
    refine IsPullback.of_map Scheme.Spec ?_ hS
    rw [← op_comp, ← op_comp, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hpb.w]
  have hP := hR.unop.flip
  refine hP.of_iso U.topIso V.topIso U'.topIso (V ⊓ f ⁻¹ᵁ U').topIso ?_ ?_ ?_ ?_
  · simp only [Scheme.Opens.topIso, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Quiver.Hom.unop_op,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  · simp only [Scheme.Opens.topIso, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Quiver.Hom.unop_op,
      Scheme.homOfLE_appTop, ← Functor.map_comp]
    rfl
  · simp only [Scheme.Opens.topIso, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Quiver.Hom.unop_op,
      Scheme.homOfLE_appTop, ← Functor.map_comp]
    rfl
  · simp only [Scheme.Opens.topIso, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Quiver.Hom.unop_op,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem pres_base_change {R S R' S' : CommRingCat.{0}} {φ : R ⟶ S} {g : R ⟶ R'} {g' : S ⟶ S'} {φ' : R' ⟶ S'}
    (hP : IsPushout φ g g' φ') {ι : Type} (u : ι → S) (hs : Function.Surjective (MvPolynomial.eval₂Hom φ.hom u)) :
    Function.Surjective (MvPolynomial.eval₂Hom φ'.hom (g'.hom ∘ u)) ∧
      RingHom.ker (MvPolynomial.eval₂Hom φ'.hom (g'.hom ∘ u)) =
        (RingHom.ker (MvPolynomial.eval₂Hom φ.hom u)).map (MvPolynomial.map g.hom) := by
  classical
  set e := MvPolynomial.eval₂Hom φ.hom u with he
  set e' := MvPolynomial.eval₂Hom φ'.hom (g'.hom ∘ u) with he'
  set K' := (RingHom.ker e).map (MvPolynomial.map g.hom) with hK'
  have hw : ∀ r, g'.hom (φ.hom r) = φ'.hom (g.hom r) := fun r =>
    RingHom.congr_fun (congrArg CommRingCat.Hom.hom hP.w) r
  have hcomm : e'.comp (MvPolynomial.map g.hom) = g'.hom.comp e := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [he, he', hw]
    · intro i
      simp [he, he']
  have hKle : K' ≤ RingHom.ker e' := by
    rw [hK', Ideal.map_le_iff_le_comap]
    intro p hp
    rw [RingHom.mem_ker] at hp
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hcomm, RingHom.comp_apply, hp, map_zero]
  let sQ : S →+* MvPolynomial ι R' ⧸ K' :=
    (Ideal.quotientMap K' (MvPolynomial.map g.hom) Ideal.le_comap_map).comp
      (RingHom.quotientKerEquivOfSurjective hs).symm.toRingHom
  have hsQ : ∀ p, sQ (e p) = Ideal.Quotient.mk K' (MvPolynomial.map g.hom p) := by
    intro p
    have h1 : (RingHom.quotientKerEquivOfSurjective hs).symm (e p) =
        Ideal.Quotient.mk (RingHom.ker e) p := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    simp only [sQ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, h1,
      Ideal.quotientMap_mk]
  let rQ : R' →+* MvPolynomial ι R' ⧸ K' := (Ideal.Quotient.mk K').comp MvPolynomial.C
  have w' : φ ≫ CommRingCat.ofHom sQ = g ≫ CommRingCat.ofHom rQ := by
    ext r
    change sQ (φ.hom r) = rQ (g.hom r)
    have hr : φ.hom r = e (MvPolynomial.C r) := by simp [he]
    rw [hr, hsQ]
    simp [rQ]
  let h := hP.desc (CommRingCat.ofHom sQ) (CommRingCat.ofHom rQ) w'
  have hl : ∀ s, h.hom (g'.hom s) = sQ s := fun s =>
    RingHom.congr_fun (congrArg CommRingCat.Hom.hom (hP.inl_desc _ _ w')) s
  have hr : ∀ r, h.hom (φ'.hom r) = rQ r := fun r =>
    RingHom.congr_fun (congrArg CommRingCat.Hom.hom (hP.inr_desc _ _ w')) r
  let eb : MvPolynomial ι R' ⧸ K' →+* S' := Ideal.Quotient.lift K' e' (fun a ha => hKle ha)
  have heb : ∀ s', eb (h.hom s') = s' := by
    have hid : h ≫ CommRingCat.ofHom eb = 𝟙 S' := by
      apply hP.hom_ext
      · ext s
        change eb (h.hom (g'.hom s)) = g'.hom s
        rw [hl]
        obtain ⟨p, rfl⟩ := hs s
        rw [hsQ]
        change e' (MvPolynomial.map g.hom p) = g'.hom (e p)
        rw [← RingHom.comp_apply, hcomm, RingHom.comp_apply]
      · ext r
        change eb (h.hom (φ'.hom r)) = φ'.hom r
        rw [hr]
        simp [rQ, eb, he']
    intro s'
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom hid) s'
  have hbe : (h.hom.comp eb).comp (Ideal.Quotient.mk K') = Ideal.Quotient.mk K' := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change h.hom (e' (MvPolynomial.C r)) = _
      rw [show e' (MvPolynomial.C r) = φ'.hom r by simp [he'], hr]
      rfl
    · intro i
      change h.hom (e' (MvPolynomial.X i)) = _
      rw [show e' (MvPolynomial.X i) = g'.hom (u i) by simp [he'], hl,
        show u i = e (MvPolynomial.X i) by simp [he], hsQ]
      simp
  refine ⟨fun s' => ?_, ?_⟩
  · obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (h.hom s')
    refine ⟨p, ?_⟩
    rw [← heb s', ← hp]
    rfl
  · refine le_antisymm (fun p hp => ?_) hKle
    rw [RingHom.mem_ker] at hp
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hpp := RingHom.congr_fun hbe p
    simp only [RingHom.comp_apply] at hpp
    rw [← hpp]
    change h.hom (e' p) = 0
    rw [hp, map_zero]

def BChart.resC {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    [IsClosedImmersion i] {π : Y ⟶ Z} {d : ℕ} {V : Z.Opens} (c : BChart q i π d V) (V' : Z.Opens) (h : V' ≤ V)
    (hV' : IsAffineOpen V') : BChart q i π d V' where
  affine := hV'
  n := c.n
  x j := rs h (c.x j)
  t j := rs h (c.t j)
  etale := by
    obtain ⟨c'', hc''⟩ := coord_res c.coordV h hV'
    have := etale_reindex (strV q V') c''.t finSumFinEquiv c''.etale
    convert this using 3
    funext j
    rcases j with j | j <;> simp [hc'', BChart.coordV]
  ker := by
    have e3 := (i.ker).map_ideal (U := ⟨V', hV'⟩) (V := ⟨V, c.affine⟩) h
    rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply, c.ker, Ideal.map_span] at e3
    rw [← e3, ← Set.range_comp]
    rfl
  C k := c.C k ⊓ π ⁻¹ᵁ V'
  C_aff k := (pushout_res π c.affine hV' (c.C_aff k) h (c.C_le k)).1
  C_le k := inf_le_right
  C_cover := by
    calc π ⁻¹ᵁ V' ≤ (⨆ k, c.C k) ⊓ π ⁻¹ᵁ V' := le_inf (fun x hx => c.C_cover (h hx)) le_rfl
      _ = ⨆ k, (c.C k ⊓ π ⁻¹ᵁ V') := iSup_inf_eq _ _
  u k j := rs (inf_le_left : c.C k ⊓ π ⁻¹ᵁ V' ≤ c.C k) (c.u k j)
  surj k := (pres_base_change (pushout_res π c.affine hV' (c.C_aff k) h (c.C_le k)).2 (c.u k) (c.surj k)).1
  rel k := by
    refine (pres_base_change (pushout_res π c.affine hV' (c.C_aff k) h (c.C_le k)).2 (c.u k) (c.surj k)).2.trans ?_
    rw [c.rel k, Ideal.map_span, Set.image_insert_eq, ← Set.range_comp]
    simp [Function.comp_def, rs]
  inter k j := by
    simp only [rs]
    rw [Scheme.basicOpen_res, ← c.inter k j]
    simp only [← SetLike.coe_set_eq, TopologicalSpace.Opens.coe_inf]
    ext x
    simp only [Set.mem_inter_iff]
    tauto

theorem chartLaws_A (K : Type) [Field K] (W Z Y : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z)
    [IsClosedImmersion i] (π : Y ⟶ Z) (d : ℕ) (V : Z.Opens) (c : BChart q i π d V) :
    (∀ V' : Z.Opens, ∀ h : V' ≤ V, IsAffineOpen V' → ∃ c' : BChart q i π d V', (∀ j, c'.t j = rs h (c.t j)) ∧
      ∀ k, c'.C k = c.C k ⊓ π ⁻¹ᵁ V') ∧
    Nonempty (Coord q V (c.n + d)) ∧ Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) c.n) := by
  exact ⟨fun V' h hV' => ⟨c.resC V' h hV', fun j => rfl, fun k => rfl⟩, ⟨c.coordV⟩, ⟨c.coordI⟩⟩

end CrystallineSemistableComparison.Onto

end
