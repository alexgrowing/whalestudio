import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PlaceData
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ IsWt fib)
open UpperTheory.Gal UpperTheory.Gal.Mod UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Mod.FixedDescent

private theorem isUnit_nat {k : Type} [Field k] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) (m : ℕ)
    (h : (m : k) ≠ 0) : IsUnit (m : Γ(X, ⊤)) := by
  have := (h.isUnit).map ((q.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  simpa using this

private theorem isWt_one {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Etale p] : IsWt p (Wt.const Z 1) := by
  have h := TranscendenceTraces.multBasic_holds.2.2 p
  rw [← h]
  exact TranscendenceTraces.wtFlat_holds p

private theorem fin_of_pb {A B C D : Scheme.{0}} {u : A ⟶ B} {s : A ⟶ C} {p : B ⟶ D} {e : C ⟶ D}
    (h : IsPullback u s p e) [IsFinite p] : IsFinite s :=
  MorphismProperty.of_isPullback (P := @IsFinite) h ‹_›

private theorem et_of_pb {A B C D : Scheme.{0}} {u : A ⟶ B} {s : A ⟶ C} {p : B ⟶ D} {e : C ⟶ D}
    (h : IsPullback u s p e) [Etale p] : Etale s :=
  MorphismProperty.of_isPullback (P := @Etale) h ‹_›

section Geo
variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]

private theorem gm_fst {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    (hu : u ≫ q = p) : geomMap Ω p u hu ≫ pullback.fst _ _ = pullback.fst _ _ ≫ u := pullback.lift_fst _ _ _

private theorem gm_snd {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    (hu : u ≫ q = p) : geomMap Ω p u hu ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

private theorem gm_isIso {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    [IsIso u] (hu : u ≫ q = p) : IsIso (geomMap Ω p u hu) := by
  have hv : inv u ≫ p = q := by rw [← hu]; simp
  refine ⟨geomMap Ω q (inv u) hv, ?_, ?_⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, gm_fst, reassoc_of% (gm_fst Ω p u hu)]; simp
    · rw [Category.assoc, gm_snd, gm_snd, Category.id_comp]
  · apply pullback.hom_ext
    · rw [Category.assoc, gm_fst, reassoc_of% (gm_fst Ω q (inv u) hv)]; simp
    · rw [Category.assoc, gm_snd, gm_snd, Category.id_comp]

private theorem gm_pb {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    (hu : u ≫ q = p) :
    IsPullback (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) (geomMap Ω p u hu) u
      (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) := by
  subst hu
  refine IsPullback.of_bot (v₂₁ := pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) (v₂₂ := q)
    (h₃₁ := Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ?_ (gm_fst Ω _ _ _).symm (IsPullback.of_hasPullback q _)
  rw [gm_snd]
  exact IsPullback.of_hasPullback _ _

private theorem splits_geom {Z Y : Scheme.{0}} (qZ : Z ⟶ Spec (CommRingCat.of k)) {qY : Y ⟶ Spec (CommRingCat.of k)}
    (u : Z ⟶ Y) (hu : u ≫ qY = qZ) {J : Type} [Finite J] (a : J → (Z ⟶ Z)) (ha : ∀ j, a j ≫ qZ = qZ)
    (h : Splits u u a) :
    Splits (geomMap Ω qZ u hu) (geomMap Ω qZ u hu) fun j => geomMap Ω qZ (a j) (ha j) := by
  obtain ⟨hs, hi⟩ := h
  have hA : ∀ j, geomMap Ω qZ (a j) (ha j) ≫ geomMap Ω qZ u hu = geomMap Ω qZ u hu := fun j => by
    apply pullback.hom_ext
    · rw [Category.assoc, gm_fst, reassoc_of% (gm_fst Ω qZ (a j) (ha j)), hs j]
    · rw [Category.assoc, gm_snd, gm_snd]
  refine ⟨hA, ?_⟩
  set G := geomMap Ω qZ u hu with hG
  set b := Spec.map (CommRingCat.ofHom (algebraMap k Ω)) with hb
  have hf : (pullback.fst G G ≫ pullback.fst qZ b) ≫ u = (pullback.snd G G ≫ pullback.fst qZ b) ≫ u := by
    have h1 : pullback.fst qZ b ≫ u = G ≫ pullback.fst qY b := (gm_fst Ω qZ u hu).symm
    rw [Category.assoc, Category.assoc, h1, pullback.condition_assoc]
  let f : pullback G G ⟶ pullback u u := pullback.lift _ _ hf
  have hf1 : f ≫ pullback.fst u u = pullback.fst G G ≫ pullback.fst qZ b := pullback.lift_fst _ _ _
  have hf2 : f ≫ pullback.snd u u = pullback.snd G G ≫ pullback.fst qZ b := pullback.lift_snd _ _ _
  have hout : IsPullback (f ≫ pullback.fst u u) (pullback.snd G G) u (pullback.fst qZ b ≫ u) := by
    have h1 := (IsPullback.of_hasPullback G G).paste_horiz (gm_pb Ω qZ u hu)
    rw [gm_fst, ← hf1] at h1
    exact h1
  have hL : IsPullback f (pullback.snd G G) (pullback.snd u u) (pullback.fst qZ b) :=
    IsPullback.of_right hout hf2 (IsPullback.of_hasPullback u u)
  have hR : IsPullback (pullback.snd G G ≫ pullback.snd qZ b) f b (pullback.snd u u ≫ qZ) :=
    hL.flip.paste_horiz (IsPullback.of_hasPullback qZ b).flip
  have hsq : ∀ j, IsPullback (pullback.lift (geomMap Ω qZ (a j) (ha j)) (𝟙 _) (by rw [hA j, Category.id_comp]))
      (pullback.fst qZ b) f (pullback.lift (a j) (𝟙 Z) (by rw [hs j, Category.id_comp])) := fun j => by
    refine IsPullback.of_right ?_ ?_ hR
    · rw [pullback.lift_snd_assoc, Category.id_comp, pullback.lift_snd_assoc, Category.id_comp]
      exact (IsPullback.of_hasPullback qZ b).flip
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hf1, pullback.lift_fst_assoc, pullback.lift_fst]
        exact gm_fst Ω qZ (a j) (ha j)
      · rw [Category.assoc, Category.assoc, hf2, pullback.lift_snd_assoc, pullback.lift_snd, Category.id_comp,
          Category.comp_id]
  have key := FinitaryPreExtensive.isIso_sigmaDesc_fst
    (fun j => pullback.lift (a j) (𝟙 Z) (by rw [hs j, Category.id_comp])) f hi
  have heq : (Sigma.desc (fun j => pullback.lift (geomMap Ω qZ (a j) (ha j)) (𝟙 _) (by rw [hA j, Category.id_comp])) :
      ∐ (fun _ : J => pullback qZ b) ⟶ pullback G G) =
      (Sigma.mapIso fun j => (hsq j).isoPullback).hom ≫ Sigma.desc fun j => pullback.fst _ _ := by
    refine Sigma.hom_ext _ _ fun j => ?_
    simp [IsPullback.isoPullback_hom_fst]
    rfl
  change IsIso (Sigma.desc (fun j => pullback.lift (geomMap Ω qZ (a j) (ha j)) (𝟙 _) (by rw [hA j, Category.id_comp])) :
      ∐ (fun _ : J => pullback qZ b) ⟶ pullback G G)
  rw [heq]
  infer_instance

end Geo

private theorem splits_fin {Z Y W : Scheme.{0}} {s : Y ⟶ Z} {c : W ⟶ Z} {J : Type} {σ : J → (W ⟶ Y)} (h : Splits s c σ)
    {m : ℕ} (e : Fin m ≃ J) : Splits s c fun i => σ (e i) := by
  obtain ⟨hs, hi⟩ := h
  refine ⟨fun i => hs _, ?_⟩
  have heq : (Sigma.desc (fun i => pullback.lift (σ (e i)) (𝟙 W) (by rw [hs (e i), Category.id_comp])) :
      ∐ (fun _ : Fin m => W) ⟶ pullback s c) =
      (Sigma.reindex e (fun _ : J => W)).hom ≫ Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hs j, Category.id_comp]) := by
    refine Sigma.hom_ext _ _ fun i => ?_
    have hr : Sigma.ι (fun _ : Fin m => W) i ≫ (Sigma.reindex e (fun _ : J => W)).hom = Sigma.ι (fun _ : J => W) (e i) :=
      Sigma.ι_reindex_hom e (fun _ : J => W) i
    rw [Sigma.ι_desc, ← Category.assoc, hr, Sigma.ι_desc]
  rw [heq]
  infer_instance

private theorem pullQ_comp (l : ℕ) [Fact l.Prime] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = pullHQ l f n i ∘ₗ pullHQ l g n i := by
  unfold pullHQ; rw [pullHl_comp]; exact LinearMap.baseChange_comp _ _

private theorem tr_pull_iso (l : ℕ) [Fact l.Prime] {A B : Scheme.{0}} (p : A ⟶ B) [IsIso p] (hl : IsUnit (l : Γ(B, ⊤)))
    (n i : ℤ) : trHQ l p (Wt.const A 1) n i ∘ₗ pullHQ l (sch.map p) n i = LinearMap.id := by
  have hw : (Wt.const A 1).push p = Wt.const B 1 := by
    funext Ω _ _ x
    have hfib : fib p x = {x ≫ inv p} := by
      ext z
      constructor
      · intro h
        have h' : z ≫ p = x := h
        rw [Set.mem_singleton_iff, ← h']
        simp
      · intro h
        rw [Set.mem_singleton_iff] at h
        change z ≫ p = x
        rw [h]
        simp
    change ∑ᶠ z ∈ fib p x, (1 : ℤ) = 1
    rw [hfib, finsum_mem_singleton]
  have h := TranscendenceTraces.adic.2.2.2.2.1 l n i p (Wt.const A 1) 1 (isWt_one p) hl hw
  simpa using h

private theorem fEt_iso {Y X : Scheme.{0}} (f : Y ⟶ X) [IsIso f] : FEt f 1 :=
  ⟨inferInstance, inferInstance, fun K _ _ x => by
    have : Unique {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ f = x} :=
      ⟨⟨⟨x ≫ inv f, by simp⟩⟩, fun a => Subtype.ext (show a.1 = x ≫ inv f from (cancel_mono f).1 (by rw [a.2]; simp))⟩
    exact Nat.card_unique⟩

private theorem baseChange_finsum {R A M N ι : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (s : Finset ι) (f : ι → M →ₗ[R] N) :
    (∑ i ∈ s, f i).baseChange A = ∑ i ∈ s, (f i).baseChange A := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.baseChange_add, ih]

end UpperTheory.Gal.Mod.FixedDescent

open UpperTheory.Gal.Mod.FixedDescent in
theorem UpperTheory.Gal.Mod.fixDesc :
    HopOp → FixDesc := by
  intro hOp
  unfold FixDesc
  intro l _ k L _ _ _ H θ O _ _ C Ω _ _ hl x hx
  have hlΩ : (l : Ω) ≠ 0 := hl.ne_zero
  have hu : pullback.lift C.π H.q C.ov ≫ pullback.snd C.p (sp (algebraMap O k)) = H.q := pullback.lift_snd _ _ _
  obtain ⟨hs0, hi0⟩ := id C.spl
  have ha : ∀ δ, C.a δ ≫ H.q = H.q := fun δ => by
    calc C.a δ ≫ H.q = C.a δ ≫ pullback.lift C.π H.q C.ov ≫ pullback.snd C.p (sp (algebraMap O k)) := by rw [hu]
      _ = H.q := by rw [← Category.assoc, hs0 δ, hu]
  haveI : IsFinite (pullback.lift C.π H.q C.ov) := C.finπ
  haveI : Etale (pullback.lift C.π H.q C.ov) := C.etπ
  haveI hF : IsFinite (piG C Ω) := fin_of_pb (gm_pb Ω H.q (pullback.lift C.π H.q C.ov) hu)
  haveI hE : Etale (piG C Ω) := et_of_pb (gm_pb Ω H.q (pullback.lift C.π H.q C.ov) hu)
  let aΩ : C.Δ → (H.geomZ Ω ⟶ H.geomZ Ω) := fun δ => geomMap Ω H.q (C.a δ) (ha δ)
  have hS : Splits (piG C Ω) (piG C Ω) aΩ := splits_geom Ω H.q (pullback.lift C.π H.q C.ov) hu C.a ha C.spl
  let e : Fin (Nat.card C.Δ) ≃ C.Δ := (Finite.equivFin C.Δ).symm
  obtain ⟨hs', hi'⟩ := splits_fin hS e
  have hlS := isUnit_nat (pullback.snd (pullback.snd C.p (sp (algebraMap O k))) (sp (algebraMap k Ω))) l hlΩ
  have hlZ := isUnit_nat (pullback.snd H.q (sp (algebraMap k Ω))) l hlΩ
  have hT : ∀ n : ℤ, pullHQ l (sch.map (piG C Ω)) n 0 ∘ₗ trHQ l (piG C Ω) (Wt.const _ 1) n 0 =
      ∑ j, pullHQ l (sch.map (aΩ (e j))) n 0 := fun n =>
    TranscendenceTraces.adic.2.2.2.2.2.2.2.2.2 l n 0 (piG C Ω) hlS _ (piG C Ω) _ (fun j => aΩ (e j)) hs' hi'
  have hopE : ∀ δ, ∃ g, hop l H Ω g = pullTot l (sch.map (aΩ δ)) ∧ θ g = 1 := fun δ => by
    obtain ⟨g, hiso, ht, h1⟩ := C.fix δ
    haveI := hiso
    have e1 := hOp l k H Ω hl g 1 (fEt_iso _)
    haveI hi2 : IsIso (H.sΩ Ω g) := gm_isIso Ω _ _ _
    have e2 : H.tΩ Ω g = H.sΩ Ω g ≫ aΩ δ := by
      apply pullback.hom_ext
      · change geomMap Ω (H.s g ≫ H.q) (H.t g) (H.comm g) ≫ _ =
          (geomMap Ω (H.s g ≫ H.q) (H.s g) rfl ≫ geomMap Ω H.q (C.a δ) (ha δ)) ≫ _
        rw [Category.assoc, gm_fst, gm_fst, reassoc_of% (gm_fst Ω (H.s g ≫ H.q) (H.s g) rfl), ht]
      · change geomMap Ω (H.s g ≫ H.q) (H.t g) (H.comm g) ≫ _ =
          (geomMap Ω (H.s g ≫ H.q) (H.s g) rfl ≫ geomMap Ω H.q (C.a δ) (ha δ)) ≫ _
        rw [Category.assoc, gm_snd, gm_snd, gm_snd]
    refine ⟨g, ?_, h1⟩
    rw [e1]
    unfold pullTot
    congr 1
    funext n
    rw [e2, Functor.map_comp, pullQ_comp, ← LinearMap.comp_assoc, tr_pull_iso l _ hlZ, LinearMap.id_comp]
  have hfix : ∀ δ, (pullTot l (sch.map (aΩ δ))).baseChange L x = x := fun δ => by
    obtain ⟨g, hg, h1⟩ := hopE δ
    have h2 := Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hx g)
    rw [hg, h1, one_smul] at h2
    exact h2
  let Tr : Htot l (sch.obj (H.geomZ Ω)) →ₗ[ℚ_[l]] Htot l (sch.obj (geom Ω (pullback.snd C.p (sp (algebraMap O k))))) :=
    DirectSum.lmap fun n : ℤ => trHQ l (piG C Ω) (Wt.const _ 1) n 0
  have hPT : pullTot l (sch.map (piG C Ω)) ∘ₗ Tr = ∑ j, pullTot l (sch.map (aΩ (e j))) := by
    refine DirectSum.linearMap_ext _ fun n => LinearMap.ext fun z => ?_
    have h3 := LinearMap.congr_fun (hT n) z
    simp only [LinearMap.comp_apply, LinearMap.sum_apply] at h3 ⊢
    simp only [Tr, pullTot, DirectSum.lmap_lof]
    rw [h3, map_sum]
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[l] L).injective
  have hc : (Nat.card C.Δ : L) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  refine ⟨(Nat.card C.Δ : L)⁻¹ • Tr.baseChange L x, ?_⟩
  have h4 : (pullTot l (sch.map (piG C Ω))).baseChange L (Tr.baseChange L x) = (Nat.card C.Δ : L) • x := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hPT, baseChange_finsum, LinearMap.sum_apply]
    simp only [hfix, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_smul_eq_nsmul]
  rw [map_smul, h4, smul_smul, inv_mul_cancel₀ hc, one_smul]
