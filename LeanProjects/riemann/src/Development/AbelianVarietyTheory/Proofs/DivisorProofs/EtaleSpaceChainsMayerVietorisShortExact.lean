import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
universe u in
private theorem nonempty_iso_shortComplex_map_of_squares {A B : Type*} [Category A] [Category B] [Abelian A]
    [Abelian B] (T : A ⥤ B) [T.Additive]
    {W X Y Z : A} {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {W' X' Y' Z' : B} {a' : W' ⟶ X'} {b' : W' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (iW : T.obj W ≅ W') (iX : T.obj X ≅ X') (iY : T.obj Y ≅ Y') (iZ : T.obj Z ≅ Z')
    (ha : T.map a ≫ iX.hom = iW.hom ≫ a') (hb : T.map b ≫ iY.hom = iW.hom ≫ b')
    (hf : T.map f ≫ iZ.hom = iX.hom ≫ f') (hg : T.map g ≫ iZ.hom = iY.hom ≫ g')
    (w : biprod.lift a (-b) ≫ biprod.desc f g = 0) (w' : biprod.lift a' (-b') ≫ biprod.desc f' g' = 0) :
    Nonempty ((ShortComplex.mk _ _ w).map T ≅ ShortComplex.mk _ _ w') := by
  haveI : PreservesBinaryBiproducts T := preservesBinaryBiproducts_of_preservesBiproducts T
  have h₁ : iW.hom ≫ biprod.lift a' (-b') =
      T.map (biprod.lift a (-b)) ≫ (T.mapBiprod X Y ≪≫ biprod.mapIso iX iY).hom := by
    simp only [Iso.trans_hom, biprod.mapIso_hom, Functor.mapBiprod_hom]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, biprod.lift_fst,
        ← Functor.map_comp_assoc, ha]
    · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, biprod.lift_snd,
        ← Functor.map_comp_assoc, hb, Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg]
  have h₂ : (T.mapBiprod X Y ≪≫ biprod.mapIso iX iY).hom ≫ biprod.desc f' g' =
      T.map (biprod.desc f g) ≫ iZ.hom := by
    simp only [Iso.trans_hom, biprod.mapIso_hom, Category.assoc]
    rw [← cancel_epi (T.mapBiprod X Y).inv]
    apply biprod.hom_ext'
    · simp only [Iso.inv_hom_id_assoc]
      simp only [biprod.inl_map_assoc, biprod.inl_desc, Functor.mapBiprod_inv,
        biprod.inl_desc_assoc, ← Functor.map_comp_assoc, hf]
    · simp only [Iso.inv_hom_id_assoc]
      simp only [biprod.inr_map_assoc, biprod.inr_desc, Functor.mapBiprod_inv,
        biprod.inr_desc_assoc, ← Functor.map_comp_assoc, hg]
  exact ⟨ShortComplex.isoMk iW (T.mapBiprod X Y ≪≫ biprod.mapIso iX iY) iZ h₁ h₂⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
universe u in

theorem _root_.GlobalTheory.EtC.mv_map_shortExact {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B] (T : A ⥤ B) [T.Additive]
    {W X Y Z : A} {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {W' X' Y' Z' : B} {a' : W' ⟶ X'} {b' : W' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (iW : T.obj W ≅ W') (iX : T.obj X ≅ X') (iY : T.obj Y ≅ Y') (iZ : T.obj Z ≅ Z')
    (ha : T.map a ≫ iX.hom = iW.hom ≫ a') (hb : T.map b ≫ iY.hom = iW.hom ≫ b')
    (hf : T.map f ≫ iZ.hom = iX.hom ≫ f') (hg : T.map g ≫ iZ.hom = iY.hom ≫ g')
    (w : biprod.lift a (-b) ≫ biprod.desc f g = 0) (w' : biprod.lift a' (-b') ≫ biprod.desc f' g' = 0)
    (h : (ShortComplex.mk _ _ w').ShortExact) : ((ShortComplex.mk _ _ w).map T).ShortExact :=
  ShortComplex.shortExact_of_iso
    (Classical.choice (nonempty_iso_shortComplex_map_of_squares T iW iX iY iZ ha hb hf hg w w')).symm h

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
universe u in

theorem _root_.GlobalTheory.EtC.chainsXIso_naturality (R : Type) [CommRing R] {E E' : _root_.GlobalTheory.EtC.Spc} (f : E ⟶ E') (p : ℕ) :
    ((_root_.GlobalTheory.EtC.chains R).map f).f (-(p : ℤ)) ≫ (_root_.GlobalTheory.EtC.chainsXIso R E' p).hom =
      (_root_.GlobalTheory.EtC.chainsXIso R E p).hom ≫ (_root_.GlobalTheory.EtC.free R).map (f.app (op (SimplexCategory.mk p))) := by
  simp only [_root_.GlobalTheory.EtC.chainsXIso, _root_.GlobalTheory.EtC.chains, Functor.comp_map,
    ComplexShape.Embedding.extendFunctor_map]
  rw [HomologicalComplex.extendMap_f _ _ (i := p) (by simp)]
  simp [_root_.GlobalTheory.EtC.chainsN]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
universe u in

theorem _root_.GlobalTheory.EtC.chains_isZero_pos (R : Type) [CommRing R] (E : _root_.GlobalTheory.EtC.Spc) (i : ℤ) (hi : 0 < i) : IsZero (((_root_.GlobalTheory.EtC.chains R).obj E).X i) := by
  apply HomologicalComplex.isZero_extend_X
  intro n hn
  simp at hn
  omega

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
universe u in
private theorem exists_mapDomain_eq_of_pullback_square {S : Type*} [Ring S] {W A B C : Type*} (t : W → A) (l : W → B)
    (r : A → C) (b : B → C) (hr : Function.Injective r) (hb : Function.Injective b)
    (hcomm : ∀ w, r (t w) = b (l w)) (ht : Function.Injective t)
    (hex : ∀ a c, r a = b c → ∃ w, t w = a ∧ l w = c)
    (m : A →₀ S) (n : B →₀ S) (h : Finsupp.mapDomain r m + Finsupp.mapDomain b n = 0) :
    ∃ z : W →₀ S, Finsupp.mapDomain t z = m ∧ Finsupp.mapDomain l z = -n := by
  have hsupp : (↑m.support : Set A) ⊆ Set.range t := by
    intro a ha
    have hma : m a ≠ 0 := Finsupp.mem_support_iff.1 ha
    have hn : Finsupp.mapDomain b n (r a) ≠ 0 := by
      intro h0
      have h1 := congrArg (fun v => v (r a)) h
      simp only [Finsupp.add_apply, Finsupp.mapDomain_apply hr, h0, add_zero, Finsupp.coe_zero,
        Pi.zero_apply] at h1
      exact hma h1
    obtain ⟨c, hc⟩ : r a ∈ Set.range b := by
      by_contra hc
      exact hn (Finsupp.mapDomain_notin_range _ _ hc)
    obtain ⟨w, hw, -⟩ := hex a c hc.symm
    exact ⟨w, hw⟩
  refine ⟨Finsupp.comapDomain t m ht.injOn, Finsupp.mapDomain_comapDomain t ht m hsupp, ?_⟩
  apply Finsupp.mapDomain_injective hb
  have hneg : Finsupp.mapDomain b (-n) = -Finsupp.mapDomain b n := by
    rw [eq_neg_iff_add_eq_zero, ← Finsupp.mapDomain_add, neg_add_cancel, Finsupp.mapDomain_zero]
  rw [← Finsupp.mapDomain_comp, show b ∘ l = r ∘ t from funext fun w => (hcomm w).symm,
    Finsupp.mapDomain_comp, Finsupp.mapDomain_comapDomain t ht m hsupp, hneg]
  exact eq_neg_of_add_eq_zero_left h

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
universe u in
private theorem moduleCat_free_pullback_exact {S : Type u} [Ring S] {W A B C : Type u} (t : W ⟶ A) (l : W ⟶ B)
    (r : A ⟶ C) (b : B ⟶ C) (hsq : IsPullback t l r b) [Mono r] [Mono b]
    (w : biprod.lift ((ModuleCat.free S).map t) (-(ModuleCat.free S).map l) ≫
      biprod.desc ((ModuleCat.free S).map r) ((ModuleCat.free S).map b) = 0) :
    Mono (biprod.lift ((ModuleCat.free S).map t) (-(ModuleCat.free S).map l)) ∧
      (ShortComplex.mk _ _ w).Exact := by
  obtain ⟨hc, hinj, hex⟩ := (Types.isPullback_iff t r l b).1 hsq
  have hr : Function.Injective r := (mono_iff_injective r).1 inferInstance
  have hb : Function.Injective b := (mono_iff_injective b).1 inferInstance
  have hcomm : ∀ x, r (t x) = b (l x) := fun x => by
    simpa using congrArg (fun φ : W ⟶ C => ConcreteCategory.hom φ x) hc
  have ht : Function.Injective t := fun x y hxy => hinj x y ⟨hxy, hb (by rw [← hcomm, ← hcomm, hxy])⟩
  have hmono : Mono ((ModuleCat.free S).map t) :=
    (ModuleCat.mono_iff_injective _).2 (Finsupp.mapDomain_injective ht)
  refine ⟨?_, ?_⟩
  · have : Mono (biprod.lift ((ModuleCat.free S).map t) (-(ModuleCat.free S).map l) ≫ biprod.fst) := by
      rw [biprod.lift_fst]; exact hmono
    exact mono_of_mono _ biprod.fst
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    have htot : ∀ y : ↑((ModuleCat.free S).obj A ⊞ (ModuleCat.free S).obj B),
        ConcreteCategory.hom (biprod.inl : (ModuleCat.free S).obj A ⟶ _)
            (ConcreteCategory.hom (biprod.fst : _ ⟶ (ModuleCat.free S).obj A) y) +
          ConcreteCategory.hom (biprod.inr : (ModuleCat.free S).obj B ⟶ _)
            (ConcreteCategory.hom (biprod.snd : _ ⟶ (ModuleCat.free S).obj B) y) = y := by
      intro y
      calc _ = ConcreteCategory.hom (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr :
            (ModuleCat.free S).obj A ⊞ (ModuleCat.free S).obj B ⟶ _) y := rfl
        _ = y := by rw [biprod.total]; rfl
    have e1 : ∀ m, ConcreteCategory.hom (biprod.desc ((ModuleCat.free S).map r) ((ModuleCat.free S).map b))
        (ConcreteCategory.hom (biprod.inl : (ModuleCat.free S).obj A ⟶ (ModuleCat.free S).obj A ⊞ (ModuleCat.free S).obj B) m) = ConcreteCategory.hom ((ModuleCat.free S).map r) m :=
      fun m => by rw [← ConcreteCategory.comp_apply, biprod.inl_desc]
    have e2 : ∀ n, ConcreteCategory.hom (biprod.desc ((ModuleCat.free S).map r) ((ModuleCat.free S).map b))
        (ConcreteCategory.hom (biprod.inr : (ModuleCat.free S).obj B ⟶ (ModuleCat.free S).obj A ⊞ (ModuleCat.free S).obj B) n) = ConcreteCategory.hom ((ModuleCat.free S).map b) n :=
      fun n => by rw [← ConcreteCategory.comp_apply, biprod.inr_desc]
    have e3 : ∀ z, ConcreteCategory.hom (biprod.fst : (ModuleCat.free S).obj A ⊞ (ModuleCat.free S).obj B ⟶ (ModuleCat.free S).obj A) (ConcreteCategory.hom (biprod.lift
        ((ModuleCat.free S).map t) (-(ModuleCat.free S).map l)) z) =
          ConcreteCategory.hom ((ModuleCat.free S).map t) z :=
      fun z => by rw [← ConcreteCategory.comp_apply, biprod.lift_fst]
    have e4 : ∀ z, ConcreteCategory.hom (biprod.snd : (ModuleCat.free S).obj A ⊞ (ModuleCat.free S).obj B ⟶ (ModuleCat.free S).obj B) (ConcreteCategory.hom (biprod.lift
        ((ModuleCat.free S).map t) (-(ModuleCat.free S).map l)) z) =
          ConcreteCategory.hom (-(ModuleCat.free S).map l) z :=
      fun z => by rw [← ConcreteCategory.comp_apply, biprod.lift_snd]
    dsimp only at x₂ hx₂ ⊢
    rw [← htot x₂, map_add, e1, e2] at hx₂
    obtain ⟨z, hz1, hz2⟩ := exists_mapDomain_eq_of_pullback_square (S := S) _ _ _ _ hr hb hcomm ht hex _ _ hx₂
    refine ⟨z, ?_⟩
    rw [← htot x₂, ← htot (ConcreteCategory.hom (biprod.lift ((ModuleCat.free S).map t) (-(ModuleCat.free S).map l)) z)]
    erw [e3, e4]
    congr 2
    change -(Finsupp.mapDomain (⇑(ConcreteCategory.hom l)) z) = _
    rw [hz2]
    exact neg_neg _

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
universe u in
private theorem freePresheaf_pullback_exact (R : Type) [CommRing R]
    {P A B C : _root_.GlobalTheory.EtC.PSh} (t : P ⟶ A) (l : P ⟶ B) (r : A ⟶ C) (b : B ⟶ C)
    (hsq : IsPullback t l r b) [Mono r] [Mono b]
    (w : biprod.lift ((_root_.GlobalTheory.EtC.freeP R).map t)
        (-(_root_.GlobalTheory.EtC.freeP R).map l) ≫
      biprod.desc ((_root_.GlobalTheory.EtC.freeP R).map r)
        ((_root_.GlobalTheory.EtC.freeP R).map b) = 0) :
    Mono (biprod.lift ((_root_.GlobalTheory.EtC.freeP R).map t)
        (-(_root_.GlobalTheory.EtC.freeP R).map l)) ∧ (ShortComplex.mk _ _ w).Exact := by
  have hU : ∀ U : Schemeᵒᵖ, Mono ((ShortComplex.mk _ _ w).map ((evaluation _ _).obj U)).f ∧
      ((ShortComplex.mk _ _ w).map ((evaluation _ _).obj U)).Exact := by
    intro U
    have hsqU : IsPullback (uliftFunctor.{1, 0}.map (t.app U)) (uliftFunctor.{1, 0}.map (l.app U))
        (uliftFunctor.{1, 0}.map (r.app U)) (uliftFunctor.{1, 0}.map (b.app U)) :=
      Functor.map_isPullback uliftFunctor.{1, 0} (Functor.map_isPullback ((evaluation _ _).obj U) hsq)
    haveI : Mono (r.app U) := (NatTrans.mono_iff_mono_app r).1 inferInstance U
    haveI : Mono (b.app U) := (NatTrans.mono_iff_mono_app b).1 inferInstance U
    obtain ⟨hm, hex⟩ := moduleCat_free_pullback_exact (S := ULift.{1} R) _ _ _ _ hsqU
      (by rw [biprod.lift_desc, Preadditive.neg_comp,
        ← (ModuleCat.free (ULift.{1} R)).map_comp, ← (ModuleCat.free (ULift.{1} R)).map_comp, hsqU.w,
        add_neg_cancel])
    obtain ⟨e⟩ := nonempty_iso_shortComplex_map_of_squares ((evaluation _ _).obj U) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (a' := (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1, 0}.map (t.app U)))
      (b' := (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1, 0}.map (l.app U)))
      (f' := (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1, 0}.map (r.app U)))
      (g' := (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1, 0}.map (b.app U)))
      (by simp; rfl) (by simp; rfl) (by simp; rfl) (by simp; rfl) w
      (by rw [biprod.lift_desc, Preadditive.neg_comp,
        ← (ModuleCat.free (ULift.{1} R)).map_comp, ← (ModuleCat.free (ULift.{1} R)).map_comp, hsqU.w,
        add_neg_cancel])
    refine ⟨?_, ShortComplex.exact_of_iso e.symm hex⟩
    have : Mono (((ShortComplex.mk _ _ w).map ((evaluation _ _).obj U)).f ≫ e.hom.τ₂) := by
      rw [← e.hom.comm₁₂]
      haveI := hm
      exact mono_comp _ _
    exact mono_of_mono _ e.hom.τ₂
  refine ⟨(NatTrans.mono_iff_mono_app _).2 fun U => (hU U).1, ?_⟩
  rw [ShortComplex.exact_iff_isZero_homology]
  refine Functor.isZero _ fun U => ?_
  exact ((ShortComplex.exact_iff_isZero_homology _).1 (hU U).2).of_iso
    ((ShortComplex.mk _ _ w).mapHomologyIso ((evaluation _ _).obj U)).symm

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
universe u in
private theorem freeSheaf_pullback_shortExact (R : Type) [CommRing R]
    {P A B C : _root_.GlobalTheory.EtC.PSh} (t : P ⟶ A) (l : P ⟶ B) (r : A ⟶ C) (b : B ⟶ C)
    (hsq : IsPullback t l r b) [Mono r] [Mono b]
    (w : biprod.lift ((_root_.GlobalTheory.EtC.free R).map t)
        (-(_root_.GlobalTheory.EtC.free R).map l) ≫
      biprod.desc ((_root_.GlobalTheory.EtC.free R).map r)
        ((_root_.GlobalTheory.EtC.free R).map b) = 0)
    (hepi : Epi (biprod.desc ((_root_.GlobalTheory.EtC.free R).map r)
        ((_root_.GlobalTheory.EtC.free R).map b))) :
    (ShortComplex.mk _ _ w).ShortExact := by
  obtain ⟨hm, hex⟩ := freePresheaf_pullback_exact R t l r b hsq
    (by rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp, hsq.w,
      add_neg_cancel])
  obtain ⟨e⟩ := nonempty_iso_shortComplex_map_of_squares
    (presheafToSheaf Scheme.etaleTopology (ModuleCat (ULift.{1} R)))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (a' := (_root_.GlobalTheory.EtC.free R).map t) (b' := (_root_.GlobalTheory.EtC.free R).map l)
    (f' := (_root_.GlobalTheory.EtC.free R).map r) (g' := (_root_.GlobalTheory.EtC.free R).map b)
    (by simp; rfl) (by simp; rfl) (by simp; rfl) (by simp; rfl) _ w
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_iso e (hex.map _)) ?_ hepi
  have : Mono ((ShortComplex.mk _ _ w).f ≫ e.inv.τ₂) := by
    rw [← e.inv.comm₁₂]
    haveI := hm
    have := Functor.map_mono (presheafToSheaf Scheme.etaleTopology (ModuleCat (ULift.{1} R)))
      (biprod.lift ((_root_.GlobalTheory.EtC.freeP R).map t)
        (-(_root_.GlobalTheory.EtC.freeP R).map l))
    exact @mono_comp _ _ _ _ _ e.inv.τ₁ inferInstance _ this
  exact mono_of_mono _ e.inv.τ₂

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
universe u in

theorem _root_.GlobalTheory.EtC.mv_shortExact : ∀ (R : Type) [CommRing R] {U V E : _root_.GlobalTheory.EtC.Spc} (f : U ⟶ E) (g : V ⟶ E), _root_.GlobalTheory.EtC.Cover2 R f g → ∃ w, (ShortComplex.mk (biprod.lift ((_root_.GlobalTheory.EtC.chains R).map (pullback.fst f g)) (-(_root_.GlobalTheory.EtC.chains R).map (pullback.snd f g))) (biprod.desc ((_root_.GlobalTheory.EtC.chains R).map f) ((_root_.GlobalTheory.EtC.chains R).map g)) w).ShortExact := by
  intro R _ U V E f g hcov
  obtain ⟨hf, hg, hepi⟩ := hcov
  refine ⟨by rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp,
    pullback.condition, add_neg_cancel], ?_⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  by_cases hi : 0 < i
  · have h₁ := _root_.GlobalTheory.EtC.chains_isZero_pos R (pullback f g) i hi
    have h₃ := _root_.GlobalTheory.EtC.chains_isZero_pos R E i hi
    have h₂ : IsZero (((_root_.GlobalTheory.EtC.chains R).obj U ⊞
        (_root_.GlobalTheory.EtC.chains R).obj V).X i) := by
      have hz : ∀ {X Y : _root_.GlobalTheory.EtC.Shv R}, IsZero X → IsZero Y → IsZero (X ⊞ Y) := by
        intro X Y hX hY
        rw [IsZero.iff_id_eq_zero, ← biprod.total, hX.eq_of_tgt biprod.fst 0,
          hY.eq_of_tgt biprod.snd 0]
        simp
      exact IsZero.of_iso (hz (_root_.GlobalTheory.EtC.chains_isZero_pos R U i hi)
        (_root_.GlobalTheory.EtC.chains_isZero_pos R V i hi)) ((HomologicalComplex.eval _ _ i).mapBiprod _ _)
    refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ h₂)
      ⟨fun _ _ _ => h₁.eq_of_tgt _ _⟩ ⟨fun _ _ _ => h₃.eq_of_src _ _⟩
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
    haveI : Mono (f.app (op (SimplexCategory.mk p))) := (NatTrans.mono_iff_mono_app f).1 hf _
    haveI : Mono (g.app (op (SimplexCategory.mk p))) := (NatTrans.mono_iff_mono_app g).1 hg _
    have hsq : IsPullback ((pullback.fst f g).app (op (SimplexCategory.mk p)))
        ((pullback.snd f g).app (op (SimplexCategory.mk p))) (f.app (op (SimplexCategory.mk p)))
        (g.app (op (SimplexCategory.mk p))) :=
      Functor.map_isPullback ((evaluation _ _).obj (op (SimplexCategory.mk p)))
        (IsPullback.of_hasPullback f g)
    have hw : biprod.lift ((_root_.GlobalTheory.EtC.free R).map
          ((pullback.fst f g).app (op (SimplexCategory.mk p))))
        (-(_root_.GlobalTheory.EtC.free R).map ((pullback.snd f g).app (op (SimplexCategory.mk p)))) ≫
        biprod.desc ((_root_.GlobalTheory.EtC.free R).map (f.app (op (SimplexCategory.mk p))))
          ((_root_.GlobalTheory.EtC.free R).map (g.app (op (SimplexCategory.mk p)))) = 0 := by
      rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp, hsq.w,
        add_neg_cancel]
    exact _root_.GlobalTheory.EtC.mv_map_shortExact
      (HomologicalComplex.eval (_root_.GlobalTheory.EtC.Shv R) (ComplexShape.up ℤ) (-(p : ℤ)))
      (W := (_root_.GlobalTheory.EtC.chains R).obj (pullback f g))
      (X := (_root_.GlobalTheory.EtC.chains R).obj U) (Y := (_root_.GlobalTheory.EtC.chains R).obj V)
      (Z := (_root_.GlobalTheory.EtC.chains R).obj E)
      (a := (_root_.GlobalTheory.EtC.chains R).map (pullback.fst f g))
      (b := (_root_.GlobalTheory.EtC.chains R).map (pullback.snd f g))
      (f := (_root_.GlobalTheory.EtC.chains R).map f) (g := (_root_.GlobalTheory.EtC.chains R).map g)
      (_root_.GlobalTheory.EtC.chainsXIso R (pullback f g) p) (_root_.GlobalTheory.EtC.chainsXIso R U p)
      (_root_.GlobalTheory.EtC.chainsXIso R V p) (_root_.GlobalTheory.EtC.chainsXIso R E p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R (pullback.fst f g) p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R (pullback.snd f g) p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R f p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R g p) _ hw
      (freeSheaf_pullback_shortExact R _ _ _ _ hsq hw (hepi _))

end GlobalTheory.EtC
