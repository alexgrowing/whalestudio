import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsColimitPushoutUnder
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.TorsorColim

theorem exists_common_under {K : Type} [SmallCategory K] [IsFiltered K] {I : Type} [Finite I]
    (k : K) (l : I → K) (f : ∀ i, k ⟶ l i) :
    ∃ (m : K) (p : k ⟶ m) (r : ∀ i, l i ⟶ m), ∀ i, f i ≫ r i = p := by
  classical
  letI := Fintype.ofFinite I
  obtain ⟨c'⟩ := IsFiltered.cocone_nonempty (WidePushoutShape.wideSpan k l f)
  exact ⟨c'.pt, c'.ι.app none, fun i => c'.ι.app (some i), fun i => c'.w (.init i)⟩

theorem exists_stage_eq {K : Type} [SmallCategory K] [IsFiltered K] {I : Type} [Finite I]
    {R S : CommRingCat.{0}} (E : K ⥤ CommRingCat.{0}) (α : (Functor.const _).obj R ⟶ E)
    (φ : R ⟶ S) (c : Cocone E) (hc : IsColimit c) (hφ : φ.hom.EssFiniteType) {k : K}
    (a b : I → (S ⟶ E.obj k)) (ha : ∀ i, φ ≫ a i = α.app k) (hb : ∀ i, φ ≫ b i = α.app k)
    (hab : ∀ i, a i ≫ c.ι.app k = b i ≫ c.ι.app k) :
    ∃ (m : K) (p : k ⟶ m), ∀ i, a i ≫ E.map p = b i ≫ E.map p := by
  choose l f₁ f₂ h using fun i => RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit R E α φ c hc
    hφ (a i) (ha i) (b i) (hb i) (hab i)
  obtain ⟨m, p, r, hr⟩ := exists_common_under k (fun i => IsFiltered.coeq (f₁ i) (f₂ i))
    (fun i => f₁ i ≫ IsFiltered.coeqHom (f₁ i) (f₂ i))
  refine ⟨m, p, fun i => ?_⟩
  have h2 : (f₂ i ≫ IsFiltered.coeqHom (f₁ i) (f₂ i)) ≫ r i = p := by
    rw [← IsFiltered.coeq_condition]; exact hr i
  conv_lhs => rw [← hr i]
  conv_rhs => rw [← h2]
  simp only [E.map_comp, Category.assoc]
  rw [reassoc_of% (h i)]

theorem exists_stage_factor {K : Type} [SmallCategory K] [IsFiltered K] {I : Type} [Finite I]
    {R S : CommRingCat.{0}} (E : K ⥤ CommRingCat.{0}) (α : (Functor.const _).obj R ⟶ E)
    (φ : R ⟶ S) (c : Cocone E) (hc : IsColimit c) (hφ : φ.hom.FinitePresentation)
    (a : I → (S ⟶ c.pt)) (ha : ∀ i k, φ ≫ a i = α.app k ≫ c.ι.app k) :
    ∃ (m : K) (s : I → (S ⟶ E.obj m)), ∀ i, φ ≫ s i = α.app m ∧ s i ≫ c.ι.app m = a i := by
  classical
  choose l s h₁ h₂ using fun i => RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit R E α φ c
    hc hφ (a i) (ha i)
  letI := Fintype.ofFinite I
  obtain ⟨m, hm⟩ := IsFiltered.sup_objs_exists (Finset.univ.image l)
  have r : ∀ i, l i ⟶ m := fun i => (hm (Finset.mem_image_of_mem l (Finset.mem_univ i))).some
  refine ⟨m, fun i => s i ≫ E.map (r i), fun i => ⟨?_, ?_⟩⟩
  · rw [reassoc_of% (h₁ i), ← α.naturality]
    exact Category.id_comp _
  · rw [Category.assoc, c.w, ← h₂]

theorem exists_stage_action {K : Type} [SmallCategory K] [IsFiltered K] {G : Type} [Monoid G]
    [Finite G] {R S : CommRingCat.{0}} (P E : K ⥤ CommRingCat.{0})
    (β : ∀ k, R ⟶ P.obj k) (φ : R ⟶ S) (hφ : φ.hom.FinitePresentation)
    (u : P ⟶ E) (v : (Functor.const _).obj S ⟶ E)
    (hpo : ∀ k, IsPushout φ (β k) (v.app k) (u.app k))
    (c : Cocone E) (hc : IsColimit c) (τ : G → (c.pt ⟶ c.pt)) (τ1 : τ 1 = 𝟙 _)
    (τm : ∀ g h, τ (g * h) = τ h ≫ τ g)
    (τu : ∀ g k, u.app k ≫ c.ι.app k ≫ τ g = u.app k ≫ c.ι.app k) :
    ∃ (m : K) (σ : G → (E.obj m ⟶ E.obj m)), σ 1 = 𝟙 _ ∧ (∀ g h, σ (g * h) = σ h ≫ σ g) ∧
      (∀ g, u.app m ≫ σ g = u.app m) ∧ ∀ g, σ g ≫ c.ι.app m = c.ι.app m ≫ τ g := by
  let α : (Functor.const K).obj R ⟶ E := (Functor.const K).map φ ≫ v
  let w : ∀ k, S ⟶ E.obj k := fun k => v.app k
  let ι : ∀ k, E.obj k ⟶ c.pt := fun k => c.ι.app k
  have hα : ∀ k, α.app k = φ ≫ w k := fun k => rfl
  have hι : ∀ {k l} (f : k ⟶ l), E.map f ≫ ι l = ι k := fun f => c.w f
  have hw : ∀ {k l} (f : k ⟶ l), w k ≫ E.map f = w l := fun f =>
    (v.naturality f).symm.trans (Category.id_comp _)
  have hpo' : ∀ k, IsPushout φ (β k) (w k) (u.app k) := hpo
  have τu' : ∀ g k, u.app k ≫ ι k ≫ τ g = u.app k ≫ ι k := τu
  have k₀ : K := IsFiltered.nonempty.some
  have hwι : ∀ k, w k ≫ ι k = w k₀ ≫ ι k₀ := fun k => by
    rw [← hι (IsFiltered.leftToMax k k₀), ← hι (IsFiltered.rightToMax k k₀), reassoc_of% hw,
      reassoc_of% hw]
  obtain ⟨k, s, hs⟩ := exists_stage_factor E α φ c hc hφ (fun g : G => w k₀ ≫ ι k₀ ≫ τ g)
    (fun g k => by
      change φ ≫ w k₀ ≫ ι k₀ ≫ τ g = (φ ≫ w k) ≫ ι k
      rw [← reassoc_of% (hwι k), (hpo' k).w, reassoc_of% (hpo' k).w, τu', Category.assoc])
  have hs1 : ∀ g, φ ≫ s g = φ ≫ w k := fun g => (hs g).1
  have hs2 : ∀ g, s g ≫ ι k = w k₀ ≫ ι k₀ ≫ τ g := fun g => (hs g).2
  let σ : ∀ {l} (_ : k ⟶ l), G → (E.obj l ⟶ E.obj l) := fun {l} f g =>
    (hpo' l).desc (s g ≫ E.map f) (u.app l) (by
      rw [reassoc_of% hs1, hw, (hpo' l).w])
  have σw : ∀ {l} (f : k ⟶ l) g, w l ≫ σ f g = s g ≫ E.map f := fun f g => (hpo' _).inl_desc _ _ _
  have σu : ∀ {l} (f : k ⟶ l) g, u.app l ≫ σ f g = u.app l := fun f g => (hpo' _).inr_desc _ _ _
  have σι : ∀ {l} (f : k ⟶ l) g, σ f g ≫ ι l = ι l ≫ τ g := fun {l} f g => by
    apply (hpo' l).hom_ext
    · rw [reassoc_of% σw, hι, hs2, reassoc_of% (hwι l)]
    · rw [reassoc_of% σu, τu']
  have σmap : ∀ {l} (f : k ⟶ l) g, σ (𝟙 k) g ≫ E.map f = E.map f ≫ σ f g := fun {l} f g => by
    apply (hpo' k).hom_ext
    · rw [reassoc_of% σw, reassoc_of% hw, σw, E.map_id, Category.id_comp]
    · rw [reassoc_of% σu, ← u.naturality_assoc, σu, u.naturality]
  obtain ⟨m, p, hp⟩ := exists_stage_eq (I := Option (G × G)) E α φ c hc
    (RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_finitePresentation hφ)) (k := k)
    (fun i => i.elim (s 1) (fun x => s (x.1 * x.2)))
    (fun i => i.elim (w k) (fun x => s x.2 ≫ σ (𝟙 k) x.1))
    (by
      rintro (_ | x)
      · exact hs1 _
      · exact hs1 _)
    (by
      rintro (_ | x)
      · rfl
      · change φ ≫ s x.2 ≫ σ (𝟙 k) x.1 = φ ≫ w k
        rw [reassoc_of% hs1, σw, E.map_id, Category.comp_id, hs1])
    (by
      rintro (_ | x)
      · change s 1 ≫ ι k = w k ≫ ι k
        rw [hs2, τ1, Category.comp_id, hwι k]
      · change s (x.1 * x.2) ≫ ι k = (s x.2 ≫ σ (𝟙 k) x.1) ≫ ι k
        rw [Category.assoc, σι, reassoc_of% hs2, hs2, τm])
  refine ⟨m, σ p, ?_, fun g h => ?_, σu p, σι p⟩
  · apply (hpo' m).hom_ext
    · rw [σw, Category.comp_id, ← hw p]
      exact hp none
    · rw [σu, Category.comp_id]
  · apply (hpo' m).hom_ext
    · rw [σw, reassoc_of% σw, ← σmap, ← Category.assoc]
      exact hp (some (g, h))
    · rw [σu, reassoc_of% σu, σu]

theorem finitePresentation_of_isPushout {R S R' S' : CommRingCat.{0}} {φ : R ⟶ S} {β : R ⟶ R'}
    {v : S ⟶ S'} {u : R' ⟶ S'} (h : IsPushout φ β v u) (hφ : φ.hom.FinitePresentation) :
    u.hom.FinitePresentation := by
  algebraize [φ.hom, β.hom, v.hom, u.hom, v.hom.comp φ.hom]
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  have : Algebra.IsPushout R S R' S' := CommRingCat.isPushout_iff_isPushout.1 h
  exact RingHom.finitePresentation_isStableUnderBaseChange R S R' S' hφ

theorem exists_algEquiv_of_isPushout {R C B D : Type} [CommRing R] [CommRing C] [CommRing B]
    [CommRing D] [Algebra R C] [Algebra R B] [Algebra C D] (ι : B →+* D)
    (h : IsPushout (CommRingCat.ofHom (algebraMap R C)) (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (algebraMap C D)) (CommRingCat.ofHom ι)) :
    ∃ e : C ⊗[R] B ≃ₐ[C] D, ∀ x y, e (x ⊗ₜ y) = algebraMap C D x * ι y := by
  algebraize [ι, (algebraMap C D).comp (algebraMap R C)]
  have : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  have : Algebra.IsPushout R C B D := CommRingCat.isPushout_iff_isPushout.1 h
  exact ⟨Algebra.IsPushout.equiv R C B D, fun x y => Algebra.IsPushout.equiv_tmul R C B D x y⟩

theorem exists_action_model_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A] (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)),
    letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) →
    ∃ (k : J) (B : Type) (_ : CommRing B) (_ : Algebra (F.obj k) B)
      (_ : Algebra.FinitePresentation (F.obj k) B)
      (actB : Multiplicative (ZMod q) →* (B ≃ₐ[F.obj k] B)),
      letI : Algebra (F.obj k) c.pt := (c.ι.app k).hom.toAlgebra;
      ∃ e : c.pt ⊗[F.obj k] B ≃ₐ[c.pt] D, ∀ (g : Multiplicative (ZMod q)) (x : c.pt ⊗[F.obj k] B),
        e (GlobalTheory.TorsorColim.bcAct c.pt actB g x) = act g (e x) := by
  intro J _ _ F c hc q hq j A _ _ _ D _ _ act
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  rintro ⟨e₀⟩
  haveI : NeZero q := ⟨hq.ne'⟩
  let φ : F.obj j ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap (F.obj j) A)
  have hφ : φ.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.2 inferInstance
  let g₀ : c.pt ⟶ CommRingCat.of D := CommRingCat.ofHom (algebraMap c.pt D)
  let h₀ : CommRingCat.of A ⟶ CommRingCat.of D :=
    CommRingCat.ofHom (e₀.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := F.obj j) (A := c.pt) (B := A)).toRingHom)
  let ιc : ∀ k, F.obj k ⟶ c.pt := fun k => c.ι.app k
  have hsq : IsPushout φ (ιc j) h₀ g₀ := by
    refine (CommRingCat.isPushout_tensorProduct (F.obj j) c.pt A).flip.of_iso (Iso.refl _)
      (Iso.refl _) (Iso.refl _) e₀.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · ext x
      exact e₀.commutes x
  obtain ⟨E, ι, u, v, ⟨hE⟩, hk⟩ :=
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J F c hc j _ _ φ h₀ g₀ hsq
  let τ : Multiplicative (ZMod q) → (CommRingCat.of D ⟶ CommRingCat.of D) := fun g =>
    CommRingCat.ofHom (act g).toRingEquiv.toRingHom
  have hτ : ∀ g, g₀ ≫ τ g = g₀ := fun g => by
    ext x
    exact (act g).commutes x
  let ι' : ∀ k, E.obj k ⟶ CommRingCat.of D := fun k => ι.app k
  let u' : ∀ k : Under j, F.obj k.right ⟶ E.obj k := fun k => u.app k
  let v' : ∀ k : Under j, CommRingCat.of A ⟶ E.obj k := fun k => v.app k
  have hu : ∀ k, u' k ≫ ι' k = ιc k.right ≫ g₀ := fun k => (hk k).2.2
  have hv : ∀ k, v' k ≫ ι' k = h₀ := fun k => (hk k).2.1
  have hpo : ∀ k : Under j, IsPushout φ (F.map k.hom) (v' k) (u' k) := fun k => (hk k).1
  obtain ⟨m, σ, σ1, σm, σu, σι⟩ := exists_stage_action (Under.forget j ⋙ F) E
    (fun k => F.map k.hom) φ hφ u v hpo (Cocone.mk _ ι) hE τ
    (by
      ext x
      change act 1 x = x
      simp)
    (fun g h => by
      ext x
      change act (g * h) x = act g (act h x)
      simp)
    (fun g k => by
      change u' k ≫ ι' k ≫ τ g = u' k ≫ ι' k
      rw [reassoc_of% hu, hτ, hu])
  letI : Algebra (F.obj m.right) (E.obj m) := (u' m).hom.toAlgebra
  letI : Algebra (F.obj m.right) c.pt := (c.ι.app m.right).hom.toAlgebra
  let σ' : Multiplicative (ZMod q) →* (E.obj m →ₐ[F.obj m.right] E.obj m) :=
    { toFun := fun g => ⟨(σ g).hom, fun x => congr(($(σu g)).hom x)⟩
      map_one' := AlgHom.ext fun x => congr(($σ1).hom x)
      map_mul' := fun g h => AlgHom.ext fun x => congr(($(σm g h)).hom x) }
  have hsq' : IsPushout (u' m) (ιc m.right) (ι' m) g₀ := by
    have hcw : F.map m.hom ≫ ιc m.right = ιc j := c.w m.hom
    refine IsPushout.of_top ?_ (hu m) (hpo m)
    rw [hv]
    exact hcw ▸ hsq
  obtain ⟨e, he⟩ := exists_algEquiv_of_isPushout (R := F.obj m.right) (C := c.pt) (B := E.obj m)
    (D := D) (ι' m).hom hsq'.flip
  refine ⟨m.right, E.obj m, inferInstance, inferInstance,
    finitePresentation_of_isPushout (hpo m) hφ,
    (AlgEquiv.algHomUnitsEquiv _ _).toMonoidHom.comp σ'.toHomUnits, e, fun g x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s b =>
    rw [bcAct_tmul, he, he, map_mul, AlgEquiv.commutes]
    congr 1
    exact congr(($(σι g)).hom b)

end GlobalTheory.TorsorColim
