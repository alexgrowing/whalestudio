import Mathlib

noncomputable section

open CategoryTheory Limits Opposite Abelian

namespace GlobalTheory.ChangeRing

universe w w' w'' v₁ v₂ v₃ u₁ u₂ u₃

section Abstract

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasExt.{w} A] [EnoughInjectives A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasExt.{w'} B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D] [HasExt.{w''} D]

attribute [local instance] Ext.subsingleton_of_injective

theorem exists_shift {Z : A} (F : A) (n : ℕ) :
    ∃ (I Q : A) (i : F ⟶ I) (q : I ⟶ Q) (h : i ≫ q = 0) (hS : (ShortComplex.mk i q h).ShortExact), Injective I ∧
      ∀ x : Ext.{w} Z F (n + 1), ∃ y : Ext.{w} Z Q n, y.comp hS.extClass rfl = x := by
  let I : InjectivePresentation F := Classical.arbitrary _
  have := I.injective
  have := I.mono
  have hS : (ShortComplex.mk _ _ (cokernel.condition I.f)).ShortExact := { exact := ShortComplex.exact_cokernel I.f }
  exact ⟨_, _, _, _, _, hS, I.injective, fun x => Ext.covariant_sequence_exact₁ _ hS x (Subsingleton.elim _ _) rfl⟩

theorem exists_epi_comp_eq_zero (n : ℕ) {P Y : A} (x : Ext.{w} P Y (n + 1)) :
    ∃ (P' : A) (p : P' ⟶ P), Epi p ∧ (Ext.mk₀ p).comp x (zero_add _) = 0 := by
  induction n generalizing Y with
  | zero =>
    obtain ⟨I, Q, i, q, h, hS, -, hx⟩ := exists_shift.{w} (Z := P) Y 0
    obtain ⟨y, rfl⟩ := hx x
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective P Q).surjective y
    have := hS.epi_g
    refine ⟨pullback g q, pullback.fst g q, inferInstance, ?_⟩
    rw [Ext.mk₀_comp_mk₀_assoc, pullback.condition, ← Ext.mk₀_comp_mk₀_assoc]
    erw [hS.comp_extClass]
    exact Ext.comp_zero _ _ _ _ _
  | succ n hn =>
    obtain ⟨I, Q, i, q, h, hS, -, hx⟩ := exists_shift.{w} (Z := P) Y (n + 1)
    obtain ⟨y, rfl⟩ := hx x
    obtain ⟨P', p, hp, h0⟩ := hn y
    refine ⟨P', p, hp, ?_⟩
    rw [← Ext.comp_assoc (Ext.mk₀ p) y hS.extClass (zero_add _) rfl (by omega), h0]
    exact Ext.zero_comp _ _ _ _ _

theorem ext_eq_zero_of_class (Y : A) (Pr : A → Prop)
    (h : ∀ {P P' : A} (p : P' ⟶ P), Epi p → Pr P → ∃ (Q : A) (q : Q ⟶ P'), Epi q ∧ Pr (kernel (q ≫ p)) ∧
      ∀ z : kernel (q ≫ p) ⟶ Y, ∃ z' : Q ⟶ Y, kernel.ι (q ≫ p) ≫ z' = z)
    (n : ℕ) {P : A} (hP : Pr P) (x : Ext.{w} P Y (n + 1)) : x = 0 := by
  induction n generalizing P with
  | zero =>
    obtain ⟨P', p, hp, h0⟩ := exists_epi_comp_eq_zero 0 x
    obtain ⟨Q, q, hq, -, hz⟩ := h p hp hP
    have hS : (ShortComplex.mk _ _ (kernel.condition (q ≫ p))).ShortExact :=
      { exact := ShortComplex.exact_kernel _ }
    obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₃ hS Y x (by
      change (Ext.mk₀ (q ≫ p)).comp x (zero_add _) = 0
      rw [← Ext.mk₀_comp_mk₀_assoc, h0]; exact Ext.comp_zero _ _ _ _ _) (n₀ := 0) rfl
    obtain ⟨z, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
    obtain ⟨z', rfl⟩ := hz z
    rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero]
    erw [hS.extClass_comp]
    exact Ext.zero_comp _ _ _ _ _
  | succ n hn =>
    obtain ⟨P', p, hp, h0⟩ := exists_epi_comp_eq_zero (n + 1) x
    obtain ⟨Q, q, hq, hK, -⟩ := h p hp hP
    have hS : (ShortComplex.mk _ _ (kernel.condition (q ≫ p))).ShortExact :=
      { exact := ShortComplex.exact_kernel _ }
    obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₃ hS Y x (by
      change (Ext.mk₀ (q ≫ p)).comp x (zero_add _) = 0
      rw [← Ext.mk₀_comp_mk₀_assoc, h0]; exact Ext.comp_zero _ _ _ _ _) (n₀ := n + 1) (by omega)
    rw [hn hK y]
    exact Ext.comp_zero _ _ _ _ _

variable (Φ : A ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

def extMap {Z : A} {Z' : B} (a : Z' ⟶ Φ.obj Z) (F : A) (n : ℕ) : Ext.{w} Z F n →+ Ext.{w'} Z' (Φ.obj F) n :=
  ((Ext.mk₀ a).precomp (Φ.obj F) (zero_add n)).comp (Φ.mapExtAddHom.{w, w'} Z F n)

omit [EnoughInjectives A] in
theorem extMap_apply {Z : A} {Z' : B} (a : Z' ⟶ Φ.obj Z) (F : A) (n : ℕ) (x : Ext.{w} Z F n) :
    extMap.{w, w'} Φ a F n x = (Ext.mk₀ a).comp (x.mapExactFunctor Φ) (zero_add n) := rfl

theorem extMap_bijective {Z : A} {Z' : B} (a : Z' ⟶ Φ.obj Z)
    (ha : ∀ F : A, Function.Bijective fun g : Z ⟶ F => a ≫ Φ.map g)
    (hI : ∀ (I : A), Injective I → ∀ (n : ℕ) (x : Ext.{w'} Z' (Φ.obj I) (n + 1)), x = 0)
    (n : ℕ) (F : A) : Function.Bijective (extMap.{w, w'} Φ a F n) := by
  induction n generalizing F with
  | zero =>
    rw [← Function.Bijective.of_comp_iff _ (Ext.mk₀_bijective Z F)]
    convert (Ext.mk₀_bijective Z' (Φ.obj F)).comp (ha F) using 1
    ext g
    simp [extMap_apply, Ext.mapExactFunctor_mk₀]
  | succ n hn =>
    obtain ⟨I, Q, i, q, h, hS, hinj, hx⟩ := exists_shift.{w} (Z := Z) F n
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (extMap.{w, w'} Φ a I n) (extMap.{w, w'} Φ a Q n) (extMap.{w, w'} Φ a F (n + 1))
      (by
        ext x
        change ((Ext.mk₀ a).comp (x.mapExactFunctor Φ) (zero_add n)).comp (Ext.mk₀ (Φ.map q)) (add_zero n) =
          (Ext.mk₀ a).comp ((x.comp (Ext.mk₀ q) (add_zero n)).mapExactFunctor Φ) (zero_add n)
        rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero])
      (by
        ext x
        change ((Ext.mk₀ a).comp (x.mapExactFunctor Φ) (zero_add n)).comp (hS.map_of_exact Φ).extClass rfl =
          (Ext.mk₀ a).comp ((x.comp hS.extClass rfl).mapExactFunctor Φ) (zero_add (n + 1))
        rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
        exact Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' Z hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' Z' (hS.map_of_exact Φ) n (n + 1) rfl))
      (hn _).surjective (hn _) hx
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ (hS.map_of_exact Φ) y₁ (hI I hinj _ _) rfl)

theorem mapExactFunctor_natTrans (Ψ : A ⥤ B) [Ψ.Additive] [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ]
    (τ : Φ ⟶ Ψ) (n : ℕ) {Z F : A} (x : Ext.{w} Z F n) :
    (x.mapExactFunctor.{w, w'} Φ).comp (Ext.mk₀ (τ.app F)) (add_zero n) =
      (Ext.mk₀ (τ.app Z)).comp (x.mapExactFunctor.{w, w'} Ψ) (zero_add n) := by
  induction n generalizing F with
  | zero =>
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective Z F).surjective x
    simp [Ext.mapExactFunctor_mk₀]
  | succ n hn =>
    obtain ⟨I, Q, i, q, h, hS, -, hx⟩ := exists_shift.{w} (Z := Z) F n
    obtain ⟨y, rfl⟩ := hx x
    obtain ⟨e, he, hnat⟩ : ∃ e : Ext.{w} Q F 1, y.comp hS.extClass rfl = y.comp e rfl ∧
        (e.mapExactFunctor.{w, w'} Φ).comp (Ext.mk₀ (τ.app F)) (add_zero 1) =
          (Ext.mk₀ (τ.app Q)).comp (e.mapExactFunctor.{w, w'} Ψ) (zero_add 1) := by
      refine ⟨hS.extClass, rfl, ?_⟩
      have h1 := (hS.map_of_exact Φ).extClass_naturality (hS.map_of_exact Ψ)
        ((ShortComplex.mk i q h).mapNatTrans τ)
      rw [← Ext.mapExactFunctor_extClass, ← Ext.mapExactFunctor_extClass] at h1
      exact h1
    rw [he, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp, Ext.comp_assoc_of_third_deg_zero, hnat,
      ← Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega), ← hn y, Ext.comp_assoc_of_second_deg_zero]

end Abstract

section Site

variable {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C)

attribute [local instance] Ext.subsingleton_of_injective

instance isGrothendieckAbelian_presheaf (R : Type 1) [CommRing R] :
    IsGrothendieckAbelian.{1} (Cᵒᵖ ⥤ ModuleCat.{1} R) where
  hasSeparator := inferInstance
  ab5OfSize := ⟨fun _ _ _ => inferInstance⟩

theorem isGrothendieckAbelian_sheaf (R : Type 1) [CommRing R] :
    IsGrothendieckAbelian.{1} (Sheaf J (ModuleCat.{1} R)) := by
  have : EssentiallySmall.{1} C := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ (ModuleCat.{1} R)

attribute [local instance] isGrothendieckAbelian_sheaf

variable {R S : Type 1} [CommRing R] [CommRing S] (f : R →+* S)

def PointwiseProjective (P : Cᵒᵖ ⥤ ModuleCat.{1} R) : Prop := ∀ U, Projective (P.obj U)

theorem pointwiseProjective_free (T : Cᵒᵖ ⥤ Type 1) : PointwiseProjective (T ⋙ ModuleCat.free R) := fun U =>
  inferInstanceAs (Projective (ModuleCat.of R (T.obj U →₀ R)))

theorem presheaf_ext_eq_zero (I : Cᵒᵖ ⥤ ModuleCat.{1} S) [Injective I] (n : ℕ) {P : Cᵒᵖ ⥤ ModuleCat.{1} R}
    (hP : PointwiseProjective P) (x : Ext.{1} P (I ⋙ ModuleCat.restrictScalars.{1} f) (n + 1)) : x = 0 := by
  refine ext_eq_zero_of_class.{1} _ PointwiseProjective ?_ n hP x
  intro P P' p hp hP
  let adj := (ModuleCat.adj R).whiskerRight Cᵒᵖ
  let q := adj.counit.app P'
  have hq : Epi q := adj.counit_epi_of_R_faithful P'
  have hS : (ShortComplex.mk _ _ (kernel.condition (q ≫ p))).ShortExact :=
    { exact := ShortComplex.exact_kernel _ }
  have hsplit (U : Cᵒᵖ) : IsSplitMono ((kernel.ι (q ≫ p)).app U) := by
    have hU := hS.map_of_exact ((evaluation Cᵒᵖ (ModuleCat.{1} R)).obj U)
    have : Projective ((ShortComplex.mk _ _ (kernel.condition (q ≫ p))).map
      ((evaluation Cᵒᵖ (ModuleCat.{1} R)).obj U)).X₃ := hP U
    exact ⟨⟨hU.splittingOfProjective.splitMono_f⟩⟩
  refine ⟨_, q, hq, fun U => ?_, fun z => ?_⟩
  · have := hsplit U
    exact @Retract.projective _ _ _ _ ⟨(kernel.ι (q ≫ p)).app U, retraction _, IsSplitMono.id _⟩
      (pointwiseProjective_free (R := R) (P' ⋙ forget _) U)
  · let adj' := (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} f).whiskerRight Cᵒᵖ
    let ι' := ((Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.extendScalars.{1, 1, 1} f)).map (kernel.ι (q ≫ p))
    have (U : Cᵒᵖ) : Mono (ι'.app U) := by
      have := hsplit U
      exact inferInstanceAs (Mono ((ModuleCat.extendScalars.{1, 1, 1} f).map ((kernel.ι (q ≫ p)).app U)))
    have : Mono ι' := NatTrans.mono_of_mono_app _
    refine ⟨adj'.homEquiv _ I (Injective.factorThru ((adj'.homEquiv _ I).symm z) ι'), ?_⟩
    refine (adj'.homEquiv_naturality_left _ _).symm.trans ?_
    rw [Injective.comp_factorThru]
    exact Equiv.apply_symm_apply _ _

def Limp (F : Sheaf J (ModuleCat.{1} R)) : Prop :=
  ∀ (n : ℕ) (P : Cᵒᵖ ⥤ ModuleCat.{1} R), PointwiseProjective P → ∀ x : Ext.{1} P F.obj (n + 1), x = 0

theorem Limp.epi {T : ShortComplex (Sheaf J (ModuleCat.{1} R))} (hT : T.ShortExact) (h : Limp J T.X₁) :
    Epi T.g.hom := by
  let T' := T.map (sheafToPresheaf J _)
  have := hT.mono_f
  have hex : T'.Exact := hT.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance
  have hm : Mono T'.f := inferInstanceAs (Mono ((sheafToPresheaf J _).map T.f))
  let m : cokernel T'.f ⟶ T'.X₃ := cokernel.desc _ T'.g T'.zero
  have hmm : Mono m := hex.mono_cokernelDesc
  have hS : (ShortComplex.mk _ _ (cokernel.condition T'.f)).ShortExact := { exact := ShortComplex.exact_cokernel _ }
  let adj := (ModuleCat.adj R).whiskerRight Cᵒᵖ
  let U := (Functor.whiskeringRight Cᵒᵖ _ _).obj (forget (ModuleCat.{1} R))
  obtain ⟨l, hl⟩ := Ext.covariant_sequence_exact₃ _ hS (Ext.mk₀ (adj.counit.app (cokernel T'.f))) rfl
    (h 0 _ (pointwiseProjective_free _) _)
  obtain ⟨l, rfl⟩ := (Ext.mk₀_bijective _ _).surjective l
  rw [Ext.mk₀_comp_mk₀] at hl
  have hl' : l ≫ cokernel.π T'.f = adj.counit.app (cokernel T'.f) := (Ext.mk₀_bijective _ _).injective hl
  let l' : U.obj (cokernel T'.f) ⟶ U.obj T'.X₂ := adj.homEquiv _ _ l
  have hl'' : l' ≫ U.map (cokernel.π T'.f) = 𝟙 _ := by
    refine (adj.homEquiv_naturality_right _ _).symm.trans ?_
    rw [hl']
    exact adj.right_triangle_components _
  have hg : cokernel.π T'.f ≫ m = T'.g := cokernel.π_desc _ _ _
  have := hT.epi_g
  have hls : Presheaf.IsLocallySurjective J T'.g :=
    (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{1} R) T.g).2 inferInstance
  have hls' : Presheaf.IsLocallySurjective J m :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hg
  have hW : J.W (U.map m) := by
    rw [J.W_iff_isLocallyBijective]
    refine ⟨Presheaf.isLocallyInjective_of_injective J _ fun X => ?_,
      (Presheaf.isLocallySurjective_iff_whisker_forget J m).1 hls'⟩
    exact (ModuleCat.mono_iff_injective (m.app X)).1 inferInstance
  have s₂ : Presheaf.IsSheaf J (U.obj T'.X₂) := ((sheafCompose J (forget (ModuleCat.{1} R))).obj T.X₂).property
  have s₃ : Presheaf.IsSheaf J (U.obj T'.X₃) := ((sheafCompose J (forget (ModuleCat.{1} R))).obj T.X₃).property
  obtain ⟨σ, hσ⟩ := (hW _ s₂).surjective l'
  have hid : σ ≫ U.map T'.g = 𝟙 _ := by
    apply (hW _ s₃).injective
    dsimp only at hσ ⊢
    rw [← Category.assoc, hσ, ← hg, Functor.map_comp, ← Category.assoc, hl'', Category.id_comp, Category.comp_id]
  have : Epi (U.map T'.g) := epi_of_epi_fac hid
  exact U.epi_of_epi_map this

abbrev freeSheaf (R : Type 1) [CommRing R] : (Cᵒᵖ ⥤ Type 1) ⥤ Sheaf J (ModuleCat.{1} R) :=
  (Functor.whiskeringRight _ _ _).obj (ModuleCat.free R) ⋙ presheafToSheaf _ _

theorem injective_obj (I : Sheaf J (ModuleCat.{1} R)) [Injective I] : Injective I.obj :=
  (sheafificationAdjunction J (ModuleCat.{1} R)).map_injective I inferInstance

theorem Limp.ext_eq_zero (n : ℕ) {P : Cᵒᵖ ⥤ ModuleCat.{1} R} (hP : PointwiseProjective P)
    {F : Sheaf J (ModuleCat.{1} R)} (h : Limp J F)
    (x : Ext.{1} ((presheafToSheaf J _).obj P) F (n + 1)) : x = 0 := by
  induction n generalizing F with
  | zero =>
    obtain ⟨I, Q, i, q, hz, hS, hI, hx⟩ := exists_shift.{1} (Z := (presheafToSheaf J _).obj P) F 0
    obtain ⟨y, rfl⟩ := hx x
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
    have hepi := Limp.epi J hS h
    have := hS.mono_f
    have hS' : ((ShortComplex.mk i q hz).map (sheafToPresheaf J _)).ShortExact :=
      { exact := hS.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance
        mono_f := inferInstanceAs (Mono ((sheafToPresheaf J _).map (ShortComplex.mk i q hz).f))
        epi_g := hepi }
    let adj := sheafificationAdjunction J (ModuleCat.{1} R)
    obtain ⟨l, hl⟩ := Ext.covariant_sequence_exact₃ _ hS' (Ext.mk₀ (adj.homEquiv P Q g)) rfl (h 0 _ hP _)
    obtain ⟨l, rfl⟩ := (Ext.mk₀_bijective _ _).surjective l
    rw [Ext.mk₀_comp_mk₀] at hl
    have hl' : l ≫ (sheafToPresheaf J _).map q = adj.homEquiv P Q g := (Ext.mk₀_bijective _ _).injective hl
    have hg : g = (adj.homEquiv P I).symm l ≫ q :=
      ((adj.homEquiv_naturality_right_symm (X := P) (Y := I) l q).symm.trans
        ((congrArg (adj.homEquiv P Q).symm hl').trans (Equiv.symm_apply_apply _ _))).symm
    rw [hg, ← Ext.mk₀_comp_mk₀_assoc]
    erw [hS.comp_extClass]
    exact Ext.comp_zero _ _ _ _ _
  | succ n hn =>
    obtain ⟨I, Q, i, q, hz, hS, hI, hx⟩ := exists_shift.{1} (Z := (presheafToSheaf J _).obj P) F (n + 1)
    obtain ⟨y, rfl⟩ := hx x
    have hepi := Limp.epi J hS h
    have := hS.mono_f
    have hS' : ((ShortComplex.mk i q hz).map (sheafToPresheaf J _)).ShortExact :=
      { exact := hS.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance
        mono_f := inferInstanceAs (Mono ((sheafToPresheaf J _).map (ShortComplex.mk i q hz).f))
        epi_g := hepi }
    have hQ : Limp J Q := fun k P' hP' z => by
      obtain ⟨l, hl⟩ := Ext.covariant_sequence_exact₃ _ hS' z rfl (h _ _ hP' _)
      have : Injective ((ShortComplex.mk i q hz).map (sheafToPresheaf J _)).X₂ := injective_obj J I
      rw [← hl, Subsingleton.elim l 0]
      exact Ext.zero_comp _ _ _ _ _
    rw [hn hQ y]
    exact Ext.zero_comp _ _ _ _ _

abbrev res : Sheaf J (ModuleCat.{1} S) ⥤ Sheaf J (ModuleCat.{1} R) := sheafCompose J (ModuleCat.restrictScalars.{1} f)

instance : (res J f).Additive where

instance : PreservesFiniteLimits (res J f) := by
  have := (Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} f)).isRightAdjoint
  infer_instance

instance : PreservesFiniteColimits (res J f) := by
  have := (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} f).isLeftAdjoint
  let j : res J f ≅ Sheaf.composeAndSheafify J (ModuleCat.restrictScalars.{1} f) :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ (sheafificationNatIso J _)
  exact preservesFiniteColimits_of_natIso j.symm

theorem ext_res_eq_zero (I : Sheaf J (ModuleCat.{1} S)) (hI : Injective I) (n : ℕ) {P : Cᵒᵖ ⥤ ModuleCat.{1} R}
    (hP : PointwiseProjective P) (x : Ext.{1} ((presheafToSheaf J _).obj P) ((res J f).obj I) (n + 1)) : x = 0 := by
  have := injective_obj J I
  exact Limp.ext_eq_zero J n hP (fun k P' hP' z => presheaf_ext_eq_zero f I.obj k hP' z) x

def freeEquiv (T : Cᵒᵖ ⥤ Type 1) (F : Sheaf J (ModuleCat.{1} R)) :
    ((freeSheaf J R).obj T ⟶ F) ≃ (T ⟶ F.obj ⋙ forget _) :=
  ((sheafificationAdjunction J _).homEquiv _ F).trans (((ModuleCat.adj R).whiskerRight Cᵒᵖ).homEquiv T F.obj)

theorem freeEquiv_comp (T : Cᵒᵖ ⥤ Type 1) {F G : Sheaf J (ModuleCat.{1} R)} (g : (freeSheaf J R).obj T ⟶ F)
    (u : F ⟶ G) : freeEquiv J T G (g ≫ u) = freeEquiv J T F g ≫ Functor.whiskerRight u.hom (forget _) := rfl

def resEquiv (T : Cᵒᵖ ⥤ Type 1) (G : Sheaf J (ModuleCat.{1} S)) :
    ((freeSheaf J S).obj T ⟶ G) ≃ ((freeSheaf J R).obj T ⟶ (res J f).obj G) :=
  (freeEquiv J T G).trans (freeEquiv J T ((res J f).obj G)).symm

theorem freeEquiv_resEquiv (T : Cᵒᵖ ⥤ Type 1) (G : Sheaf J (ModuleCat.{1} S)) (g : (freeSheaf J S).obj T ⟶ G) :
    freeEquiv J T ((res J f).obj G) (resEquiv J f T G g) = freeEquiv J T G g :=
  (freeEquiv J T ((res J f).obj G)).apply_symm_apply _

def freeUnit (T : Cᵒᵖ ⥤ Type 1) : (freeSheaf J R).obj T ⟶ (res J f).obj ((freeSheaf J S).obj T) :=
  resEquiv J f T _ (𝟙 _)

theorem freeUnit_comp (T : Cᵒᵖ ⥤ Type 1) {G : Sheaf J (ModuleCat.{1} S)} (g : (freeSheaf J S).obj T ⟶ G) :
    freeUnit J f T ≫ (res J f).map g = resEquiv J f T G g := by
  apply (freeEquiv J T _).injective
  rw [freeEquiv_comp, freeUnit, freeEquiv_resEquiv, freeEquiv_resEquiv]
  exact (freeEquiv_comp J T (𝟙 _) g).symm.trans (congrArg _ (Category.id_comp g))

def cmp (T : Cᵒᵖ ⥤ Type 1) (G : Sheaf J (ModuleCat.{1} S)) (n : ℕ) :
    Ext.{1} ((freeSheaf J S).obj T) G n ≃+ Ext.{1} ((freeSheaf J R).obj T) ((res J f).obj G) n :=
  AddEquiv.ofBijective (extMap.{1, 1} (res J f) (freeUnit J f T) G n)
    (extMap_bijective _ _
      (fun F => by
        have h : (fun g : (freeSheaf J S).obj T ⟶ F => freeUnit J f T ≫ (res J f).map g) = resEquiv J f T F :=
          funext (freeUnit_comp J f T)
        rw [h]
        exact (resEquiv J f T F).bijective)
      (fun I hI k x => ext_res_eq_zero J f I hI k (pointwiseProjective_free T) x) n G)

theorem cmp_apply (T : Cᵒᵖ ⥤ Type 1) (G : Sheaf J (ModuleCat.{1} S)) (n : ℕ) (y : Ext.{1} ((freeSheaf J S).obj T) G n) :
    cmp J f T G n y = (Ext.mk₀ (freeUnit J f T)).comp (y.mapExactFunctor (res J f)) (zero_add n) := rfl

variable {F F' : Sheaf J (ModuleCat.{1} R)} {G G' : Sheaf J (ModuleCat.{1} S)}

def change (u : F ⟶ (res J f).obj G) (T : Cᵒᵖ ⥤ Type 1) (n : ℕ) :
    Ext.{1} ((freeSheaf J R).obj T) F n →+ Ext.{1} ((freeSheaf J S).obj T) G n :=
  (cmp J f T G n).symm.toAddMonoidHom.comp ((Ext.mk₀ u).postcomp _ (add_zero n))

theorem cmp_change (u : F ⟶ (res J f).obj G) (T : Cᵒᵖ ⥤ Type 1) (n : ℕ) (x : Ext.{1} ((freeSheaf J R).obj T) F n) :
    cmp J f T G n (change J f u T n x) = x.comp (Ext.mk₀ u) (add_zero n) :=
  (cmp J f T G n).apply_symm_apply _

theorem change_mk₀ (u : F ⟶ (res J f).obj G) (T : Cᵒᵖ ⥤ Type 1) (g : (freeSheaf J R).obj T ⟶ F) :
    change J f u T 0 (Ext.mk₀ g) = Ext.mk₀ ((resEquiv J f T G).symm (g ≫ u)) := by
  apply (cmp J f T G 0).injective
  rw [cmp_change, cmp_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, freeUnit_comp,
    Equiv.apply_symm_apply]

theorem change_postcomp_left (v : F ⟶ F') (u : F' ⟶ (res J f).obj G) (T : Cᵒᵖ ⥤ Type 1) (n : ℕ)
    (x : Ext.{1} ((freeSheaf J R).obj T) F n) :
    change J f u T n (x.comp (Ext.mk₀ v) (add_zero n)) = change J f (v ≫ u) T n x := by
  apply (cmp J f T G n).injective
  rw [cmp_change, cmp_change, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

theorem change_postcomp_right (u : F ⟶ (res J f).obj G) (v : G ⟶ G') (T : Cᵒᵖ ⥤ Type 1) (n : ℕ)
    (x : Ext.{1} ((freeSheaf J R).obj T) F n) :
    (change J f u T n x).comp (Ext.mk₀ v) (add_zero n) = change J f (u ≫ (res J f).map v) T n x := by
  apply (cmp J f T G' n).injective
  rw [cmp_change, cmp_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero, ← cmp_apply, cmp_change, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀]

theorem change_smul (u : F ⟶ (res J f).obj G) (T : Cᵒᵖ ⥤ Type 1) (n : ℕ) (r : R)
    (x : Ext.{1} ((freeSheaf J R).obj T) F n) : change J f u T n (r • x) = f r • change J f u T n x := by
  rw [Ext.smul_eq_comp_mk₀, Ext.smul_eq_comp_mk₀, change_postcomp_left, change_postcomp_right]
  have h : (res J f).map (f r • 𝟙 G) = r • 𝟙 _ := rfl
  rw [h, Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

def resId (f : R →+* R) (hf : f = RingHom.id R) : res J f ⟶ 𝟭 _ where
  app G := ⟨Functor.whiskerLeft G.obj (ModuleCat.restrictScalarsId' f hf).hom⟩
  naturality _ _ _ := rfl

variable {S' : Type 1} [CommRing S']

def resComp (g : S →+* S') (gf : R →+* S') (h : gf = g.comp f) : res J g ⋙ res J f ⟶ res J gf where
  app G := ⟨Functor.whiskerLeft G.obj (ModuleCat.restrictScalarsComp' f g gf h).inv⟩
  naturality _ _ _ := rfl

end Site

end GlobalTheory.ChangeRing

end
