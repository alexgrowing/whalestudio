import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.CompF
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.AcycOfCoprod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallDescentH1Surjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineH2SmallCoverBijective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

universe v u v' u' v'' u''

section General

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {C'' : Type u''} [Category.{v''} C'']

theorem restrict_pull1 (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C'' ⥤ C') (c : GlobalTheory.CatCoh.H1 F) :
    (CoefMap.restrict (G ⋙ F) H).pull1 ((CoefMap.restrict F G).pull1 c) =
      (CoefMap.restrict F (H ⋙ G)).pull1 c := by
  rw [← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ (𝟙 _) (fun T b => by simp [CoefMap.comp, CoefMap.restrict, mp] <;> rfl) c

theorem restrict_pull2 (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C'' ⥤ C') (c : GlobalTheory.CatCoh.H2 F) :
    (CoefMap.restrict (G ⋙ F) H).pull2 ((CoefMap.restrict F G).pull2 c) =
      (CoefMap.restrict F (H ⋙ G)).pull2 c := by
  rw [← CoefMap.pullCohomologyTwo_comp]
  exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ (𝟙 _) (fun T b => by simp [CoefMap.comp, CoefMap.restrict, mp] <;> rfl) c

end General

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}
  {γ : DividedPowers I} {s : X ⟶ Sp R} {K : Type} {U : K → X.Opens}

def toSmall (γ : DividedPowers I) (s : X ⟶ Sp R) (U : K → X.Opens) :
    Tag γ s U ⥤ (IsSmall γ s U).FullSubcategory where
  obj S := ⟨S.T, S.k, S.le⟩
  map f := ⟨f.f⟩

section Comma

variable {T : (IsSmall γ s U).FullSubcategory}

theorem comma_le (a : CostructuredArrow (toSmall γ s U) T) : ⊤ ≤ T.obj.x ⁻¹ᵁ U a.left.k :=
  Thick.Hom.le_preimage a.hom.hom a.left.le

def selfObj (k : K) (h : ⊤ ≤ T.obj.x ⁻¹ᵁ U k) : CostructuredArrow (toSmall γ s U) T :=
  CostructuredArrow.mk (Y := (⟨T.obj, k, h⟩ : Tag γ s U)) (𝟙 T)

def toSelf (a : CostructuredArrow (toSmall γ s U) T) (k : K) (h : ⊤ ≤ T.obj.x ⁻¹ᵁ U k)
    (e : U a.left.k ≤ U k) : a ⟶ selfObj k h :=
  CostructuredArrow.homMk (⟨a.hom.hom, e⟩ : Tag.Hom _ _) (Category.comp_id _)

theorem toSelf_unique {a : CostructuredArrow (toSmall γ s U) T} {k : K} {h : ⊤ ≤ T.obj.x ⁻¹ᵁ U k}
    (f g : a ⟶ selfObj k h) : f = g := by
  have hf := CostructuredArrow.w f
  have hg := CostructuredArrow.w g
  apply CostructuredArrow.hom_ext
  revert hf hg
  rcases f with ⟨⟨f1, l1⟩, fr, fw⟩
  rcases g with ⟨⟨g1, l2⟩, gr, gw⟩
  intro hf hg
  simp [selfObj, toSmall] at hf hg ⊢
  have e : f1 = g1 := congrArg (fun q => q.hom) (hf.trans hg.symm)
  subst e
  rfl

def selfFun (m : CostructuredArrow (toSmall γ s U) T → K) (h : ∀ a, ⊤ ≤ T.obj.x ⁻¹ᵁ U (m a))
    (mono : ∀ a b, (a ⟶ b) → U (m a) ≤ U (m b)) :
    CostructuredArrow (toSmall γ s U) T ⥤ CostructuredArrow (toSmall γ s U) T where
  obj a := selfObj (m a) (h a)
  map {a b} f := toSelf _ _ _ (mono a b f)
  map_id _ := toSelf_unique _ _
  map_comp _ _ := toSelf_unique _ _

private theorem pull1_restrict_const_eq_of_natTrans {D : Type u} [Category.{v} D] (M : CommAlgCat.{0} R) (Φ Ψ : D ⥤ D)
    (θ : Φ ⟶ Ψ) (c : GlobalTheory.CatCoh.H1 ((Functor.const D).obj M)) :
    (CoefMap.restrict ((Functor.const D).obj M) Φ).pull1 c =
      (CoefMap.restrict ((Functor.const D).obj M) Ψ).pull1 c :=
  CoefMap.pullCohomologyOne_eq_of_natTrans (CoefMap.restrict ((Functor.const D).obj M) Φ)
    (CoefMap.restrict ((Functor.const D).obj M) Ψ :
      CoefMap (RingHom.id R) ((Functor.const D).obj M) (Φ ⋙ (Functor.const D).obj M))
    θ (fun _ _ => rfl) c

private theorem pull2_restrict_const_eq_of_natTrans {D : Type u} [Category.{v} D] (M : CommAlgCat.{0} R) (Φ Ψ : D ⥤ D)
    (θ : Φ ⟶ Ψ) (c : GlobalTheory.CatCoh.H2 ((Functor.const D).obj M)) :
    (CoefMap.restrict ((Functor.const D).obj M) Φ).pull2 c =
      (CoefMap.restrict ((Functor.const D).obj M) Ψ).pull2 c :=
  CoefMap.pullCohomologyTwo_eq_of_natTrans (CoefMap.restrict ((Functor.const D).obj M) Φ)
    (CoefMap.restrict ((Functor.const D).obj M) Ψ :
      CoefMap (RingHom.id R) ((Functor.const D).obj M) (Φ ⋙ (Functor.const D).obj M))
    θ (fun _ _ => rfl) c

private theorem pull1_restrict_id {D : Type u} [Category.{v} D] (F : D ⥤ CommAlgCat.{0} R)
    (c : GlobalTheory.CatCoh.H1 F) : (CoefMap.restrict F (𝟭 D)).pull1 c = c := by
  have e := CoefMap.pullCohomologyOne_eq_of_natTrans (CoefMap.id F) (CoefMap.restrict F (𝟭 D)) (𝟙 _)
    (fun _ b => by simp [CoefMap.restrict, CoefMap.id, mp] <;> rfl) c
  rw [CoefMap.pullCohomologyOne_id] at e
  exact e.symm

private theorem pull2_restrict_id {D : Type u} [Category.{v} D] (F : D ⥤ CommAlgCat.{0} R)
    (c : GlobalTheory.CatCoh.H2 F) : (CoefMap.restrict F (𝟭 D)).pull2 c = c := by
  have e := CoefMap.pullCohomologyTwo_eq_of_natTrans (CoefMap.id F) (CoefMap.restrict F (𝟭 D)) (𝟙 _)
    (fun _ b => by simp [CoefMap.restrict, CoefMap.id, mp] <;> rfl) c
  rw [CoefMap.pullCohomologyTwo_id] at e
  exact e.symm

private theorem H2_discrete_punit_eq_zero (F : Discrete PUnit.{1} ⥤ CommAlgCat.{0} R) (c : GlobalTheory.CatCoh.H2 F) :
    c = 0 := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  rw [H2.mk_eq_zero]
  refine ⟨fun a b φ => z.1 a b b φ (𝟙 b), ?_⟩
  funext a b d φ ψ
  rcases a with ⟨⟨⟩⟩
  rcases b with ⟨⟨⟩⟩
  rcases d with ⟨⟨⟩⟩
  obtain rfl : φ = 𝟙 _ := Subsingleton.elim _ _
  obtain rfl : ψ = 𝟙 _ := Subsingleton.elim _ _
  simp [d1_apply, mp]

private theorem pull1_restrict_const_const_eq_zero {D : Type u} [Category.{v} D] (M : CommAlgCat.{0} R) (x : D)
    (c : GlobalTheory.CatCoh.H1 ((Functor.const D).obj M)) :
    (CoefMap.restrict ((Functor.const D).obj M) ((Functor.const D).obj x)).pull1 c = 0 := by
  have e := restrict_pull1 ((Functor.const D).obj M) ((Functor.const (Discrete PUnit.{1})).obj x)
    ((Functor.const D).obj ⟨⟨⟩⟩) c
  rw [H1.eq_zero_of_isInitial _ (T₀ := (⟨⟨⟩⟩ : Discrete PUnit.{1}))
    (Limits.IsInitial.ofUniqueHom (fun _ => Discrete.eqToHom (Subsingleton.elim _ _))
      (fun _ _ => Subsingleton.elim _ _))
    ((CoefMap.restrict ((Functor.const D).obj M) ((Functor.const (Discrete PUnit.{1})).obj x)).pull1 c),
    map_zero] at e
  exact e.symm

private theorem pull2_restrict_const_const_eq_zero {D : Type u} [Category.{v} D] (M : CommAlgCat.{0} R) (x : D)
    (c : GlobalTheory.CatCoh.H2 ((Functor.const D).obj M)) :
    (CoefMap.restrict ((Functor.const D).obj M) ((Functor.const D).obj x)).pull2 c = 0 := by
  have e := restrict_pull2 ((Functor.const D).obj M) ((Functor.const (Discrete PUnit.{1})).obj x)
    ((Functor.const D).obj ⟨⟨⟩⟩) c
  rw [H2_discrete_punit_eq_zero _
    ((CoefMap.restrict ((Functor.const D).obj M) ((Functor.const (Discrete PUnit.{1})).obj x)).pull2 c),
    map_zero] at e
  exact e.symm

theorem acyc_toSmall (hinf : ∀ k l, ∃ m, U m = U k ⊓ U l) (T : (IsSmall γ s U).FullSubcategory) :
    Acyc R (CostructuredArrow (toSmall γ s U) T) := by
  obtain ⟨k0, h0⟩ := T.property
  choose m2 hm2 using fun (a : CostructuredArrow (toSmall γ s U) T) => hinf a.left.k k0
  have h2 : ∀ a, ⊤ ≤ T.obj.x ⁻¹ᵁ U (m2 a) := by
    intro a
    rw [hm2 a]
    intro p hp
    exact ⟨comma_le a hp, h0 hp⟩
  let S1 := selfFun (T := T) (fun a => a.left.k) comma_le (fun a b f => Tag.Hom.le f.left)
  let S2 := selfFun (T := T) m2 h2 (fun a b f => by
    rw [hm2 a, hm2 b]
    exact inf_le_inf_right _ (Tag.Hom.le f.left))
  let θ1 : 𝟭 _ ⟶ S1 :=
    { app := fun a => toSelf a _ (comma_le a) le_rfl
      naturality := fun _ _ _ => toSelf_unique _ _ }
  let θ2 : S2 ⟶ S1 :=
    { app := fun a => toSelf (selfObj (m2 a) (h2 a)) a.left.k (comma_le a)
        (show U (m2 a) ≤ U a.left.k by rw [hm2 a]; exact inf_le_left)
      naturality := fun _ _ _ => toSelf_unique _ _ }
  let θ3 : S2 ⟶ (Functor.const _).obj (selfObj k0 h0) :=
    { app := fun a => toSelf (selfObj (m2 a) (h2 a)) k0 h0
        (show U (m2 a) ≤ U k0 by rw [hm2 a]; exact inf_le_right)
      naturality := fun _ _ _ => toSelf_unique (k := k0) (h := h0) _ _ }
  refine ⟨⟨selfObj k0 h0⟩, fun M => ⟨?_, ?_, ?_⟩⟩
  · intro g hg
    have key : ∀ a, g a = g (selfObj k0 h0) := fun a =>
      (hg _ _ (θ1.app a)).symm.trans ((hg _ _ (θ2.app a)).trans (hg _ _ (θ3.app a)).symm)
    intro a b
    exact (key a).trans (key b).symm
  · intro c
    exact (pull1_restrict_id _ c).symm.trans ((pull1_restrict_const_eq_of_natTrans M _ _ θ1 c).trans
      ((pull1_restrict_const_eq_of_natTrans M _ _ θ2 c).symm.trans ((pull1_restrict_const_eq_of_natTrans M _ _ θ3 c).trans
        (pull1_restrict_const_const_eq_zero M _ c))))
  · intro c
    exact (pull2_restrict_id _ c).symm.trans ((pull2_restrict_const_eq_of_natTrans M _ _ θ1 c).trans
      ((pull2_restrict_const_eq_of_natTrans M _ _ θ2 c).symm.trans ((pull2_restrict_const_eq_of_natTrans M _ _ θ3 c).trans
        (pull2_restrict_const_const_eq_zero M _ c))))

end Comma

theorem tag_pull1 (hcov : ⨆ k, U k = ⊤) (hinf : ∀ k l, ∃ m, U m = U k ⊓ U l) :
    Function.Bijective (CoefMap.restrict (O γ s) (Tag.forget γ s U)).pull1 := by
  have key : ⇑(CoefMap.restrict (O γ s) (Tag.forget γ s U)).pull1 =
      ⇑(CoefMap.restrict ((IsSmall γ s U).ι ⋙ O γ s) (toSmall γ s U)).pull1 ∘
        ⇑(CoefMap.restrict (O γ s) (IsSmall γ s U).ι).pull1 :=
    funext fun c => (restrict_pull1 (O γ s) (IsSmall γ s U).ι (toSmall γ s U) c).symm
  rw [key]
  exact (qa1 _ _ (fun T => acyc_toSmall hinf T)).comp
    (SmallDescent.pull1_bijective R I γ X s K U hcov)

private theorem pull2_restrict_isSmall_bijective_of_cover (hcov : ⨆ k, U k = ⊤) :
    Function.Bijective (CoefMap.restrict (O γ s) (IsSmall γ s U).ι).pull2 := by
  apply Desc.pull2_bijective
  · intro T b
    obtain ⟨L, l, hl⟩ := SmallDescent.exists_isLoc T b
    obtain ⟨hu, hsurj, hker, hfac⟩ := hl
    refine ⟨L, l, hu, ?_, hker, ?_⟩
    · intro y
      obtain ⟨n, N, h⟩ := hsurj y
      exact ⟨N, n, h⟩
    · intro S u hu'
      obtain ⟨ψ, hψ⟩ := hfac S u hu'
      exact ⟨ψ, hψ, fun ψ' h' =>
        SmallDescent.IsLoc.hom_ext ⟨hu, hsurj, hker, hfac⟩ (h'.trans hψ.symm)⟩
  · intro S S' a hS
    exact SmallDescent.isSmall_of_hom a hS
  · intro T
    obtain ⟨σ, hσ, hσs⟩ := SmallDescent.exists_cover hcov T
    refine ⟨σ.card, fun i => (σ.equivFin.symm i : T.B), ?_, ?_⟩
    · have hr : Set.range (fun i => (σ.equivFin.symm i : T.B)) = (σ : Set T.B) := by
        ext x
        constructor
        · rintro ⟨i, rfl⟩
          exact (σ.equivFin.symm i).2
        · intro hx
          exact ⟨σ.equivFin ⟨x, hx⟩, by simp⟩
      rw [hr]
      exact hσ
    · intro i S u hu
      exact hσs _ (σ.equivFin.symm i).2 S u hu

theorem tag_pull2 (hcov : ⨆ k, U k = ⊤) (hinf : ∀ k l, ∃ m, U m = U k ⊓ U l) :
    Function.Bijective (CoefMap.restrict (O γ s) (Tag.forget γ s U)).pull2 := by
  have key : ⇑(CoefMap.restrict (O γ s) (Tag.forget γ s U)).pull2 =
      ⇑(CoefMap.restrict ((IsSmall γ s U).ι ⋙ O γ s) (toSmall γ s U)).pull2 ∘
        ⇑(CoefMap.restrict (O γ s) (IsSmall γ s U).ι).pull2 :=
    funext fun c => (restrict_pull2 (O γ s) (IsSmall γ s U).ι (toSmall γ s U) c).symm
  rw [key]
  exact (qa2 _ _ (fun T => acyc_toSmall hinf T)).comp (pull2_restrict_isSmall_bijective_of_cover hcov)

end FubiniStudyChowHeightFormula₂.Adr
