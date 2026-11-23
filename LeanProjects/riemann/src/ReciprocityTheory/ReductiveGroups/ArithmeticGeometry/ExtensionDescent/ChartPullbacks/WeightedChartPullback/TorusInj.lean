import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory
open scoped AlgebraMonoidAlgebra

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Semi.TorusInj

variable {S : Scheme.{0}} (X : Type) [AddCommGroup X] (Y : Over S)

def chiP (χ : X) : Γ((splitTorus S X ⊗ Y).left, ⊤) :=
  (fst (splitTorus S X) Y).left.appTop.hom (charUnit S X χ).val

def tFst : (splitTorus S X).left ⟶ Spec (torusRing ZU X) :=
  pullback.fst (splitTorusAff ZU X).hom (toZ S)

section Point

variable {X Y} {V : Y.left.Opens} (hV : IsAffineOpen V)

abbrev zuAlg (A : Type) [CommRing A] : Algebra ZU.{0} A := ULift.algebra' ℤ A

attribute [local instance] zuAlg

abbrev GA : CommRingCat.{0} := CommRingCat.of (AddMonoidAlgebra Γ(Y.left, V) X)

def ptY : Spec (GA (X := X) (V := V)) ⟶ Y.left :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(Y.left, V) (AddMonoidAlgebra Γ(Y.left, V) X))) ≫ hV.fromSpec

def ptZ : Spec (GA (X := X) (V := V)) ⟶ Spec (torusRing ZU X) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (AddMonoidAlgebra ZU.{0} X) (AddMonoidAlgebra Γ(Y.left, V) X)))

def ptT : Spec (GA (X := X) (V := V)) ⟶ (splitTorus S X).left :=
  pullback.lift (ptZ (X := X) (V := V)) (ptY hV ≫ Y.hom) (specULiftZIsTerminal.hom_ext _ _)

def pt : Spec (GA (X := X) (V := V)) ⟶ (splitTorus S X ⊗ Y).left :=
  pullback.lift (ptT hV) (ptY hV) (pullback.lift_snd _ _ _)

lemma pt_snd : pt hV ≫ (snd (splitTorus S X) Y).left = ptY hV := by
  first
  | exact pullback.lift_snd _ _ _
  | simp [pt]

lemma pt_fst : pt hV ≫ (fst (splitTorus S X) Y).left = ptT hV := by
  first
  | exact pullback.lift_fst _ _ _
  | simp [pt]

lemma ptY_preimage : ptY (X := X) hV ⁻¹ᵁ V = ⊤ := by
  apply eq_top_iff.mpr
  intro p _
  show hV.fromSpec.base ((Spec.map _).base p) ∈ V
  rw [← SetLike.mem_coe, ← hV.range_fromSpec]
  exact Set.mem_range_self _

lemma pt_le : (⊤ : (Spec (GA (X := X) (V := V))).Opens) ≤
    pt hV ⁻¹ᵁ ((snd (splitTorus S X) Y).left ⁻¹ᵁ V) := by
  intro p _
  have h1 : (pt hV ≫ (snd (splitTorus S X) Y).left).base p ∈ V := by
    rw [pt_snd]
    exact (ptY_preimage hV).ge (show p ∈ (⊤ : (Spec (GA (X := X) (V := V))).Opens) from trivial)
  exact h1

def ev : Γ((splitTorus S X ⊗ Y).left, (snd (splitTorus S X) Y).left ⁻¹ᵁ V) →+*
    AddMonoidAlgebra Γ(Y.left, V) X :=
  (Scheme.ΓSpecIso (GA (X := X) (V := V))).hom.hom.comp
    ((pt hV).appLE _ ⊤ (pt_le hV)).hom

lemma tle {A B : Scheme.{0}} (f : A ⟶ B) : (⊤ : A.Opens) ≤ f ⁻¹ᵁ ⊤ := by
  intro p _
  trivial

lemma appLE_of_eq {A B : Scheme.{0}} {f g : A ⟶ B} (hfg : f = g) {U : B.Opens} {W : A.Opens}
    (e : W ≤ f ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W (hfg ▸ e) := by
  subst hfg
  rfl

lemma specMap_appLE_top {R R' : CommRingCat.{0}} (f : R ⟶ R') (e) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso R').hom = f := by
  have h1 : (Spec.map f).appLE ⊤ ⊤ e = (Spec.map f).appTop := by
    first
    | (rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl)
    | (simp only [Scheme.Hom.appLE]
       erw [show (homOfLE e).op = 𝟙 (Opposite.op (⊤ : (Spec R').Opens)) from Subsingleton.elim _ _,
         CategoryTheory.Functor.map_id, Category.comp_id]
       rfl)
  rw [h1, Scheme.ΓSpecIso_naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

lemma specMap_fromSpec_appLE {R : CommRingCat.{0}} (f : Γ(Y.left, V) ⟶ R) (e) :
    (Spec.map f ≫ hV.fromSpec).appLE V ⊤ e ≫ (Scheme.ΓSpecIso R).hom = f := by
  have h1 : (Spec.map f ≫ hV.fromSpec).appLE V ⊤ e =
      hV.fromSpec.appLE V ⊤ (by simp) ≫ (Spec.map f).appLE ⊤ ⊤ (by simp) :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h2 : hV.fromSpec.appLE V ⊤ (by simp) = (Scheme.ΓSpecIso Γ(Y.left, V)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    conv_rhs => rw [← Category.comp_id (Scheme.ΓSpecIso Γ(Y.left, V)).inv]
    congr 1
  rw [h1, h2, Category.assoc]
  exact specMap_appLE_top f _

lemma ev_snd (h : Γ(Y.left, V)) :
    ev hV (((snd (splitTorus S X) Y).left.app V).hom h) = AddMonoidAlgebra.single 0 h := by
  have e1 : (snd (splitTorus S X) Y).left.app V ≫ (pt hV).appLE _ ⊤ (pt_le hV) ≫
      (Scheme.ΓSpecIso (GA (X := X) (V := V))).hom =
      CommRingCat.ofHom (algebraMap Γ(Y.left, V) (AddMonoidAlgebra Γ(Y.left, V) X)) := by
    rw [Scheme.Hom.app_eq_appLE, ← Category.assoc, Scheme.Hom.appLE_comp_appLE,
      appLE_of_eq (pt_snd hV)]
    exact specMap_fromSpec_appLE hV _ _
  have := congrArg (fun φ => φ.hom h) e1
  rw [ev, RingHom.comp_apply]; simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this; convert this using 1
  simp [AddMonoidAlgebra.coe_algebraMap]

lemma charUnit_val (χ : X) :
    (charUnit S X χ).val = ((tFst (S := S) X).appLE ⊤ ⊤
      (tle _)).hom
      ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1)) := by
  simp [charUnit, res, pullU, Scheme.Hom.appLE, AddMonoidAlgebra.of_apply]
  rfl

lemma ev_chi (χ : X) :
    ev hV (((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op).hom (chiP X Y χ)) =
      AddMonoidAlgebra.single χ 1 := by
  have hfst : (pt hV ≫ (fst (splitTorus S X) Y).left) ≫ tFst (S := S) X =
      ptZ (X := X) (V := V) := by
    rw [pt_fst]; exact pullback.lift_fst _ _ _
  have key : (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫
      ((tFst (S := S) X).appLE ⊤ ⊤ (tle _) ≫
      ((fst (splitTorus S X) Y).left.appTop ≫
      ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op ≫
      ((pt hV).appLE _ ⊤ (pt_le hV) ≫ (Scheme.ΓSpecIso (GA (X := X) (V := V))).hom)))) =
      CommRingCat.ofHom (algebraMap (AddMonoidAlgebra ZU.{0} X) (AddMonoidAlgebra Γ(Y.left, V) X)) := by
    have hT : (fst (splitTorus S X) Y).left.appTop = (fst (splitTorus S X) Y).left.appLE ⊤ ⊤ (tle _) := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    rw [hT, ← Category.assoc ((splitTorus S X ⊗ Y).left.presheaf.map _), Scheme.Hom.map_appLE,
      ← Category.assoc ((fst (splitTorus S X) Y).left.appLE _ _ _), Scheme.Hom.appLE_comp_appLE,
      ← Category.assoc ((tFst (S := S) X).appLE ⊤ ⊤ _),
      Scheme.Hom.appLE_comp_appLE, appLE_of_eq hfst]
    exact specMap_appLE_top _ _
  have := congrArg (fun φ => φ.hom (AddMonoidAlgebra.single χ (1 : ULift.{0} ℤ))) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [ev, RingHom.comp_apply, chiP, charUnit_val]
  convert this using 1
  simp [AddMonoidAlgebra.algebraMap_def]

end Point

lemma coeff_sum_single {A : Type} [CommRing A] (s : Finset X) (g : X → A) (χ₀ : X) (h : χ₀ ∈ s) :
    (∑ c ∈ s, AddMonoidAlgebra.single c (g c)).coeff χ₀ = g χ₀ := by
  classical
  first
  | simp [AddMonoidAlgebra.coeff, Finsupp.finset_sum_apply, Finsupp.single_apply, h]
  | simp [Finsupp.finset_sum_apply, Finsupp.single_apply, h]
  | simp [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, h]

theorem eq_zero_of_sum {V : Y.left.Opens} (s : Finset X) (h : X → Γ(Y.left, V))
    (hs : ∑ χ ∈ s, ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op).hom (chiP X Y χ) *
      ((snd (splitTorus S X) Y).left.app V).hom (h χ) = 0) :
    ∀ χ ∈ s, h χ = 0 := by
  intro χ₀ hχ₀
  refine TopCat.Presheaf.section_ext Y.left.sheaf V (h χ₀) 0 fun x hx => ?_
  obtain ⟨W, hW, hxW, hWV⟩ : ∃ W : Y.left.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ V := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := (Y.left.isBasis_affineOpens).exists_subset_of_mem_open hx V.2
    exact ⟨W, hW, hxW, hWV⟩
  have hle : (snd (splitTorus S X) Y).left ⁻¹ᵁ W ≤ (snd (splitTorus S X) Y).left ⁻¹ᵁ V :=
    fun y hy => hWV hy
  have e1 : ∀ χ : X, ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE hle).op).hom
      (((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op).hom (chiP X Y χ)) =
      ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op).hom (chiP X Y χ) := by
    intro c; rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  have e2 : ∀ c : Γ(Y.left, V), ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE hle).op).hom
      (((snd (splitTorus S X) Y).left.app V).hom c) =
      ((snd (splitTorus S X) Y).left.app W).hom ((Y.left.presheaf.map (homOfLE hWV).op).hom c) := by
    intro c
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have hres := congrArg ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE hle).op).hom hs
  simp only [map_sum, map_mul, map_zero, e1, e2] at hres
  have hev := congrArg (ev hW) hres
  simp only [map_sum, map_mul, map_zero, ev_chi, ev_snd, AddMonoidAlgebra.single_mul_single,
    add_zero, one_mul] at hev
  have hc := congrArg (fun f => f.coeff χ₀) hev
  rw [coeff_sum_single X s _ χ₀ hχ₀, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hc
  have hg := TopCat.Presheaf.germ_res_apply Y.left.presheaf (homOfLE hWV) x hxW (h χ₀)
  rw [hc, map_zero] at hg
  exact hg.symm.trans (map_zero _).symm

end ReciprocityTheory.ChartRestriction.G.Semi.TorusInj
