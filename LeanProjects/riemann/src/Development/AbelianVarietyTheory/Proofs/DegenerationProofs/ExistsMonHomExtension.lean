import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.GenericHom

theorem mul_eq_of_generic {A B P : Type*} [Group A] [Group B] (j : P → A) (f : P → B)
    (hm : ∀ x y z, j x * j y = j z → f x * f y = f z)
    (hg : ∀ s : List A, ∃ u, ∀ h ∈ s, ∃ p, j p = h * u) (a x b y : P)
    (h : j a * j x = j b * j y) : f a * f x = f b * f y := by
  obtain ⟨u, hu⟩ := hg [1, j x, j y, j a * j x]
  obtain ⟨c, hc⟩ := hu 1 (by simp)
  obtain ⟨p, hp⟩ := hu (j x) (by simp)
  obtain ⟨q, hq⟩ := hu (j y) (by simp)
  obtain ⟨r, hr⟩ := hu (j a * j x) (by simp)
  rw [_root_.one_mul] at hc
  have e1 := hm x c p (by rw [hc, hp])
  have e2 := hm y c q (by rw [hc, hq])
  have e3 := hm a p r (by rw [hp, hr, _root_.mul_assoc])
  have e4 := hm b q r (by rw [hq, hr, h, _root_.mul_assoc])
  apply mul_right_cancel (b := f c)
  rw [_root_.mul_assoc, _root_.mul_assoc, e1, e2, e3, e4]

theorem mul_four_eq_of_generic {A B P : Type*} [Group A] [Group B] (j : P → A) (f : P → B)
    (hm : ∀ x y z, j x * j y = j z → f x * f y = f z)
    (hg : ∀ s : List A, ∃ u, ∀ h ∈ s, ∃ p, j p = h * u) (a x b y c z : P)
    (h : (j a * j x) * (j b * j y) = j c * j z) : (f a * f x) * (f b * f y) = f c * f z := by
  obtain ⟨u, hu⟩ := hg [1, j y, j b * j y, j x * (j b * j y), j c * j z, j z]
  obtain ⟨p₀, h₀⟩ := hu 1 (by simp)
  obtain ⟨p₁, h₁⟩ := hu (j y) (by simp)
  obtain ⟨p₂, h₂⟩ := hu (j b * j y) (by simp)
  obtain ⟨p₃, h₃⟩ := hu (j x * (j b * j y)) (by simp)
  obtain ⟨p₄, h₄⟩ := hu (j c * j z) (by simp)
  obtain ⟨p₅, h₅⟩ := hu (j z) (by simp)
  rw [_root_.one_mul] at h₀
  have e1 := hm y p₀ p₁ (by rw [h₀, h₁])
  have e2 := hm b p₁ p₂ (by rw [h₁, h₂, _root_.mul_assoc])
  have e3 := hm x p₂ p₃ (by rw [h₂, h₃]; simp only [_root_.mul_assoc])
  have e4 := hm a p₃ p₄ (by rw [h₃, h₄, ← h]; simp only [_root_.mul_assoc])
  have e5 := hm z p₀ p₅ (by rw [h₀, h₅])
  have e6 := hm c p₅ p₄ (by rw [h₅, h₄, _root_.mul_assoc])
  apply mul_right_cancel (b := f p₀)
  simp only [_root_.mul_assoc]
  rw [e1, e2, e3, e4, e5, e6]

variable {k : Type} [Field k] [IsAlgClosed k]

theorem exists_point_mem (X : Over (Sp k)) [LocallyOfFiniteType X.hom] (W : Set X.left)
    (hW : IsLocallyClosed W) (hne : W.Nonempty) :
    ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, ∀ p, x.left p ∈ W := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hne hW
  exact ⟨Over.homMk (pointOfClosedPoint (K := k) X.hom c hc) (pointOfClosedPoint_comp (K := k) X.hom c hc),
    fun p => (congrArg (· ∈ W) (pointOfClosedPoint_apply (K := k) X.hom c hc p)).mpr hcW⟩

theorem hom_ext_points {X Y : Over (Sp k)}
    [Smooth X.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] (f g : X ⟶ Y)
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have := isNormalScheme_of_smooth (S := Spec (.of k)) X.hom
  have : IsReduced X.left := IsNormalScheme.isReduced
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  refine Over.OverMorphism.ext (ext_of_apply_eq (K := k) Y.hom Set.univ
    isOpen_univ.isLocallyClosed dense_univ (fun x _ hx => ?_) (by rw [Over.w, Over.w]))
  obtain ⟨p, hp⟩ := exists_point_mem X {x} hx.isLocallyClosed ⟨x, rfl⟩
  have h1 : p.left ≫ f.left = p.left ≫ g.left := congrArg CommaMorphism.left (h p)
  have h2 : f.left (p.left (IsLocalRing.closedPoint k)) =
      g.left (p.left (IsLocalRing.closedPoint k)) :=
    congrArg (fun φ => φ (IsLocalRing.closedPoint k)) h1
  have h3 : p.left (IsLocalRing.closedPoint k) = x := hp _
  exact (congrArg f.left h3).symm.trans (h2.trans (congrArg g.left h3))

omit [IsAlgClosed k] in

theorem exists_lift {U H Z : Over (Sp k)} (j : U ⟶ H) [IsOpenImmersion j.left] (x : Z ⟶ H)
    (hx : ∀ p, x.left p ∈ Set.range j.left) : ∃ y : Z ⟶ U, y ≫ j = x := by
  have hr : Set.range x.left ⊆ Set.range j.left := by rintro _ ⟨p, rfl⟩; exact hx p
  refine ⟨Over.homMk (IsOpenImmersion.lift j.left x.left hr) ?_, Over.OverMorphism.ext
    (IsOpenImmersion.lift_fac j.left x.left hr)⟩
  rw [← Over.w j, IsOpenImmersion.lift_fac_assoc, Over.w]

theorem exists_generic {U H : Over (Sp k)} [LocallyOfFiniteType H.hom] [IrreducibleSpace H.left]
    (j : U ⟶ H) [IsOpenImmersion j.left] [Nonempty U.left] (s : List (H ≅ H)) :
    ∃ u : 𝟙_ (Over (Sp k)) ⟶ H, ∀ φ ∈ s, ∃ p, p ≫ j = u ≫ φ.hom := by
  have key : ∃ W : Set H.left, IsOpen W ∧ W.Nonempty ∧
      ∀ φ ∈ s, ∀ w ∈ W, φ.hom.left w ∈ Set.range j.left := by
    induction s with
    | nil => exact ⟨Set.univ, isOpen_univ, Set.univ_nonempty, by simp⟩
    | cons φ s ih =>
      obtain ⟨W, h1, h2, h3⟩ := ih
      have ho : IsOpen (φ.hom.left ⁻¹' Set.range j.left) :=
        (IsOpenImmersion.isOpen_range j.left).preimage φ.hom.left.continuous
      have hn : (φ.hom.left ⁻¹' Set.range j.left).Nonempty := by
        obtain ⟨v⟩ := ‹Nonempty U.left›
        refine ⟨φ.inv.left (j.left v), v, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, φ.inv_hom_id]
        rfl
      refine ⟨W ∩ φ.hom.left ⁻¹' Set.range j.left, h1.inter ho,
        nonempty_preirreducible_inter h1 ho h2 hn, ?_⟩
      intro ψ hψ w hw
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact hw.2
      · exact h3 ψ hψ w hw.1
  obtain ⟨W, h1, h2, h3⟩ := key
  obtain ⟨u, hu⟩ := exists_point_mem H W h1.isLocallyClosed h2
  exact ⟨u, fun φ hφ => exists_lift j _ fun p => h3 φ hφ _ (hu p)⟩

omit [IsAlgClosed k] in

theorem point_comp_mul {X G : Over (Sp k)} [GrpObj G] (x : 𝟙_ (Over (Sp k)) ⟶ X)
    (a : 𝟙_ (Over (Sp k)) ⟶ G) (g : X ⟶ G) : x ≫ ((toUnit X ≫ a) * g) = a * (x ≫ g) := by
  rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (𝟙 _), Category.id_comp]

theorem exists_monHom_extension : ∀ (k : Type) [Field k] [IsAlgClosed k] (H G U : Over (Sp k)) [GrpObj H] [GrpObj G], SmConn H → SmConn G → ∀ (j : U ⟶ H) (f : U ⟶ G), IsOpenImmersion j.left → Nonempty U.left → (∀ x y z : (𝟙_ (Over (Sp k)) ⟶ U), (x ≫ j) * (y ≫ j) = z ≫ j → (x ≫ f) * (y ≫ f) = z ≫ f) → ∃ F : H ⟶ G, IsMonHom F ∧ j ≫ F = f := by
  intro k _ _ H G U _ _ ⟨hc, hs, _, _, hgc⟩ ⟨_, _, _, _, _⟩ j f hj hU hm
  have : IsIntegral H.left := isIntegral_of_smooth_of_geometricallyConnected H.hom
  have htr : ∀ (a x : 𝟙_ (Over (Sp k)) ⟶ H), x ≫ (transl a).hom = a * x := fun a x =>
    (point_comp_mul x a (𝟙 H)).trans (by rw [Category.comp_id])
  have hg : ∀ s : List (𝟙_ (Over (Sp k)) ⟶ H), ∃ u, ∀ h ∈ s,
      ∃ p : 𝟙_ (Over (Sp k)) ⟶ U, p ≫ j = h * u := by
    intro s
    obtain ⟨u, hu⟩ := exists_generic j (s.map transl)
    exact ⟨u, fun h hh => htr h u ▸ hu _ (List.mem_map_of_mem hh)⟩
  have hdec : ∀ h : 𝟙_ (Over (Sp k)) ⟶ H, ∃ a x : 𝟙_ (Over (Sp k)) ⟶ U,
      (a ≫ j) * (x ≫ j) = h := by
    intro h
    obtain ⟨u, hu⟩ := exists_generic j [Iso.refl H, asIso (ι[H]) ≪≫ transl h]
    obtain ⟨x, hx⟩ := hu (Iso.refl H) (by simp)
    obtain ⟨a, ha⟩ := hu (asIso (ι[H]) ≪≫ transl h) (by simp)
    refine ⟨a, x, ?_⟩
    rw [ha, hx, Iso.trans_hom, ← Category.assoc, htr, asIso_hom, Iso.refl_hom, Category.comp_id,
      ← Hom.inv_def, inv_mul_cancel_right]
  let J : (𝟙_ (Over (Sp k)) ⟶ U) → (U ⟶ H) := fun a => j ≫ (transl (a ≫ j)).hom
  let φ : (𝟙_ (Over (Sp k)) ⟶ U) → (U ⟶ G) := fun a => (toUnit U ≫ a ≫ f) * f
  have hJ : ∀ a x : 𝟙_ (Over (Sp k)) ⟶ U, x ≫ J a = (a ≫ j) * (x ≫ j) := fun a x => by
    rw [← htr, Category.assoc]
  have hφ : ∀ a x : 𝟙_ (Over (Sp k)) ⟶ U, x ≫ φ a = (a ≫ f) * (x ≫ f) := fun a x =>
    point_comp_mul x _ _
  have hJo : ∀ a, IsOpenImmersion (J a).left := fun a => by
    have : IsIso (transl (a ≫ j)).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (transl (a ≫ j)).hom))
    exact inferInstanceAs (IsOpenImmersion (j.left ≫ (transl (a ≫ j)).hom.left))
  have hcov : ∀ y : H.left, ∃ a, y ∈ Set.range (J a).left := by
    by_contra hn
    push Not at hn
    obtain ⟨y, hy⟩ := hn
    have hcl : IsClosed (⋃ a, Set.range (J a).left)ᶜ :=
      (isOpen_iUnion fun a => IsOpenImmersion.isOpen_range (J a).left).isClosed_compl
    obtain ⟨h, hh⟩ := exists_point_mem H _ hcl.isLocallyClosed ⟨y, by simpa using hy⟩
    obtain ⟨a, x, e⟩ := hdec h
    rw [← hJ] at e
    subst e
    exact hh (IsLocalRing.closedPoint k) (Set.mem_iUnion.2 ⟨a, x.left (IsLocalRing.closedPoint k), rfl⟩)
  have hsU : Smooth U.hom := by rw [← Over.w j]; infer_instance
  let 𝒰 : H.left.OpenCover := Scheme.Cover.mkOfCovers (𝟙_ (Over (Sp k)) ⟶ U) (fun _ => U.left)
    (fun a => (J a).left) (fun y => hcov y) hJo
  have hcomp : ∀ a b, pullback.fst (J a).left (J b).left ≫ (φ a).left =
      pullback.snd (J a).left (J b).left ≫ (φ b).left := by
    intro a b
    let Z : Over (Sp k) := Over.mk (pullback.fst (J a).left (J b).left ≫ U.hom)
    have : Smooth Z.hom := inferInstanceAs (Smooth (pullback.fst (J a).left (J b).left ≫ U.hom))
    let p₁ : Z ⟶ U := Over.homMk (pullback.fst (J a).left (J b).left) rfl
    let p₂ : Z ⟶ U := Over.homMk (pullback.snd (J a).left (J b).left) (by
      show _ = pullback.fst (J a).left (J b).left ≫ U.hom
      have e := congrArg (· ≫ H.hom) (pullback.condition (f := (J a).left) (g := (J b).left))
      simp only [Category.assoc, Over.w] at e
      exact e.symm)
    have hp : p₁ ≫ J a = p₂ ≫ J b := Over.OverMorphism.ext pullback.condition
    have : p₁ ≫ φ a = p₂ ≫ φ b := hom_ext_points _ _ fun z => by
      rw [← Category.assoc, ← Category.assoc, hφ, hφ]
      refine mul_eq_of_generic (· ≫ j) (· ≫ f) hm hg _ _ _ _ ?_
      show (a ≫ j) * ((z ≫ p₁) ≫ j) = (b ≫ j) * ((z ≫ p₂) ≫ j)
      rw [← hJ, ← hJ, Category.assoc, Category.assoc, hp]
    exact congrArg CommaMorphism.left this
  let F₀ : H.left ⟶ G.left := 𝒰.glueMorphisms (fun a => (φ a).left) hcomp
  have hF₀ : ∀ a, (J a).left ≫ F₀ = (φ a).left := fun a =>
    𝒰.ι_glueMorphisms (fun a => (φ a).left) hcomp a
  let F : H ⟶ G := Over.homMk F₀ (𝒰.hom_ext _ _ fun a => by
    show (J a).left ≫ F₀ ≫ G.hom = (J a).left ≫ H.hom
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) (hF₀ a)).trans
      ((Over.w (φ a)).trans (Over.w (J a)).symm)))
  have hF : ∀ a x : 𝟙_ (Over (Sp k)) ⟶ U, ((a ≫ j) * (x ≫ j)) ≫ F = (a ≫ f) * (x ≫ f) := by
    intro a x
    have : J a ≫ F = φ a := Over.OverMorphism.ext (hF₀ a)
    rw [← hJ, Category.assoc, this, hφ]
  have hmul : ∀ h h' : 𝟙_ (Over (Sp k)) ⟶ H, (h * h') ≫ F = (h ≫ F) * (h' ≫ F) := by
    intro h h'
    obtain ⟨c, z, e⟩ := hdec (h * h')
    obtain ⟨a, x, rfl⟩ := hdec h
    obtain ⟨b, y, rfl⟩ := hdec h'
    rw [← e, hF, hF, hF]
    exact (mul_four_eq_of_generic (· ≫ j) (· ≫ f) hm hg _ _ _ _ _ _ e.symm).symm
  refine ⟨F, ⟨?_, ?_⟩, hom_ext_points _ _ fun w => ?_⟩
  · have := hmul 1 1
    rw [_root_.one_mul] at this
    have h1 : (1 : 𝟙_ (Over (Sp k)) ⟶ H) ≫ F = 1 := left_eq_mul.1 this
    simpa [Hom.one_def] using h1
  · have : Smooth (H ⊗ H).hom := inferInstanceAs (Smooth (pullback.fst H.hom H.hom ≫ H.hom))
    refine hom_ext_points _ _ fun z => ?_
    have := hmul (z ≫ fst H H) (z ≫ snd H H)
    rw [Hom.mul_def, Hom.mul_def, lift_comp_fst_snd] at this
    rw [← Category.assoc, this, ← Category.assoc]
    congr 1
    ext <;> simp
  · obtain ⟨a, x, e⟩ := hdec (w ≫ j)
    rw [← Category.assoc, ← e, hF]
    exact hm _ _ _ e

end GlobalTheory.GenericHom
