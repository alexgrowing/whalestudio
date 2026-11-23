import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusStableGoodOpenOfWeightUnits
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

open GlobalTheory.SS.TorusSlice

private theorem goodOpen_of_unit_point {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Module.Finite ℤ X]
    {G Y Z₀ : Over S} [GrpObj G]
    (i : splitTorus S X ⟶ G) [IsMonHom i] (j : Y ⟶ G) [IsOpenImmersion j.left] [QuasiCompact j.left] [IsAffine Y.left]
    (σ : Y ⟶ splitTorus S X) (hσ : Equivar i j σ) (y : Z₀ ⟶ Y) (hy : y ≫ σ = 1) :
    ∃ V, GoodOpen i V ∧ ∀ s, (y ≫ j).left s ∈ V := by
  let T := splitTorus S X
  let Y₁ := pullback σ η[T]
  let e : Y₁ ⟶ Y := pullback.fst _ _
  have he : IsPullback e (toUnit Y₁) σ η[T] := by
    rw [toUnit_unique (toUnit Y₁) (pullback.snd σ η[T])]
    exact IsPullback.of_hasPullback _ _
  have he1 : e ≫ σ = 1 := he.w
  have hη : IsClosedImmersion (η[T]).left := by
    have : IsClosedImmersion ((η[T]).left ≫ T.hom) := by
      rw [Over.w]
      exact inferInstanceAs (IsClosedImmersion (𝟙 S))
    exact IsClosedImmersion.of_comp (η[T]).left T.hom
  have : IsAffineHom e.left := MorphismProperty.of_isPullback (P := @IsAffineHom) (he.map (Over.forget S)).flip
    (inferInstanceAs (IsAffineHom (η[T]).left))
  have : IsAffine Y₁.left := isAffine_of_isAffineHom e.left
  have : IsAffineHom (snd T Y₁).left := inferInstanceAs (IsAffineHom (pullback.snd T.hom Y₁.hom))
  have : IsAffine (T ⊗ Y₁).left := isAffine_of_isAffineHom (snd T Y₁).left
  have := isOpenImmersion_sweep i j σ hσ e he
  refine ⟨_, goodOpen_of_equivar i ((fst T Y₁ ≫ i) * (snd T Y₁ ≫ e ≫ j)) (fst T Y₁) (fun Z t p p' h => ?_)
    (fun Z t p => ⟨lift (t * (p ≫ fst _ _)) (p ≫ snd _ _), ?_⟩), fun s => ?_⟩
  · have h1 : (p' ≫ snd T Y₁ ≫ e) ≫ j =
        (((p' ≫ fst T Y₁)⁻¹ * (t * (p ≫ fst T Y₁))) ≫ i) * ((p ≫ snd T Y₁ ≫ e) ≫ j) := by
      simp only [MonObj.comp_mul] at h
      rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, _root_.mul_assoc, eq_inv_mul_iff_mul_eq, _root_.mul_assoc]
      simpa using h
    have h2 := hσ _ _ _ _ h1
    simp only [Category.assoc, he1, MonObj.comp_one, _root_.mul_one] at h2
    exact (eq_inv_mul_iff_mul_eq.1 h2 ▸ (_root_.mul_one _).symm)
  · simp [MonObj.comp_mul, MonObj.mul_comp, _root_.mul_assoc]
  · obtain ⟨y₁, hy₁, -⟩ := he.exists_lift y (toUnit _) hy
    have : y ≫ j = lift 1 y₁ ≫ ((fst T Y₁ ≫ i) * (snd T Y₁ ≫ e ≫ j)) := by
      simp [MonObj.comp_mul, reassoc_of% hy₁]
    rw [this, Scheme.Hom.image_top_eq_opensRange, Over.comp_left, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

private theorem exists_section {S B : Scheme.{0}} {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    (p : B ⟶ S) (r : S ⟶ B) (h : p ≫ r = 𝟙 _) (t : Over.mk p ⟶ splitTorus S X) :
    ∃ c : 𝟙_ (Over S) ⟶ splitTorus S X, toUnit _ ≫ c = t := by
  let b := Module.Free.chooseBasis ℤ X
  obtain ⟨c, hc⟩ := exists_of_basis (Z := 𝟙_ (Over S)) b fun n =>
    Units.map r.appTop.hom.toMonoidHom (splitTorusPointsEquiv S X _ t (Multiplicative.ofAdd (b n)))
  refine ⟨c, ext_basis b fun n => ?_⟩
  have e : (toUnit (Over.mk p)).left = p := (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk p)))
  have e2 := congrArg (fun φ : B ⟶ B => φ.appTop.hom (ch t (b n))) h
  rw [ch_comp, hc, e]
  rw [ch_eq] at e2 ⊢
  simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at e2
  exact e2

theorem UpperTheory.weight_units_section_at_point :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C →
        ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus C X ⟶ G), IsMonHom u →
        (∀ (χ : X) (s : C), ∃ (U : G.left.Opens) (f : Γ(G.left, U)), (∃ y ∈ U, G.hom y = s) ∧ IsUnit f ∧ Wt u U f χ) →
        ∀ p : Sp k ⟶ C, p ≫ strHom k C = 𝟙 _ → ∃ (V : G.left.Opens) (w : Over.mk p ⟶ G), GoodOpen u V ∧ ⊤ ≤ w.left ⁻¹ᵁ V := by
  intro k _ _ C _ hC G _ hG X _ _ _ i hi H p hp
  have := hG.smooth
  have := hG.geomConnected
  have : Smooth (strHom k C) := have := hC.1; SmoothOfRelativeDimension.smooth 1 _
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian (G.hom ≫ strHom k C)
  let b := Module.Free.chooseBasis ℤ X
  let pt : Sp k := IsLocalRing.closedPoint k
  choose U u hne hu hw using fun χ => H χ (p pt)
  let F : Over (Sp k) := Over.mk (pullback.snd G.hom p)
  let φ : F.left ⟶ G.left := pullback.fst G.hom p
  have : IsIntegral F.left := GlobalTheory.isIntegral_pullback_of_smooth G.hom p
  have : LocallyOfFiniteType F.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom p))
  let O : G.left.Opens := ⟨⋂ n, (U (b n) : G.left.Opens),
    isOpen_iInter_of_finite fun n => TopologicalSpace.Opens.isOpen _⟩
  have hd : Dense (⋂ n, ((φ ⁻¹ᵁ U (b n) : F.left.Opens) : Set F.left)) := by
    have aux : ∀ (s : Finset (Module.Free.ChooseBasisIndex ℤ X)) (f : _ → Set F.left), (∀ n, IsOpen (f n)) →
        (∀ n, Dense (f n)) → Dense (⋂ n ∈ s, f n) := fun s f h1 h2 => by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s _ ih =>
        rw [Finset.set_biInter_insert]
        exact (h2 a).inter_of_isOpen_left ih (h1 a)
    suffices h : ∀ n, Dense ((φ ⁻¹ᵁ U (b n) : F.left.Opens) : Set F.left) by
      simpa using aux Finset.univ _ (fun n => TopologicalSpace.Opens.isOpen _) h
    intro n
    obtain ⟨y, hy, e⟩ := hne (b n)
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := p) y pt e
    exact (TopologicalSpace.Opens.isOpen _).dense ⟨z, show φ z ∈ U (b n) from hz ▸ hy⟩
  obtain ⟨q, hq⟩ := exists_point F hd.nonempty
    (isOpen_iInter_of_finite fun n => TopologicalSpace.Opens.isOpen _).isLocallyClosed
  let w : Over.mk p ⟶ G := Over.homMk (q.left ≫ φ) (by
    have := Over.w q
    change (q.left ≫ pullback.fst G.hom p) ≫ G.hom = p
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (· ≫ p) this).trans (Category.id_comp _))
  have hO : w.left pt ∈ O := Set.mem_iInter.2 fun n => by
    change (q.left ≫ φ) pt ∈ U (b n)
    rw [Scheme.Hom.comp_apply]
    exact Set.mem_iInter.1 (hq pt) n
  obtain ⟨Y₀, hY₀, hpY, hYO⟩ := exists_isAffineOpen_mem_and_subset hO
  let Y : Over C := Over.mk (Y₀.ι ≫ G.hom)
  let j : Y ⟶ G := Over.homMk Y₀.ι rfl
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion Y₀.ι)
  have : QuasiCompact j.left := inferInstance
  have : IsAffine Y.left := hY₀
  have hr : Set.range w.left ⊆ Set.range Y₀.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim (α := PrimeSpectrum k) s pt]
    exact hpY
  let y₀ : Over.mk p ⟶ Y := Over.homMk (IsOpenImmersion.lift Y₀.ι w.left hr)
    ((IsOpenImmersion.lift_fac_assoc _ _ hr _).trans (Over.w w))
  have hy₀ : y₀ ≫ j = w := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ hr)
  have hle : ∀ n, ⊤ ≤ j.left ⁻¹ᵁ U (b n) := fun n z _ => Set.mem_iInter.1 (hYO z.2) n
  obtain ⟨σ₀, hσ⟩ := exists_of_basis (Z := Y) b fun n =>
    ((hu (b n)).map (j.left.appLE (U (b n)) ⊤ (hle n)).hom).unit
  have hE : Equivar i j σ₀ := fun Z t a a' h => ext_basis b fun n => by
    have pre : ∀ c : Z ⟶ Y, ⊤ ≤ (c ≫ j).left ⁻¹ᵁ U (b n) := fun c z _ => by
      change (c ≫ j).left z ∈ U (b n)
      rw [Over.comp_left, Scheme.Hom.comp_apply]
      exact hle n (Set.mem_univ _)
    have := hw (b n) Z t (a ≫ j) (h ▸ pre a') (pre a)
    rw [appLE_comp_top a' _ _ h.symm _ _ (hle n), appLE_comp_top a _ _ rfl _ _ (hle n)] at this
    rw [ch_mul, ch_comp, ch_comp, hσ, IsUnit.unit_spec]
    exact this
  obtain ⟨c, hc⟩ := exists_section p (strHom k C) hp (y₀ ≫ σ₀)⁻¹
  let σ : Y ⟶ splitTorus C X := σ₀ * (toUnit Y ≫ c)
  have hσ' : Equivar i j σ := fun Z t a a' h => by
    simp only [σ, MonObj.comp_mul, hE Z t a a' h, _root_.mul_assoc]
    rw [← Category.assoc, ← Category.assoc a, toUnit_unique (a' ≫ toUnit Y) (a ≫ toUnit Y)]
  have hy : y₀ ≫ σ = 1 := by
    simp only [σ, MonObj.comp_mul]
    rw [← Category.assoc, toUnit_unique (y₀ ≫ toUnit Y) (toUnit _), hc, mul_inv_cancel]
  obtain ⟨V, hV, hpV⟩ := goodOpen_of_unit_point i j σ hσ' y₀ hy
  rw [hy₀] at hpV
  exact ⟨V, w, hV, fun s _ => hpV s⟩
