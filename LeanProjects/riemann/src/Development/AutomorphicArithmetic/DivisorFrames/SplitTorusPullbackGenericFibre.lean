import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIntegralTensorLeftOfSmoothGrpObj
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

private theorem spread_unit {Y Y' : Scheme.{0}} (φ : Y' ⟶ Y) [SurjectiveOnStalks φ] (U' : Y'.Opens) (f' : Γ(Y', U'))
    (hf' : IsUnit f') (y : Y') (hy : y ∈ U') :
    ∃ (U : Y.Opens) (f : Γ(Y, U)) (V : Y'.Opens), y ∈ V ∧ IsUnit f ∧ V ≤ U' ∧ V ≤ φ ⁻¹ᵁ U ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (_ : ⊤ ≤ r ⁻¹ᵁ V) (h₁ : ⊤ ≤ (r ≫ φ) ⁻¹ᵁ U) (h₂ : ⊤ ≤ r ⁻¹ᵁ U'),
        ((r ≫ φ).appLE U ⊤ h₁).hom f = (r.appLE U' ⊤ h₂).hom f' := by
  obtain ⟨a, ha⟩ := φ.stalkMap_surjective y (Y'.presheaf.germ U' y hy f')
  have hau : IsUnit a := by
    have : IsUnit (φ.stalkMap y a) := ha ▸ hf'.map _
    exact (isUnit_map_iff (φ.stalkMap y).hom a).1 this
  obtain ⟨U₀, hU₀, f₀, rfl⟩ := Y.presheaf.germ_exist a
  have hb : φ y ∈ Y.basicOpen f₀ := (Y.mem_basicOpen f₀ _ hU₀).2 hau
  let f : Γ(Y, Y.basicOpen f₀) := Y.presheaf.map (homOfLE (Y.basicOpen_le f₀)).op f₀
  have hf : IsUnit f := RingedSpace.isUnit_res_basicOpen Y.toRingedSpace f₀
  have e : Y'.presheaf.germ (φ ⁻¹ᵁ Y.basicOpen f₀) y hb (φ.app _ f) = Y'.presheaf.germ U' y hy f' := by
    rw [← φ.germ_stalkMap_apply _ y hb, ← ha]
    congr 1
    exact Y.presheaf.germ_res_apply _ _ _ _
  obtain ⟨V, hV, i₁, i₂, hi⟩ := Y'.presheaf.germ_eq y _ _ _ _ e
  refine ⟨_, f, V, hV, hf, i₂.le, i₁.le, fun Z r h h₁ h₂ => ?_⟩
  have a₁ := congrArg (fun q => q.hom (φ.app _ f)) (r.map_appLE h i₁.op)
  have a₂ := congrArg (fun q => q.hom f') (r.map_appLE h i₂.op)
  have a₃ := congrArg (fun q => q.hom f) (Scheme.Hom.comp_appLE r φ _ ⊤ h₁)
  exact a₃.trans (a₁.symm.trans ((congrArg (r.appLE V ⊤ h).hom hi).trans a₂))

private theorem isDominant_of_isPullback {P X Y S : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : IsPullback fst snd f g) (hf : IsOpenMap f) [IsDominant g] : IsDominant fst := by
  refine ⟨(Dense.preimage g.denseRange hf).mono ?_⟩
  rintro a ⟨b, hb⟩
  obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback h a b hb.symm
  exact ⟨p, hp⟩

theorem UpperTheory.split_torus_pullback_generic_fibre :
    WtGeneric → ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ (K : Type) [Field K] (x : Sp K ⟶ C), IsGen x →
        ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus C X ⟶ G), IsMonHom u →
        ∀ (G' : Over (Sp K)) [GrpObj G'] (φ : G'.left ⟶ G.left) (u' : splitTorus (Sp K) X ⟶ G'), IsGrpPullback G' G x φ →
        TorusCompat x φ u' u → ∀ (χ : X) (U' : G'.left.Opens) (f' : Γ(G'.left, U')), (U' : Set G'.left).Nonempty → IsUnit f' →
        Wt u' U' f' χ → ∃ (U : G.left.Opens) (f : Γ(G.left, U)), (U : Set G.left).Nonempty ∧ IsUnit f ∧ Wt u U f χ := by
  intro hW k _ _ C _ hC K _ x hx G _ hG X _ _ _ u hu G' _ φ u' hφ hT χ U' f' ⟨y, hy⟩ hf' hwt
  have := LieSemineg.isIntegral_curve hC.1 hC.2.2
  have := hx.1
  have := hx.2
  have := hG.smooth
  have := hG.geomConnected
  have hu' : IsMonHom u' := hT.isMonHom hφ
  obtain ⟨-, -, -, -, h1, -, -, h2, -⟩ := (splitTorus_properties C).1 X
  have : Smooth (splitTorus C X).hom := SmoothOfRelativeDimension.smooth (Module.finrank ℤ X) _
  have : Smooth (splitTorus C X ⊗ G).hom :=
    inferInstanceAs (Smooth (pullback.fst (splitTorus C X).hom G.hom ≫ (splitTorus C X).hom))
  have : GeometricallyConnected (splitTorus C X ⊗ G).hom :=
    GeometricallyConnected.comp (pullback.fst (splitTorus C X).hom G.hom) (splitTorus C X).hom
  have hI : IsIntegral (splitTorus C X ⊗ G).left :=
    isIntegral_of_isPullback_of_smooth (IsPullback.id_horiz (splitTorus C X ⊗ G).hom)
  have : IsPreimmersion φ := MorphismProperty.of_isPullback (P := @IsPreimmersion) hφ.1.flip hx.2
  obtain ⟨U, f, V, hV, hf, hVU', hVU, H⟩ := spread_unit φ U' f' hf' y hy
  refine ⟨U, f, ⟨φ y, hVU hV⟩, hf, ?_⟩
  let τ := SplitTorus.bcMap x X
  let P' := splitTorus (Sp K) X ⊗ G'
  let ψ : P'.left ⟶ (splitTorus C X ⊗ G).left :=
    pullback.lift ((fst _ _ : P' ⟶ _).left ≫ τ) ((snd _ _ : P' ⟶ _).left ≫ φ) (by
      rw [Category.assoc, Category.assoc, SplitTorus.bcMap_hom, hφ.1.w, Over.w_assoc, Over.w_assoc])
  have hψ₁ : ψ ≫ (fst _ _ : splitTorus C X ⊗ G ⟶ _).left = (fst _ _ : P' ⟶ _).left ≫ τ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ (snd _ _ : splitTorus C X ⊗ G ⟶ _).left = (snd _ _ : P' ⟶ _).left ≫ φ := pullback.lift_snd _ _ _
  have sq : IsPullback ψ P'.hom (splitTorus C X ⊗ G).hom x := by
    have s₁ : IsPullback (fst _ _ : splitTorus C X ⊗ G ⟶ _).left (snd _ _ : splitTorus C X ⊗ G ⟶ _).left
      (splitTorus C X).hom G.hom := IsPullback.of_hasPullback _ _
    have s₂ : IsPullback (fst _ _ : P' ⟶ _).left (snd _ _ : P' ⟶ _).left
      (splitTorus (Sp K) X).hom G'.hom := IsPullback.of_hasPullback _ _
    have s₃ := s₂.paste_horiz (SplitTorus.isPullback_bcMap x X)
    rw [← hψ₁, ← hφ.1.w] at s₃
    have s₄ := (s₃.of_right hψ₂ s₁).paste_vert hφ.1
    rwa [Over.w, Over.w] at s₄
  have : IsIntegral P'.left := isIntegral_of_isPullback_of_smooth sq
  have : IsDominant ψ := isDominant_of_isPullback sq (splitTorus C X ⊗ G).hom.isOpenMap
  let O : P'.left.Opens := ((fst _ _ ≫ u') * snd _ _ : P' ⟶ G').left ⁻¹ᵁ V ⊓ (snd _ _ : P' ⟶ G').left ⁻¹ᵁ V
  have hO : (O : Set P'.left).Nonempty := by
    let s : G' ⟶ P' := lift 1 (𝟙 G')
    have e₁ : s ≫ ((fst _ _ ≫ u') * snd _ _ : P' ⟶ G') = 𝟙 G' := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, MonObj.one_comp, _root_.one_mul]
    have e₂ : s ≫ (snd _ _ : P' ⟶ G') = 𝟙 G' := lift_snd _ _
    refine ⟨s.left y, ?_, ?_⟩
    · show (s ≫ ((fst _ _ ≫ u') * snd _ _ : P' ⟶ G')).left y ∈ V
      rw [e₁]; exact hV
    · show (s ≫ (snd _ _ : P' ⟶ G')).left y ∈ V
      rw [e₂]; exact hV
  have : IsDominant O.ι := ⟨by
    have := O.isOpen.dense hO
    rwa [DenseRange, Scheme.Opens.range_ι]⟩
  let Z' : Over (Sp K) := Over.mk (O.ι ≫ P'.hom)
  let j : Z' ⟶ P' := Over.homMk O.ι rfl
  let t' : Z' ⟶ splitTorus (Sp K) X := j ≫ fst _ _
  let g' : Z' ⟶ G' := j ≫ snd _ _
  let t : Over.mk (Z'.hom ≫ x) ⟶ splitTorus C X := Over.homMk (t'.left ≫ τ) (by
    rw [Category.assoc, SplitTorus.bcMap_hom, Over.w_assoc]; rfl)
  let g : Over.mk (Z'.hom ≫ x) ⟶ G := Over.homMk (g'.left ≫ φ) (by
    rw [Category.assoc, hφ.1.w, Over.w_assoc]; rfl)
  have hm : ((t ≫ u) * g).left = ((t' ≫ u') * g').left ≫ φ :=
    hφ.2 Z' _ _ _ _ (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, ← torusCompat_iff.1 hT, ← Category.assoc]; rfl) rfl
  have hd : (lift t g).left = O.ι ≫ ψ := by
    refine pullback.hom_ext ?_ ?_
    · exact (congrArg (·.left) (lift_fst t g)).trans
        ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (O.ι ≫ ·) hψ₁)).symm)
    · exact (congrArg (·.left) (lift_snd t g)).trans
        ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (O.ι ≫ ·) hψ₂)).symm)
  have k₁ : ⊤ ≤ ((t' ≫ u') * g').left ⁻¹ᵁ V := by
    have : (t' ≫ u') * g' = j ≫ ((fst _ _ ≫ u') * snd _ _ : P' ⟶ G') := by
      rw [MonObj.comp_mul, Category.assoc]
    rw [this]
    exact fun z _ => z.2.1
  have k₂ : ⊤ ≤ g'.left ⁻¹ᵁ V := fun z _ => z.2.2
  have l₁ : ⊤ ≤ (((t' ≫ u') * g').left ≫ φ) ⁻¹ᵁ U := fun z hz => hVU (k₁ hz)
  have l₂ : ⊤ ≤ (g'.left ≫ φ) ⁻¹ᵁ U := fun z hz => hVU (k₂ hz)
  refine hW C G X u hI U f χ _ t g (by rw [hd]; infer_instance) (by rw [hm]; exact l₁) l₂ ?_
  have b₁ := H _ _ k₁ l₁ (fun z hz => hVU' (k₁ hz))
  have b₂ := H _ _ k₂ l₂ (fun z hz => hVU' (k₂ hz))
  have b₃ : t.left.appTop.hom (charUnit C X χ).val = t'.left.appTop.hom (charUnit (Sp K) X χ).val := by
    rw [← bcMap_charUnit x χ]
    rfl
  have b₄ : ∀ (r r' : Z'.left ⟶ G.left) (e : r = r') h h', (r.appLE U ⊤ h).hom f = (r'.appLE U ⊤ h').hom f := by
    intro r r' e h h'
    subst e
    rfl
  exact (b₄ _ _ hm _ l₁).trans (b₁.trans ((hwt Z' t' g' _ _).trans (congrArg₂ (· * ·) b₃.symm b₂.symm)))
