import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusStableGoodOpenOfWeightUnits
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothTorusQuotientOfGoodOpenCover
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

private theorem equivar_of_goodOpen {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]
    (u : splitTorus S X ⟶ G) (V : G.left.Opens) (hV : GoodOpen u V)
    (j : Over.mk (V.ι ≫ G.hom) ⟶ G) (hj : j.left = V.ι) :
    (∃ τ : Over.mk (V.ι ≫ G.hom) ⟶ splitTorus S X, TorusSlice.Equivar u j τ) ∧
      ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (p : Z ⟶ Over.mk (V.ι ≫ G.hom)),
        ∃ p' : Z ⟶ Over.mk (V.ι ≫ G.hom), p' ≫ j = (t ≫ u) * (p ≫ j) := by
  obtain ⟨-, h₂, v, hv⟩ := hV
  have h0 : ⊤ ≤ j.left ⁻¹ᵁ V := fun z _ => by
    change j.left z ∈ V
    rw [hj]; exact z.2
  have pre : ∀ {Z : Over S} (c : Z ⟶ Over.mk (V.ι ≫ G.hom)), ⊤ ≤ (c ≫ j).left ⁻¹ᵁ V := fun c z _ => by
    change (c ≫ j).left z ∈ V
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact h0 (Set.mem_univ _)
  refine ⟨⟨(splitTorusPointsEquiv S X _).symm
    ((Units.map (j.left.appLE V ⊤ h0).hom.toMonoidHom).comp v), fun Z t y y' h => ?_⟩, fun Z t p => ?_⟩
  · apply (splitTorusPointsEquiv S X Z).injective
    refine MonoidHom.ext fun χ => Units.ext ?_
    have e : TorusSlice.ch ((splitTorusPointsEquiv S X (Over.mk (V.ι ≫ G.hom))).symm
        ((Units.map (j.left.appLE V ⊤ h0).hom.toMonoidHom).comp v)) χ.toAdd
        = (j.left.appLE V ⊤ h0).hom (v χ).val := by
      rw [TorusSlice.ch_eq, MulEquiv.apply_symm_apply]; rfl
    have := hv χ.toAdd Z t (y ≫ j) (h ▸ pre y') (pre y)
    rw [TorusSlice.appLE_comp_top y' _ _ h.symm _ _ h0, TorusSlice.appLE_comp_top y _ _ rfl _ _ h0] at this
    refine (TorusSlice.ch_eq _ χ.toAdd).symm.trans (Eq.trans ?_ (TorusSlice.ch_eq _ χ.toAdd))
    rw [TorusSlice.ch_mul, TorusSlice.ch_comp, TorusSlice.ch_comp, e]
    exact this
  · have hr : Set.range ((t ≫ u) * (p ≫ j)).left ⊆ Set.range V.ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      have e1 : (t ≫ u) * (p ≫ j) = lift t (p ≫ j) ≫
          ((fst (splitTorus S X) G ≫ u) * snd (splitTorus S X) G) := by
        simp [MonObj.comp_mul]
      have e2 : lift t (p ≫ j) ≫ snd (splitTorus S X) G = p ≫ j := lift_snd _ _
      rw [e1, Over.comp_left, Scheme.Hom.comp_apply]
      apply h₂
      change (snd (splitTorus S X) G).left ((lift t (p ≫ j)).left z) ∈ V
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e2]
      exact pre p (Set.mem_univ _)
    refine ⟨Over.homMk (IsOpenImmersion.lift V.ι _ hr) ?_, ?_⟩
    · exact (IsOpenImmersion.lift_fac_assoc _ _ hr _).trans (Over.w _)
    · refine Over.OverMorphism.ext ?_
      rw [Over.comp_left, hj]
      exact IsOpenImmersion.lift_fac _ _ hr

theorem UpperTheory.good_open_translate_section :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsCommMonObj G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G), IsMonHom u →
        ∀ V : G.left.Opens, GoodOpen u V → ∀ (U : S.Opens) (σ : Over.mk U.ι ⟶ G) (T : Over S) (p : T ⟶ Over.mk U.ι) (w : T ⟶ G)
        (t : T.left), w.left t ∈ V → ∃ V' : G.left.Opens, GoodOpen u V' ∧ ((p ≫ σ) * w).left t ∈ V' := by
  intro S G _ hc X _ _ _ u hu V hV U σ T p w t ht
  have hW : (snd (splitTorus S X) G).left ⁻¹ᵁ (G.hom ⁻¹ᵁ U) ≤
      ((fst (splitTorus S X) G ≫ u) * snd (splitTorus S X) G).left ⁻¹ᵁ (G.hom ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, Over.w, Over.w]
  have htU : w.left t ∈ G.hom ⁻¹ᵁ U := by
    change G.hom (w.left t) ∈ U
    rw [← Scheme.Hom.comp_apply, Over.w, ← Over.w p, Scheme.Hom.comp_apply]
    exact (p.left t).2
  obtain ⟨b, hb, hbU⟩ := TorusQuotientGlue.exists_invariant hV hW ht htU
  have hV₁ := TorusQuotientGlue.goodOpen_basicOpen hV b.2
  generalize G.left.basicOpen b.1 = V₁ at hb hbU hV₁
  let P : Over S := Over.mk (V₁.ι ≫ G.hom)
  let j : P ⟶ G := Over.homMk V₁.ι rfl
  obtain ⟨⟨τ, hτ⟩, hs⟩ := equivar_of_goodOpen u V₁ hV₁ j rfl
  have hr : Set.range (V₁.ι ≫ G.hom) ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact hbU z.2
  let q : P ⟶ Over.mk U.ι := Over.homMk (IsOpenImmersion.lift U.ι _ hr) (IsOpenImmersion.lift_fac _ _ hr)
  have huniq : ∀ {Z : Over S} (f g : Z ⟶ Over.mk U.ι), f = g := fun f g => by
    refine Over.OverMorphism.ext ?_
    rw [← cancel_mono U.ι]
    exact (Over.w f).trans (Over.w g).symm
  let a : P ⟶ G := (q ≫ σ) * j
  have hsnd : IsOpenImmersion (snd (Over.mk U.ι) G).left :=
    inferInstanceAs (IsOpenImmersion (pullback.snd U.ι G.hom))
  have hl : (lift q j).left ≫ (snd (Over.mk U.ι) G).left = V₁.ι := by
    rw [← Over.comp_left, lift_snd]; rfl
  have hlo : IsOpenImmersion (lift q j).left := by
    have : IsOpenImmersion ((lift q j).left ≫ (snd (Over.mk U.ι) G).left) := by
      rw [hl]; exact inferInstanceAs (IsOpenImmersion V₁.ι)
    exact IsOpenImmersion.of_comp _ (snd (Over.mk U.ι) G).left
  have hiso : IsIso (TorusSlice.shearIso σ).hom.left :=
    inferInstanceAs (IsIso ((Over.forget S).map (TorusSlice.shearIso σ).hom))
  have key : ∀ {Z : Over S} (f : Z ⟶ Over.mk U.ι) (g : Z ⟶ G), ((f ≫ σ) * g).left =
      (lift f g).left ≫ (TorusSlice.shearIso σ).hom.left ≫ (snd (Over.mk U.ι) G).left := fun f g => by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp [TorusSlice.shearIso, MonObj.comp_mul]
  have hao : IsOpenImmersion a.left := by
    rw [key q j]; infer_instance
  have haff : IsAffine P.left := hV₁.1
  have ha : ∀ {Z : Over S} (y y' : Z ⟶ P), y' ≫ a = (y ≫ q ≫ σ) * (y' ≫ j) := fun y y' => by
    rw [MonObj.comp_mul, ← Category.assoc y', ← Category.assoc y, huniq (y' ≫ q) (y ≫ q)]
  refine ⟨_, TorusSlice.goodOpen_of_equivar u a τ (fun Z s y y' h => hτ Z s y y' ?_) (fun Z s y => ?_), ?_⟩
  · rw [ha y y', ha y y, mul_left_comm] at h
    exact mul_left_cancel h
  · obtain ⟨y', h⟩ := hs Z s y
    exact ⟨y', by rw [ha y y', ha y y, h, mul_left_comm]⟩
  · rw [Scheme.Hom.image_top_eq_opensRange]
    obtain ⟨x, hx⟩ : ∃ x : P.left, j.left x = w.left t := ⟨⟨w.left t, hb⟩, rfl⟩
    refine ⟨x, ?_⟩
    have e : (lift q j).left x = (lift p w).left t := by
      apply (snd (Over.mk U.ι) G).left.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, lift_snd,
        lift_snd, hx]
    rw [key p w, key q j, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply (lift p w).left, e]
