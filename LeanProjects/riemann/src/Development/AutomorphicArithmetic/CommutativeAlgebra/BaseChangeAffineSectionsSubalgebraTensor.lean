import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackGamma
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private lemma scal {k : Type} [Field k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k)
    [Algebra k C.functionField]
    (h : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) =
      (C.fromSpecStalk (genericPoint C)) ≫ c)
    (W : C.Opens) [Nonempty W] :
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c.appLE ⊤ W le_top ≫ C.germToFunctionField W =
      CommRingCat.ofHom (algebraMap k C.functionField) := by
  have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k C.functionField))
  rw [h, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop] at h1
  have hm : (Spec (C.presheaf.stalk (genericPoint C))).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk (genericPoint C))).Opens) ≤ ⊤)).op = 𝟙 _ :=
    (Spec (C.presheaf.stalk (genericPoint C))).presheaf.map_id _
  have h2 : CommRingCat.ofHom (algebraMap k C.functionField) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c.appTop ≫ C.presheaf.germ ⊤ (genericPoint C) trivial := by
    rw [← cancel_mono (Scheme.ΓSpecIso (C.presheaf.stalk (genericPoint C))).inv]
    refine h1.trans ?_
    simp only [Category.assoc]
    erw [hm, Category.comp_id]
  rw [h2]
  simp only [Scheme.Hom.appLE, Category.assoc]
  congr 2
  exact C.presheaf.germ_res (homOfLE le_top) (genericPoint C) _

theorem UpperTheory.baseChange_affine_sections_subalgebra_tensor :
    ∀ (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ (W : C.Opens) [Nonempty W], IsAffineOpen W → ∀ B : Subalgebra k C.functionField, (B : Set C.functionField) = Set.range (C.germToFunctionField W) → IsAffineOpen (u ⁻¹ᵁ W) ∧ ∃ e : L ⊗[k] B ≃+* Γ(X, u ⁻¹ᵁ W), (∀ (a : Γ(C, W)) (b : B), (b : C.functionField) = C.germToFunctionField W a → e ((1 : L) ⊗ₜ[k] b) = u.app W a) ∧ ∀ l : L, e (l ⊗ₜ[k] (1 : B)) = x.appLE ⊤ (u ⁻¹ᵁ W) le_top ((Scheme.ΓSpecIso (CommRingCat.of L)).inv l) := by
  intro k L _ _ _ C X _ c u x H _ hK W _ hW B hB
  have hu : IsAffineHom u := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  refine ⟨hW.preimage u, ?_⟩
  let g0 : Γ(C, W) →+* C.functionField := (C.germToFunctionField W).hom
  have hinj : Function.Injective g0 := C.germToFunctionField_injective W
  have hmem : ∀ a, g0 a ∈ B := fun a => by
    have : g0 a ∈ (B : Set C.functionField) := by rw [hB]; exact ⟨a, rfl⟩
    exact this
  let g1 : Γ(C, W) →+* B := g0.codRestrict B hmem
  have hbij : Function.Bijective g1 := by
    refine ⟨fun a a' h => hinj (congrArg Subtype.val h), fun b => ?_⟩
    have : (b : C.functionField) ∈ (B : Set C.functionField) := b.2
    rw [hB] at this
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Subtype.ext ha⟩
  let gB : Γ(C, W) ≃+* B := RingEquiv.ofBijective g1 hbij
  let iB : CommRingCat.of B ≅ Γ(C, W) := gB.symm.toCommRingCatIso
  have hP := (GroundTheory.Arith.SchemeCoh.isPushout_app_of_isPullback H hW).flip
  have hT := CommRingCat.isPushout_tensorProduct k L B
  have hP' : IsPushout (CommRingCat.ofHom (algebraMap k L)) (CommRingCat.ofHom (algebraMap k B))
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appLE ⊤ (u ⁻¹ᵁ W) le_top)
      (iB.hom ≫ u.app W) := by
    refine hP.of_iso (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) iB.symm (Iso.refl _)
      (Scheme.ΓSpecIso_naturality _) ?_ (by simp) (by simp)
    rw [← Iso.inv_comp_eq]
    ext r
    exact congr($(scal c hK W).hom r)
  let E := IsPushout.isoIsPushout _ _ hT hP'
  refine ⟨E.commRingCatIsoToRingEquiv, ?_, ?_⟩
  · intro a b hab
    have h1 := congr($(IsPushout.inr_isoIsPushout_hom _ _ hT hP').hom b)
    have h2 : iB.hom b = a := by
      apply hinj
      have h3 := congrArg Subtype.val (gB.apply_symm_apply b)
      exact h3.trans hab
    rw [← h2]
    exact h1
  · intro l
    have h1 := congr($(IsPushout.inl_isoIsPushout_hom _ _ hT hP').hom l)
    exact h1
