import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AdicCompleteAlgebraLiftingUniqueStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.LiftHom
open GlobalTheory.AdicColimit

section SpecForm
variable {R : Type} [CommRing R] (I : Ideal R)

abbrev specOver (A : Type) [CommRing A] [Algebra R A] : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

variable (A : Type) [CommRing A] [Algebra R A]

abbrev redA (e : ℕ) : Type := A ⧸ (I ^ (e + 1)).map (algebraMap R A)

def redι (e : ℕ) : Spec (CommRingCat.of (redA I A e)) ⟶ (thickObj R I e (specOver A)).left :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (I ^ (e + 1))).symm.toRingEquiv.toRingHom) ≫
    (pullbackSpecIso R A (R ⧸ I ^ (e + 1))).inv

instance isIso_redι (e : ℕ) : IsIso (redι I A e) := by
  unfold redι
  have : IsIso (CommRingCat.ofHom
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (I ^ (e + 1))).symm.toRingEquiv.toRingHom) :=
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (I ^ (e + 1))).symm.toRingEquiv.toCommRingCatIso).isIso_hom
  infer_instance

theorem redι_fst (e : ℕ) : redι I A e ≫ thickι I e (specOver A) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R A)))) := by
  have h := pullbackSpecIso_inv_fst R A (R ⧸ I ^ (e + 1))
  have h2 : (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (I ^ (e + 1))).symm.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] (R ⧸ I ^ (e + 1))) =
      Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R A)) := by
    ext a
    change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (I ^ (e + 1))).symm (a ⊗ₜ[R] 1) = _
    rw [← Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, AlgEquiv.symm_apply_apply]
  unfold redι
  rw [Category.assoc]
  refine (congrArg (fun t => Spec.map _ ≫ t) h).trans ?_
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h2]

theorem map_le (e : ℕ) : (I ^ (e + 1 + 1)).map (algebraMap R A) ≤ (I ^ (e + 1)).map (algebraMap R A) :=
  Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ _))

theorem redι_trans (e : ℕ) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (map_le I A e))) ≫ redι I A (e + 1) =
      redι I A e ≫ thickMap R I e (specOver A) := by
  rw [← cancel_mono (thickι I (e + 1) (specOver A)), Category.assoc, Category.assoc, redι_fst, thickMap_ι,
    redι_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end SpecForm

section Lift
variable {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]

theorem spec_lift (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Module.Finite R A]
    (v : ∀ e, (thickObj R I e (specOver A)).left ⟶ Spec (CommRingCat.of B))
    (hover : ∀ e, v e ≫ (specOver B).hom = thickι I e (specOver A) ≫ (specOver A).hom)
    (hc : ∀ e, thickMap R I e (specOver A) ≫ v (e + 1) = v e) :
    ∃! c : specOver A ⟶ specOver B, ∀ e, thickι I e (specOver A) ≫ c.left = v e := by
  have hfe : ∀ e, Spec.map (Spec.preimage (redι I A e ≫ v e)) = redι I A e ≫ v e := fun e => Spec.map_preimage _
  have hlin : ∀ e, CommRingCat.ofHom (algebraMap R B) ≫ Spec.preimage (redι I A e ≫ v e) =
      CommRingCat.ofHom (algebraMap R (redA I A e)) := fun e => by
    apply Spec.map_injective
    rw [Spec.map_comp, hfe, Category.assoc]
    refine (congrArg (fun t => redι I A e ≫ t) (hover e)).trans ?_
    rw [← Category.assoc, redι_fst]
    exact (Spec.map_comp _ _).symm
  let f : ∀ e, B →ₐ[R] redA I A e := fun e =>
    { (Spec.preimage (redι I A e ≫ v e)).hom with
      commutes' := fun r => congrArg (fun φ => φ.hom r) (hlin e) }
  have hf : ∀ e, CommRingCat.ofHom (f e : B →+* redA I A e) = Spec.preimage (redι I A e ≫ v e) := fun e => rfl
  have hcompat : ∀ e (b : B) (a : A), Ideal.Quotient.mk _ a = f (e + 1) b → Ideal.Quotient.mk _ a = f e b := by
    intro e b a h
    have key : Spec.preimage (redι I A (e + 1) ≫ v (e + 1)) ≫
        CommRingCat.ofHom (Ideal.Quotient.factor (map_le I A e)) = Spec.preimage (redι I A e ≫ v e) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hfe, hfe, ← Category.assoc, redι_trans, Category.assoc, hc]
    have h2 := congrArg (fun φ => φ.hom b) key
    have h3 := congrArg (Ideal.Quotient.factor (map_le I A e)) h
    rw [Ideal.Quotient.factor_mk] at h3
    exact h3.trans h2
  obtain ⟨g, hg, hu⟩ := GlobalTheory.T.adic_complete_algebra_lifting_unique R A B I f hcompat
  have hgover : Spec.map (CommRingCat.ofHom (g : B →+* A)) ≫ (specOver (R := R) B).hom = (specOver (R := R) A).hom := by
    change _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, g.comp_algebraMap]
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom (g : B →+* A))) hgover, fun e => ?_, fun c' hc' => ?_⟩
  · rw [← cancel_epi (redι I A e), ← Category.assoc, redι_fst]
    change _ ≫ Spec.map _ = _
    rw [← hfe, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hf]
    congr 2
    ext b
    exact hg e b
  · have hp : Spec.map (Spec.preimage c'.left) = c'.left := Spec.map_preimage _
    have hlin' : CommRingCat.ofHom (algebraMap R B) ≫ Spec.preimage c'.left = CommRingCat.ofHom (algebraMap R A) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hp]
      exact Over.w c'
    let g' : B →ₐ[R] A :=
      { (Spec.preimage c'.left).hom with commutes' := fun r => congrArg (fun φ => φ.hom r) hlin' }
    have hg' : CommRingCat.ofHom (g' : B →+* A) = Spec.preimage c'.left := rfl
    have e1 : g' = g := hu g' fun e b => by
      have key : Spec.preimage c'.left ≫ CommRingCat.ofHom (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R A))) =
          Spec.preimage (redι I A e ≫ v e) := by
        apply Spec.map_injective
        rw [Spec.map_comp, hfe, hp, ← redι_fst, Category.assoc, hc']
      exact congrArg (fun φ => φ.hom b) key
    apply Over.OverMorphism.ext
    rw [← hp, ← hg', e1]
    rfl

omit [IsNoetherianRing R] in

theorem exists_specOver (X : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A), Nonempty (X ≅ specOver A) := by
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  let ψ : CommRingCat.of R ⟶ Γ(X.left, ⊤) := Spec.preimage (X.left.isoSpec.inv ≫ X.hom)
  have hψ : Spec.map ψ = X.left.isoSpec.inv ≫ X.hom := Spec.map_preimage _
  let _ : Algebra R Γ(X.left, ⊤) := ψ.hom.toAlgebra
  have hfin : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
  have hfin' : ψ.hom.Finite := (IsFinite.SpecMap_iff ψ).1 hfin
  refine ⟨Γ(X.left, ⊤), inferInstance, inferInstance, hfin', ⟨Over.isoMk X.left.isoSpec ?_⟩⟩
  change _ ≫ Spec.map ψ = _
  rw [hψ, Iso.hom_inv_id_assoc]

theorem over_lift (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom]
    (v : ∀ e, (thickObj R I e X).left ⟶ Y.left)
    (hover : ∀ e, v e ≫ Y.hom = thickι I e X ≫ X.hom)
    (hc : ∀ e, thickMap R I e X ≫ v (e + 1) = v e) :
    ∃! c : X ⟶ Y, ∀ e, thickι I e X ≫ c.left = v e := by
  obtain ⟨A, _, _, _, ⟨α⟩⟩ := exists_specOver X
  obtain ⟨B, _, _, _, ⟨β⟩⟩ := exists_specOver Y
  have hid : ∀ {T T' : Over (Spec (CommRingCat.of R))} (a : T ≅ T') (e : ℕ),
      thickHom I e a.hom ≫ thickHom I e a.inv = 𝟙 _ := fun a e => by
    rw [← Over.comp_left, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
    rfl
  obtain ⟨c', hc', hu⟩ := spec_lift I A B (fun e => thickHom I e α.inv ≫ v e ≫ β.hom.left)
    (fun e => by
      rw [Category.assoc, Category.assoc, Over.w β.hom, hover, thickHom_ι_assoc, Over.w α.inv])
    (fun e => by
      rw [thickMap_thickHom_assoc, reassoc_of% (hc e)])
  refine ⟨α.hom ≫ c' ≫ β.inv, fun e => ?_, fun c2 h2 => ?_⟩
  · have h1 := hc' e
    rw [Over.comp_left, Over.comp_left, ← thickHom_ι_assoc, reassoc_of% h1, reassoc_of% (hid α e)]
    rw [← Over.comp_left, Iso.hom_inv_id]
    exact Category.comp_id _
  · have h3 := hu (α.inv ≫ c2 ≫ β.hom) fun e => by
      rw [Over.comp_left, Over.comp_left, ← thickHom_ι_assoc, reassoc_of% (h2 e)]
    rw [← h3]
    simp

theorem scheme_lift (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom]
    (f : ∀ e, thickObj R I e X ⟶ thickObj R I e Y)
    (hf : ∀ e, thickMap R I e X ≫ (f (e + 1)).left = (f e).left ≫ thickMap R I e Y) :
    ∃! c : X ⟶ Y, ∀ e, (Over.pullback (thick R I e)).map c = f e := by
  have hiff : ∀ (c : X ⟶ Y) e, (Over.pullback (thick R I e)).map c = f e ↔
      thickι I e X ≫ c.left = (f e).left ≫ thickι I e Y := fun c e => by
    constructor
    · intro h
      rw [← h, thickHom_ι]
    · intro h
      apply Over.OverMorphism.ext
      rw [← cancel_mono (thickι I e Y), thickHom_ι, h]
  obtain ⟨c, hc, hu⟩ := over_lift I X Y (fun e => (f e).left ≫ thickι I e Y)
    (fun e => by
      have h1 := Over.w (f e)
      simp only [Over.pullback_obj_hom] at h1
      rw [Category.assoc, pullback.condition, reassoc_of% h1, ← pullback.condition])
    (fun e => by
      rw [reassoc_of% (hf e), thickMap_ι])
  exact ⟨c, fun e => (hiff c e).2 (hc e), fun c' h => hu c' fun e => (hiff c' e).1 (h e)⟩

theorem hom_ext_of_finite {X Y : Over (Spec (CommRingCat.of R))} [IsFinite X.hom] [IsFinite Y.hom] (c c' : X ⟶ Y)
    (h : ∀ e, (Over.pullback (thick R I e)).map c = (Over.pullback (thick R I e)).map c') : c = c' := by
  obtain ⟨c₀, -, hu⟩ := scheme_lift I X Y (fun e => (Over.pullback (thick R I e)).map c')
    (fun e => thickMap_thickHom I e c')
  exact (hu c h).trans (hu c' fun _ => rfl).symm

end Lift

section Hom

theorem isMonHom_of_comp_mono {C : Type*} [Category C] [CartesianMonoidalCategory C] {A B D : C} [MonObj A] [MonObj B]
    [MonObj D] (g : A ⟶ B) (j : B ⟶ D) [IsMonHom j] [Mono j] [IsMonHom (g ≫ j)] : IsMonHom g := by
  refine ⟨?_, ?_⟩
  · rw [← cancel_mono j, Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono j, Category.assoc, IsMonHom.mul_hom (g ≫ j), Category.assoc, IsMonHom.mul_hom j,
      tensorHom_comp_tensorHom_assoc]

variable {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]

theorem isMonHom_of_reductions {P Q : Over (Spec (CommRingCat.of R))} [GrpObj P] [GrpObj Q] [IsFinite P.hom]
    [IsFinite Q.hom] (c : P ⟶ Q) (h : ∀ e, IsMonHom ((Over.pullback (thick R I e)).map c)) : IsMonHom c := by
  refine ⟨?_, ?_⟩
  · have : IsFinite (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := inferInstanceAs (IsFinite (𝟙 _))
    refine hom_ext_of_finite I _ _ fun n => ?_
    have e := (h n).one_hom
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi, ← Functor.map_comp] at e
    exact e
  · have : IsFinite (P ⊗ P).hom := inferInstanceAs (IsFinite (pullback.fst P.hom P.hom ≫ P.hom))
    refine hom_ext_of_finite I _ _ fun n => ?_
    have e := (h n).mul_hom
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc,
      cancel_epi, ← Functor.map_comp, ← Functor.map_comp] at e
    exact e

end Hom

theorem lift_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P Q P' Q' : Over (Spec (CommRingCat.of R))) [GrpObj P] [GrpObj Q] [GrpObj P'] [GrpObj Q'] [IsFinite P.hom] [IsFinite Q.hom] (jP : P ⟶ P') (jQ : Q ⟶ Q') [IsMonHom jP] [IsMonHom jQ] [Mono jQ] (φ : ∀ e, thickObj R I e P' ⟶ thickObj R I e Q'), (∀ e, IsMonHom (φ e)) → (∀ e, thickMap R I e P' ≫ (φ (e + 1)).left = (φ e).left ≫ thickMap R I e Q') → (∀ e, ∃ w : thickObj R I e P ⟶ thickObj R I e Q, w ≫ (Over.pullback (thick R I e)).map jQ = (Over.pullback (thick R I e)).map jP ≫ φ e) → ∃ c : P ⟶ Q, IsMonHom c ∧ ∀ e, (Over.pullback (thick R I e)).map (c ≫ jQ) = (Over.pullback (thick R I e)).map jP ≫ φ e := by
  intro R _ _ _ I _ P Q P' Q' _ _ _ _ _ _ jP jQ _ _ _ φ hφ hcomp hw
  choose w hw using hw
  have hmono : ∀ e, Mono ((Over.pullback (thick R I e)).map jQ) := fun e => inferInstance
  have hmonoL : ∀ e, Mono (thickHom I e jQ) := fun e => by
    have := hmono e
    exact inferInstanceAs (Mono ((Over.forget _).map ((Over.pullback (thick R I e)).map jQ)))
  have hwc : ∀ e, thickMap R I e P ≫ (w (e + 1)).left = (w e).left ≫ thickMap R I e Q := fun e => by
    have := hmonoL (e + 1)
    rw [← cancel_mono (thickHom I (e + 1) jQ), Category.assoc, Category.assoc, thickMap_thickHom]
    have h1 : (w (e + 1)).left ≫ thickHom I (e + 1) jQ =
        thickHom I (e + 1) jP ≫ (φ (e + 1)).left := congrArg (fun t => t.left) (hw (e + 1))
    have h2 : (w e).left ≫ thickHom I e jQ = thickHom I e jP ≫ (φ e).left := congrArg (fun t => t.left) (hw e)
    rw [h1, reassoc_of% h2, thickMap_thickHom_assoc, hcomp]
  obtain ⟨c, hc, -⟩ := scheme_lift I P Q w hwc
  have hcj : ∀ e, (Over.pullback (thick R I e)).map (c ≫ jQ) = (Over.pullback (thick R I e)).map jP ≫ φ e :=
    fun e => by rw [Functor.map_comp, hc, hw]
  refine ⟨c, isMonHom_of_reductions I c fun e => ?_, hcj⟩
  have := hφ e
  have := hmono e
  have : IsMonHom ((Over.pullback (thick R I e)).map c ≫ (Over.pullback (thick R I e)).map jQ) := by
    rw [← Functor.map_comp, hcj]
    infer_instance
  exact isMonHom_of_comp_mono _ ((Over.pullback (thick R I e)).map jQ)

end GlobalTheory.CompanionTheory.Ar.BT.LiftHom
