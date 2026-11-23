import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.GalV

variable (l : ℕ) [Fact l.Prime]

abbrev Htot (E : Spc) : Type 1 := DirectSum ℤ fun n : ℤ => HQ l E n 0

def pullTot {E E' : Spc} (f : E ⟶ E') : Htot l E' →ₗ[ℚ_[l]] Htot l E :=
  DirectSum.lmap fun n => pullHQ l f n 0

theorem pullTot_id (E : Spc) : pullTot l (𝟙 E) = LinearMap.id := by
  simp only [pullTot, pullHQ, pullHl_id, LinearMap.baseChange_id]
  exact DirectSum.lmap_id

theorem pullTot_comp {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') :
    pullTot l (f ≫ g) = pullTot l f ∘ₗ pullTot l g := by
  simp only [pullTot, pullHQ, pullHl_comp, LinearMap.baseChange_comp]
  exact DirectSum.lmap_comp _ _

def galTot {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) :
    (Ω ≃ₐ[k] Ω) → Htot l (sch.obj (GlobalTheory.Et.geom Ω p)) →ₗ[ℚ_[l]] Htot l (sch.obj (GlobalTheory.Et.geom Ω p)) :=
  fun σ => pullTot l (sch.map (GlobalTheory.Et.galMap Ω p σ))

private theorem galMap_one' {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) : GlobalTheory.Et.galMap Ω p (1 : Ω ≃ₐ[k] Ω) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [GlobalTheory.Et.galMap_fst, Category.id_comp]
  · rw [GlobalTheory.Et.galMap_snd, Category.id_comp]
    have h1 : CommRingCat.ofHom ((1 : Ω ≃ₐ[k] Ω) : Ω →+* Ω) = 𝟙 _ := by
      ext x; rfl
    rw [h1, Spec.map_id, Category.comp_id]

theorem galTot_one {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) :
    galTot l Ω p 1 = LinearMap.id := by
  simp only [galTot]
  rw [galMap_one', CategoryTheory.Functor.map_id, pullTot_id]

private theorem galMap_mul' {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) (σ τ : Ω ≃ₐ[k] Ω) :
    GlobalTheory.Et.galMap Ω p (σ * τ) = GlobalTheory.Et.galMap Ω p σ ≫ GlobalTheory.Et.galMap Ω p τ := by
  apply pullback.hom_ext
  · rw [GlobalTheory.Et.galMap_fst, Category.assoc, GlobalTheory.Et.galMap_fst, GlobalTheory.Et.galMap_fst]
  · have h2 : CommRingCat.ofHom ((σ * τ : Ω ≃ₐ[k] Ω) : Ω →+* Ω) =
        CommRingCat.ofHom (τ : Ω →+* Ω) ≫ CommRingCat.ofHom (σ : Ω →+* Ω) := by
      ext x; rfl
    rw [GlobalTheory.Et.galMap_snd, Category.assoc, GlobalTheory.Et.galMap_snd, GlobalTheory.Et.galMap_snd_assoc, h2, Spec.map_comp]

theorem galTot_mul {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))
    (σ τ : Ω ≃ₐ[k] Ω) : galTot l Ω p (σ * τ) = galTot l Ω p σ ∘ₗ galTot l Ω p τ := by
  simp only [galTot]
  rw [galMap_mul', CategoryTheory.Functor.map_comp, pullTot_comp]

def galTotRep {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) :
    Representation ℚ_[l] (Ω ≃ₐ[k] Ω) (Htot l (sch.obj (GlobalTheory.Et.geom Ω p))) where
  toFun := galTot l Ω p
  map_one' := galTot_one l Ω p
  map_mul' := galTot_mul l Ω p

def CDeg {Y X : Scheme.{0}} (f : Y ⟶ X) (d : ℕ) : Prop :=
  ∃ (U : Scheme.{0}) (u : U ⟶ X), Etale u ∧ Surjective u ∧
    ∃ e : ∐ (fun _ : Fin d => U) ≅ pullback f u, e.hom ≫ pullback.snd f u = Limits.Sigma.desc (fun _ => 𝟙 U)

def Splits {Z Y W : Scheme.{0}} (s : Y ⟶ Z) (c : W ⟶ Z) {J : Type} (σ : J → (W ⟶ Y)) : Prop :=
  ∃ h : ∀ j, σ j ≫ s = c,
    IsIso (Limits.Sigma.desc (fun j => pullback.lift (σ j) (𝟙 W) (by rw [h j, Category.id_comp])) :
      ∐ (fun _ : J => W) ⟶ pullback s c)

def IsGalois {W X : Scheme.{0}} (c : W ⟶ X) (G : Type) [Group G] (a : G → (W ⟶ W)) : Prop :=
  IsFinite c ∧ Etale c ∧ Surjective c ∧ a 1 = 𝟙 W ∧ (∀ g h, a (g * h) = a g ≫ a h) ∧ Splits c c a

def IsCorrOp {Z Y Z' : Scheme.{0}} (s : Y ⟶ Z) (t : Y ⟶ Z') (T : Htot l (sch.obj Z') →ₗ[ℚ_[l]] Htot l (sch.obj Z)) : Prop :=
  ∃ (W : Scheme.{0}) (c : W ⟶ Z) (G : Type) (_ : Group G) (_ : Finite G) (a : G → (W ⟶ W)) (J : Type) (_ : Fintype J)
    (σ : J → (W ⟶ Y)), IsGalois c G a ∧ Splits s c σ ∧
    ∀ x, pullTot l (sch.map c) (T x) = ∑ j, pullTot l (sch.map (σ j ≫ t)) x

variable {l}

def genEig {H : Type*} [AddCommGroup H] [Module ℚ_[l] H] (L : Type*) [Field L] [Algebra ℚ_[l] L] {J : Type*}
    (T : J → H →ₗ[ℚ_[l]] H) (θ : J → L) : Submodule L (TensorProduct ℚ_[l] L (H)) :=
  ⨅ j, Module.End.maxGenEigenspace ((T j).baseChange L) (θ j)

variable (l)

theorem isGalois_id (X : Scheme.{0}) : IsGalois (𝟙 X) Unit (fun _ => 𝟙 X) := by
  refine ⟨inferInstance, inferInstance, inferInstance, rfl, fun _ _ => (Category.comp_id _).symm,
    fun _ => Category.comp_id _, ?_⟩
  have hd : IsIso (Sigma.desc (fun _ : Unit => 𝟙 X)) :=
    ⟨⟨Sigma.ι (fun _ : Unit => X) (), by ext j; cases j; simp, by simp⟩⟩
  refine (isIso_comp_right_iff _ (pullback.fst (𝟙 X) (𝟙 X))).mp ?_
  convert hd using 1
  ext j
  simp
  exact pullback.lift_fst _ _ _

theorem splits_fold (X : Scheme.{0}) (J : Type) :
    Splits (Sigma.desc fun _ : J => 𝟙 X) (𝟙 X) (Sigma.ι (fun _ : J => X)) := by
  refine ⟨fun _ => by simp, ?_⟩
  refine (isIso_comp_right_iff _ (pullback.fst (Sigma.desc fun _ : J => 𝟙 X) (𝟙 X))).mp ?_
  convert (inferInstance : IsIso (𝟙 (∐ fun _ : J => X))) using 1
  ext j
  simp
  exact pullback.lift_fst _ _ _

theorem isCorrOp_fold {X Z' : Scheme.{0}} {J : Type} [Fintype J] (f : J → (X ⟶ Z')) :
    IsCorrOp l (Sigma.desc fun _ : J => 𝟙 X) (Sigma.desc f) (∑ j, pullTot l (sch.map (f j))) := by
  refine ⟨X, 𝟙 X, Unit, inferInstance, inferInstance, fun _ => 𝟙 X, J, inferInstance, Sigma.ι (fun _ : J => X),
    isGalois_id X, splits_fold X J, fun x => ?_⟩
  rw [CategoryTheory.Functor.map_id, pullTot_id, LinearMap.id_apply, LinearMap.sum_apply]
  simp only [Sigma.ι_desc]

example (X : Scheme.{0}) : IsCorrOp l (𝟙 X) (𝟙 X) LinearMap.id := by
  refine ⟨X, 𝟙 X, Unit, inferInstance, inferInstance, fun _ => 𝟙 X, Unit, inferInstance, fun _ => 𝟙 X,
    isGalois_id X, ⟨fun _ => Category.id_comp _, ?_⟩, fun x => ?_⟩
  · exact (isGalois_id X).2.2.2.2.2.2
  · simp [pullTot_id]

example {X Z' : Scheme.{0}} (f : Fin 2 → (X ⟶ Z')) :
    IsCorrOp l (Sigma.desc fun _ : Fin 2 => 𝟙 X) (Sigma.desc f) (pullTot l (sch.map (f 0)) + pullTot l (sch.map (f 1))) := by
  simpa [Fin.sum_univ_two] using isCorrOp_fold l f

example {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) :
    galTotRep l Ω p 1 = LinearMap.id := map_one _

end GlobalTheory.GalV

end
