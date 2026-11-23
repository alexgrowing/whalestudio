import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatFamilyExistsUnique
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtExt.GlueSec

variable {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} {W : K → X.left.Opens} {u : Fn1 X}
  {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) {n : ℕ}
  (τ : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E)

def locVal (u : Fn1 X) (a : Fin n) {E : Type} [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E)
    (F : Type) [CommRing F] [Algebra R F] (ρ : E →ₐ[R] F) : F :=
  τ a F (ρ.comp ψ) - u E F ρ (spOver ψ ≫ x)

theorem pt_comp {E F : Type} [CommRing E] [Algebra R E] [CommRing F] [Algebra R F]
    (ψ : D →ₐ[R] E) (ρ : E →ₐ[R] F) : spOver (ρ.comp ψ) ≫ x = spOver ρ ≫ (spOver ψ ≫ x) := by
  rw [← spOver_comp, Category.assoc]

theorem sm_comp {E F : Type} [CommRing E] [Algebra R E] [CommRing F] [Algebra R F]
    (ψ : D →ₐ[R] E) (ρ : E →ₐ[R] F) (h : Sm W (spOver ψ ≫ x)) : Sm W (spOver (ρ.comp ψ) ≫ x) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, fun p _ ↦ ?_⟩
  rw [pt_comp]
  exact hi trivial

variable {x τ} {s : Fin n → D}

theorem locVal_map (hu : IsCoc W u)
    (hsec : ∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) →
      τ a E' (θ.comp ψ) - θ (τ a E ψ) = u E E' θ (spOver ψ ≫ x))
    (a : Fin n) {E : Type} [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E) (hsm : Sm W (spOver ψ ≫ x))
    {F G : Type} [CommRing F] [Algebra R F] [CommRing G] [Algebra R G] (ρ : E →ₐ[R] F) (θ : F →ₐ[R] G)
    (hunit : IsUnit (ρ (ψ (s a)))) :
    θ (locVal x τ u a ψ F ρ) = locVal x τ u a ψ G (θ.comp ρ) := by
  have h1 := hsec a F G (ρ.comp ψ) θ hunit
  have h2 := hu E F G ρ θ (spOver ψ ≫ x) hsm
  rw [pt_comp] at h1
  unfold locVal
  rw [map_sub, AlgHom.comp_assoc]
  linear_combination h2 - h1

theorem locVal_agree
    (hagree : ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → τ a E ψ = τ b E ψ)
    (a b : Fin n) {E : Type} [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E)
    {F : Type} [CommRing F] [Algebra R F] (ρ : E →ₐ[R] F)
    (ha : IsUnit (ρ (ψ (s a)))) (hb : IsUnit (ρ (ψ (s b)))) :
    locVal x τ u a ψ F ρ = locVal x τ u b ψ F ρ := by
  unfold locVal
  rw [hagree a b F (ρ.comp ψ) ha hb]

theorem span_range (hs : Ideal.span (Set.range s) = ⊤) {E : Type} [CommRing E] [Algebra R E]
    (ψ : D →ₐ[R] E) : Ideal.span (Set.range fun a ↦ ψ (s a)) = ⊤ := by
  have : (Set.range fun a ↦ ψ (s a)) = ψ '' Set.range s := (Set.range_comp ψ s)
  rw [this, ← Ideal.map_span, hs, Ideal.map_top]

end GlobalTheory.PtExt.GlueSec

namespace GlobalTheory.PtExt.GlueSec

variable {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} {W : K → X.left.Opens} {u : Fn1 X}
  {D : Type} [CommRing D] [Algebra R D] {x : Pt X D} {n : ℕ}
  {τ : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E} {s : Fin n → D}

theorem isUnit_locAlg {E : Type} [CommRing E] [Algebra R E] (t : E) : IsUnit (locAlg R t t) :=
  IsLocalization.Away.algebraMap_isUnit t

theorem glue_exists (hs : Ideal.span (Set.range s) = ⊤) (hu : IsCoc W u)
    (hsec : ∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) →
      τ a E' (θ.comp ψ) - θ (τ a E ψ) = u E E' θ (spOver ψ ≫ x))
    (hagree : ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → τ a E ψ = τ b E ψ)
    {E : Type} [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E) (hsm : Sm W (spOver ψ ≫ x)) :
    ∃ e : E, ∀ (F : Type) [CommRing F] [Algebra R F] (ρ : E →ₐ[R] F) (a : Fin n),
      IsUnit (ρ (ψ (s a))) → ρ e = locVal x τ u a ψ F ρ := by
  let T : Set E := Set.range fun a ↦ ψ (s a)
  have hT : Ideal.span T = ⊤ := span_range hs ψ
  have hc : ∀ t : T, ∃ a, ψ (s a) = t.1 := fun t ↦ t.2
  choose c hc using hc
  have hcu : ∀ t : T, IsUnit (locAlg R t.1 (ψ (s (c t)))) := fun t ↦ by
    rw [hc t]; exact isUnit_locAlg _
  let v : ∀ t : T, Localization.Away t.1 := fun t ↦ locVal x τ u (c t) ψ _ (locAlg R t.1)
  obtain ⟨e, he, -⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top T hT v (fun t₁ t₂ ↦ by
    change awR R t₁.1 t₂.1 (v t₁) = awL R t₁.1 t₂.1 (v t₂)
    have hm : IsUnit (locAlg R (t₁.1 * t₂.1) (t₁.1 * t₂.1)) := isUnit_locAlg _
    rw [map_mul] at hm
    simp only [v]
    rw [locVal_map hu hsec _ ψ hsm _ _ (hcu t₁), locVal_map hu hsec _ ψ hsm _ _ (hcu t₂), awR_comp, awL_comp]
    apply locVal_agree hagree
    · rw [hc t₁]; exact isUnit_of_mul_isUnit_left hm
    · rw [hc t₂]; exact isUnit_of_mul_isUnit_right hm)
  refine ⟨e, fun F _ _ ρ a ha ↦ ?_⟩
  apply Localization.algebraMap_injective_of_span_eq_top _ (span_range hs (ρ.comp ψ))
  funext ⟨_, b, rfl⟩
  let t : T := ⟨ψ (s b), b, rfl⟩
  let lam : F →ₐ[R] Localization.Away (ρ (ψ (s b))) := locAlg R (ρ (ψ (s b)))
  let mu : Localization.Away t.1 →ₐ[R] Localization.Away (ρ (ψ (s b))) := Localization.awayMapₐ ρ t.1
  have hmu : mu.comp (locAlg R t.1) = lam.comp ρ := AlgHom.ext fun z ↦ by
    simp [mu, lam, t, Localization.awayMapₐ, IsLocalization.Away.mapₐ, IsLocalization.Away.map,
      IsLocalization.map_eq]
  change lam (ρ e) = lam (locVal x τ u a ψ F ρ)
  have het : locAlg R t.1 e = v t := he t
  rw [locVal_map hu hsec a ψ hsm ρ lam ha]
  rw [show lam (ρ e) = mu (locAlg R t.1 e) from (DFunLike.congr_fun hmu e).symm, het]
  simp only [v]
  rw [locVal_map hu hsec _ ψ hsm _ _ (hcu t), hmu]
  apply locVal_agree hagree
  · rw [AlgHom.comp_apply, hc t]; exact isUnit_locAlg _
  · exact ha.map lam

end GlobalTheory.PtExt.GlueSec

namespace GlobalTheory.PtExt

open GlueSec in

theorem glue_sections : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens) (u : Fn1 X), IsCoc W u → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D) (n : ℕ) (s : Fin n → D), Ideal.span (Set.range s) = ⊤ → ∀ τ : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, (∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → τ a E' (θ.comp ψ) - θ (τ a E ψ) = u E E' θ (spOver ψ ≫ x)) → (∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → τ a E ψ = τ b E ψ) → ∃ σ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), Sm W (spOver ψ ≫ x) → σ E' (θ.comp ψ) - θ (σ E ψ) = u E E' θ (spOver ψ ≫ x) := by
  intro R _ X K W u hu D _ _ x n s hs τ hsec hagree
  classical
  let σ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E := fun E _ _ ψ ↦
    if h : Sm W (spOver ψ ≫ x) then Classical.choose (glue_exists hs hu hsec hagree ψ h) else 0
  refine ⟨σ, fun E _ _ E' _ _ ψ θ hsm ↦ ?_⟩
  have hsm' : Sm W (spOver (θ.comp ψ) ≫ x) := sm_comp x ψ θ hsm
  have P := Classical.choose_spec (glue_exists hs hu hsec hagree ψ hsm)
  have P' := Classical.choose_spec (glue_exists hs hu hsec hagree (θ.comp ψ) hsm')
  have e1 : σ E ψ = Classical.choose (glue_exists hs hu hsec hagree ψ hsm) := dif_pos hsm
  have e2 : σ E' (θ.comp ψ) = Classical.choose (glue_exists hs hu hsec hagree (θ.comp ψ) hsm') := dif_pos hsm'
  rw [e1, e2]
  apply Localization.algebraMap_injective_of_span_eq_top _ (span_range hs (θ.comp ψ))
  funext ⟨_, a, rfl⟩
  let lam : E' →ₐ[R] Localization.Away ((θ.comp ψ) (s a)) := locAlg R ((θ.comp ψ) (s a))
  let lt : E →ₐ[R] Localization.Away ((θ.comp ψ) (s a)) := lam.comp θ
  change lam (Classical.choose (glue_exists hs hu hsec hagree (θ.comp ψ) hsm') - θ (Classical.choose (glue_exists hs hu hsec hagree ψ hsm))) = lam (u E E' θ (spOver ψ ≫ x))
  rw [map_sub, P' (Localization.Away ((θ.comp ψ) (s a))) lam a (isUnit_locAlg ((θ.comp ψ) (s a))),
    show lam (θ (Classical.choose (glue_exists hs hu hsec hagree ψ hsm))) =
      lt (Classical.choose (glue_exists hs hu hsec hagree ψ hsm)) from rfl,
    P (Localization.Away ((θ.comp ψ) (s a))) lt a (isUnit_locAlg (R := R) ((θ.comp ψ) (s a)))]
  have h2 := hu E E' (Localization.Away ((θ.comp ψ) (s a))) θ lam (spOver ψ ≫ x) hsm
  unfold locVal
  simp only [lt]
  rw [pt_comp x ψ θ, AlgHom.comp_assoc]
  linear_combination h2

end GlobalTheory.PtExt
