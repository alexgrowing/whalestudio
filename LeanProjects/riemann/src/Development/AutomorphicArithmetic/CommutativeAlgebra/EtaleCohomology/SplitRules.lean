import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

def SplitOn {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (x : X ⟶ Y) {m : ℕ} (z : Fin m → (X ⟶ Z)) : Prop :=
  ∃ h : ∀ i, z i ≫ p = x, IsIso (Sigma.desc (fun i => pullback.lift (z i) (𝟙 X) (by rw [h i, Category.id_comp])) :
    ∐ (fun _ : Fin m => X) ⟶ pullback p x)

abbrev awayPt (l : ℕ) (U : Type) [CommRing U] : Spec (CommRingCat.of (Localization.Away (l : U))) ⟶ Spec (CommRingCat.of U) :=
  Spec.map (CommRingCat.ofHom (algebraMap U (Localization.Away (l : U))))

structure WDat (l : ℕ) {Y : Scheme.{0}} {J : Type} (T : J → Corr l Y) : Type 1 where
  W : Scheme.{0}
  π : W ⟶ Y
  s : ∀ j, Fin (T j).d → (W ⟶ (T j).Z)
  hs : ∀ j i, s j i ≫ (T j).p = π
  gen : ∀ (X : Scheme.{0}) (w : X ⟶ W), IsUnit (l : Γ(X, ⊤)) → ∀ j, SplitOn (T j).p (w ≫ π) fun i => w ≫ s j i
  univ : ∀ (U : Type) [CommRing U], (l : U) ∈ nonZeroDivisors U → ∀ (y : Spec (CommRingCat.of U) ⟶ Y)
    (z : ∀ j, Fin (T j).d → (Spec (CommRingCat.of U) ⟶ (T j).Z)), (∀ j i, z j i ≫ (T j).p = y) →
    (∀ j, SplitOn (T j).p (awayPt l U ≫ y) fun i => awayPt l U ≫ z j i) →
    ∃! w : Spec (CommRingCat.of U) ⟶ W, w ≫ π = y ∧ ∀ j i, w ≫ s j i = z j i

def WEx : Prop := ∀ (l : ℕ) (Y : Scheme.{0}) (J : Type) [Fintype J] (T : J → Corr l Y), Nonempty (WDat l T)

def SplitEx : Prop := ∀ (l : ℕ), l.Prime → ∀ (Y : Scheme.{0}) (T : Corr l Y) (U : Type) [CommRing U], (l : U) ∈ nonZeroDivisors U →
  (∀ x : Localization.Away (l : U), IsIntegral U x → ∃ u : U, algebraMap U _ u = x) →
  (∀ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of (Localization.Away (l : U)))), Etale f → Surjective f → ∃ s, s ≫ f = 𝟙 _) →
  ∀ y : Spec (CommRingCat.of U) ⟶ Y, ∃ z : Fin T.d → (Spec (CommRingCat.of U) ⟶ T.Z), (∀ i, z i ≫ T.p = y) ∧
    SplitOn T.p (awayPt l U ≫ y) fun i => awayPt l U ≫ z i

def SplitPerm : Prop := ∀ (l : ℕ) (Y : Scheme.{0}) (T : Corr l Y) (U : Type) [CommRing U], (l : U) ∈ nonZeroDivisors U →
  (∀ x : Localization.Away (l : U), IsIntegral U x → ∃ u : U, algebraMap U _ u = x) →
  ∀ (y : Spec (CommRingCat.of U) ⟶ Y) (z z' : Fin T.d → (Spec (CommRingCat.of U) ⟶ T.Z)), (∀ i, z i ≫ T.p = y) → (∀ i, z' i ≫ T.p = y) →
  (SplitOn T.p (awayPt l U ≫ y) fun i => awayPt l U ≫ z i) → (SplitOn T.p (awayPt l U ≫ y) fun i => awayPt l U ≫ z' i) →
  ∃ e : Equiv.Perm (Fin T.d) → U, CompleteOrthogonalIdempotents e ∧ ∀ (σ : Equiv.Perm (Fin T.d)) (V : Type) [CommRing V] (ρ : U →+* V),
    ρ (e σ) = 1 → ∀ i, Spec.map (CommRingCat.ofHom ρ) ≫ z' i = Spec.map (CommRingCat.ofHom ρ) ≫ z (σ i)

def SplitRules : Prop :=
  (∀ {X' X Y Z : Scheme.{0}} (p : Z ⟶ Y) (x : X ⟶ Y) (g : X' ⟶ X) {m : ℕ} (z : Fin m → (X ⟶ Z)), SplitOn p x z →
    (SplitOn p (g ≫ x) fun i => g ≫ z i) ∧ ∀ σ : Equiv.Perm (Fin m), SplitOn p x fun i => z (σ i)) ∧
  ∀ (l : ℕ) (Y : Scheme.{0}) (T : Corr l Y) (U : Y.Opens), IsAffineOpen U → ∀ (B : Type) [CommRing B]
    (y : Spec (CommRingCat.of B) ⟶ Y) (hy : ⊤ ≤ y ⁻¹ᵁ U) (z : Fin T.d → (Spec (CommRingCat.of B) ⟶ T.Z))
    (hz : ∀ i, ⊤ ≤ z i ⁻¹ᵁ (T.p ⁻¹ᵁ U)), (∀ i, z i ≫ T.p = y) → (SplitOn T.p (awayPt l B ≫ y) fun i => awayPt l B ≫ z i) →
    letI := T.alg U
    letI : Algebra Γ(Y, U) B := ((y.appLE U ⊤ hy ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom).toAlgebra
    ∃ ζ : Fin T.d → (Γ(T.Z, T.p ⁻¹ᵁ U) →ₐ[Γ(Y, U)] B), SplitsAway l ζ ∧
      ∀ i a, ζ i a = ((z i).appLE (T.p ⁻¹ᵁ U) ⊤ (hz i) ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom a

end UpperTheory.Ru.crystallineComparison
