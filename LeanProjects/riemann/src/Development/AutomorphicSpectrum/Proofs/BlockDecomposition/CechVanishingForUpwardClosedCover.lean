import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIffStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechCohomologyFullSubcategoryIsoStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GlobRel

theorem subsingleton_H_of_retract {R : Type} [CommRing R] {K L : Cx R}
    (φ : Cx.Hom K L (RingHom.id R)) (ψ : Cx.Hom L K (RingHom.id R))
    (h : ∀ n x, ψ.f n (φ.f n x) = x) (n : ℕ) (hL : Subsingleton (L.H n)) : Subsingleton (K.H n) := by
  have key : ∀ a : K.H n, ψ.mapH n (φ.mapH n a) = a := by
    intro a
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    change Submodule.Quotient.mk (ψ.mapZ n (φ.mapZ n z)) = Submodule.Quotient.mk z
    congr 1
    exact Subtype.ext (h n z.1)
  refine ⟨fun a b => ?_⟩
  rw [← key a, ← key b, Subsingleton.elim (φ.mapH n a) (φ.mapH n b)]

theorem subsingleton_HU_iter {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
    (F : C ⥤ ModuleCat.{0} R) (A B : ObjectProperty C) (P : ObjectProperty A.FullSubcategory)
    (hBA : ∀ T, B T → A T) (hP : ∀ T : A.FullSubcategory, P T ↔ B T.obj) (j : ℕ)
    (hB : Subsingleton (HU F B j)) : Subsingleton (HU (A.ι ⋙ F) P j) := by
  let G : B.FullSubcategory ⥤ P.FullSubcategory :=
    P.lift (A.lift B.ι fun T => hBA _ T.property) fun T => (hP _).2 T.property
  let G' : P.FullSubcategory ⥤ B.FullSubcategory :=
    B.lift (P.ι ⋙ A.ι) fun T => (hP _).1 T.property
  let m : CH.Mor (P.ι ⋙ A.ι ⋙ F) (B.ι ⋙ F) (RingHom.id R) := ⟨G, fun _ => LinearMap.id, fun _ _ => rfl⟩
  let m' : CH.Mor (B.ι ⋙ F) (P.ι ⋙ A.ι ⋙ F) (RingHom.id R) := ⟨G', fun _ => LinearMap.id, fun _ _ => rfl⟩
  exact subsingleton_H_of_retract m.hom m'.hom (fun n x => funext fun s => rfl) j hB

theorem glob_van_rel : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type} [Fintype ι]
    (W : ι → ObjectProperty C) (hW : ∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T') (s : ℕ),
    ((∀ S : Finset ι, S.Nonempty → ∀ j < s, Subsingleton (HU F (capS W S) j)) →
      ∀ j < s, Subsingleton (CH.H ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ F) j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU F (capS W S) j)) →
      ∀ j, Subsingleton (CH.H ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ F) j)) ∧
    ((∀ S : Finset ι, S.Nonempty → ∀ j > s, Subsingleton (HU F (capS W S) j)) →
      ∀ j, s + Fintype.card ι ≤ j → Subsingleton (CH.H ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ F) j)) := by
  intro R _ C _ F ι _ W hW s
  let U' : ι → ObjectProperty (ObjectProperty.FullSubcategory fun T : C => ∃ α, W α T) :=
    fun α T => W α T.obj
  have hU : ∀ α, Cosieve (U' α) := fun α T T' f h => hW α f.hom h T'.property
  have hc : ∀ T, ∃ α, U' α T := fun T => T.property
  have tr : ∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU F (capS W S) j) →
      Subsingleton (HU ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ F) (capS U' S) j) := by
    intro S hS j h
    obtain ⟨a, ha⟩ := hS
    exact subsingleton_HU_iter F _ (capS W S) (capS U' S) (fun T hT => ⟨a, hT a ha⟩)
      (fun T => Iff.rfl) j h
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.cech_vanishing_from_cover ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ F) U' hU hc s
  exact ⟨fun h j hj => h1 (fun S hS j hj => tr S hS j (h S hS j hj)) j hj,
    fun h j => h2 (fun S hS j => tr S hS j (h S hS j)) j,
    fun h j hj => h3 (fun S hS j hj => tr S hS j (h S hS j hj)) j hj⟩

end GlobalTheory.CompanionTheory.GlobRel
