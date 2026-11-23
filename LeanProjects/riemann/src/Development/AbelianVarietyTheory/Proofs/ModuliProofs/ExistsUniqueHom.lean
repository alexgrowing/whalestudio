import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem existsUnique_hom {X Y : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}} (ψ : ∀ i, Z i ⟶ X)
    (hψ : ∀ i, IsOpenImmersion (ψ i)) (hc : ∀ x : X, ∃ i, x ∈ Set.range (ψ i)) (f : ∀ i, Z i ⟶ Y)
    (hf : ∀ i j (T : Scheme.{0}) (x : T ⟶ Z i) (y : T ⟶ Z j), x ≫ ψ i = y ≫ ψ j → x ≫ f i = y ≫ f j) :
    ∃! F : X ⟶ Y, ∀ i, ψ i ≫ F = f i := by
  let C : X.OpenCover := Scheme.Cover.mkOfCovers I Z ψ (fun x => by simpa using hc x) hψ
  refine ⟨C.glueMorphisms f fun i j => hf i j _ _ _ pullback.condition, fun i => C.ι_glueMorphisms _ _ i,
    fun F hF => C.hom_ext _ _ fun i => (hF i).trans (C.ι_glueMorphisms f _ i).symm⟩

theorem hom_ext {X Y : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}} (ψ : ∀ i, Z i ⟶ X)
    (hψ : ∀ i, IsOpenImmersion (ψ i)) (hc : ∀ x : X, ∃ i, x ∈ Set.range (ψ i)) {F F' : X ⟶ Y}
    (h : ∀ i, ψ i ≫ F = ψ i ≫ F') : F = F' :=
  (existsUnique_hom ψ hψ hc (fun i => ψ i ≫ F') fun _ _ _ _ _ e => by
    rw [← Category.assoc, e, Category.assoc]).unique h fun _ => rfl

theorem exists_hom {X Y : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}} (ψ : ∀ i, Z i ⟶ X)
    (hψ : ∀ i, IsOpenImmersion (ψ i)) (hc : ∀ x : X, ∃ i, x ∈ Set.range (ψ i)) (f : ∀ i, Z i ⟶ Y)
    {B : I → I → Scheme.{0}} {a : ∀ i j, B i j ⟶ Z i} {b : ∀ i j, B i j ⟶ Z j}
    (hB : ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) (hf : ∀ i j, a i j ≫ f i = b i j ≫ f j) :
    ∃ F : X ⟶ Y, ∀ i, ψ i ≫ F = f i :=
  (existsUnique_hom ψ hψ hc f fun i j _ x y e => by
    rw [← (hB i j).lift_fst x y e, Category.assoc, hf, ← Category.assoc, (hB i j).lift_snd]).exists

variable {S : Scheme.{0}} {I : Type} {U : I → S.Opens}

theorem exists_mem (hU : iSup U = ⊤) (s : S) : ∃ i, s ∈ U i :=
  TopologicalSpace.Opens.mem_iSup.1 (show s ∈ iSup U by rw [hU]; trivial)

theorem isOpenImmersion {X Z : Scheme.{0}} {V : S.Opens} {p : X ⟶ S} {q : Z ⟶ V.toScheme} {ψ : Z ⟶ X}
    (h : IsPullback ψ q p V.ι) : IsOpenImmersion ψ :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip inferInstance

theorem mem_range {X Z : Scheme.{0}} {V : S.Opens} {p : X ⟶ S} {q : Z ⟶ V.toScheme} {ψ : Z ⟶ X}
    (h : IsPullback ψ q p V.ι) (x : X) : x ∈ Set.range ψ ↔ p x ∈ V := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
    exact (q z).2
  · intro hx
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback h x ⟨p x, hx⟩ rfl
    exact ⟨z, hz⟩

theorem covers (hU : iSup U = ⊤) {X : Scheme.{0}} {Z : I → Scheme.{0}} {p : X ⟶ S} {q : ∀ i, Z i ⟶ (U i).toScheme}
    {ψ : ∀ i, Z i ⟶ X} (h : ∀ i, IsPullback (ψ i) (q i) p (U i).ι) (x : X) : ∃ i, x ∈ Set.range (ψ i) :=
  (exists_mem hU (p x)).imp fun i hi => (mem_range (h i) x).2 hi

theorem over_ext (hU : iSup U = ⊤) {T A : Over S} {f g : T ⟶ A}
    (h : ∀ i (T' : Over (U i).toScheme) (r : Over.mk (T'.hom ≫ (U i).ι) ⟶ T), r ≫ f = r ≫ g) : f = g := by
  ext1
  refine hom_ext (fun i => (T.hom ⁻¹ᵁ U i).ι) (fun _ => inferInstance)
    (covers hU fun i => (isPullback_morphismRestrict T.hom (U i)).flip) fun i => ?_
  exact congrArg (fun z => z.left) (h i (Over.mk (T.hom ∣_ U i))
    (Over.homMk (T.hom ⁻¹ᵁ U i).ι (morphismRestrict_ι _ _).symm))

theorem exists_lift {S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {G : Over S'} {ψ : G.left ⟶ A.left}
    (h : IsPullback ψ G.hom A.hom f) {T : Over S'} (x₀ : Over.mk (T.hom ≫ f) ⟶ A) :
    ∃ x : T ⟶ G, x₀.left = x.left ≫ ψ :=
  ⟨Over.homMk (h.lift x₀.left T.hom (Over.w x₀)) (h.lift_snd _ _ _), (h.lift_fst _ _ _).symm⟩

theorem lift_ext {S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {G : Over S'} {ψ : G.left ⟶ A.left}
    (h : IsPullback ψ G.hom A.hom f) {T : Over S'} {x y : T ⟶ G} (e : x.left ≫ ψ = y.left ≫ ψ) : x = y :=
  Over.OverMorphism.ext (h.hom_ext e ((Over.w x).trans (Over.w y).symm))

end GlobalTheory.CoverGlue
