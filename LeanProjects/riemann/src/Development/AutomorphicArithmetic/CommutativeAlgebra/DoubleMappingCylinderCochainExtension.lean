import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNaturalStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.PushoutCovers

private noncomputable def Fe (p : ℕ) (U : Scheme.{0}) : Spc ⥤ Type 1 :=
  ((evaluation _ _).obj (op (SimplexCategory.mk p))) ⋙ ((evaluation _ _).obj (op U)) ⋙ uliftFunctor.{1, 0}

private theorem po (P : Arrow Spc) (p : ℕ) (U : Scheme.{0}) :
    IsPushout ((Fe p U).map P.hom) ((Fe p U).map P.hom) ((Fe p U).map (dbl.inl P)) ((Fe p U).map (dbl.inr P)) := by
  have : PreservesColimit (span P.hom P.hom) (Fe p U) := by
    unfold Fe
    infer_instance
  exact (IsPushout.of_hasPushout P.hom P.hom).map (Fe p U)

private theorem cover (P : Arrow Spc) (p : ℕ) (U : Scheme.{0}) (w : Sx (dbl P) p U) :
    (∃ z : Sx P.right p U, z.map (dbl.inl P) = w) ∨ ∃ z : Sx P.right p U, z.map (dbl.inr P) = w := by
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit (po P p U).isColimit (ULift.up w)
  rcases j with _ | j
  · left
    exact ⟨Sx.map P.hom y.down, congrArg ULift.down hy⟩
  · cases j
    · left
      exact ⟨y.down, congrArg ULift.down hy⟩
    · right
      exact ⟨y.down, congrArg ULift.down hy⟩

private theorem fn (P : Arrow Spc) (p : ℕ) (U : Scheme.{0}) {T : Type 1} [Zero T] (f : Sx P.right p U → T)
    (hf : ∀ y : Sx P.left p U, f (y.map P.hom) = 0) :
    ∃ φ : Sx (dbl P) p U → T, (∀ z : Sx P.right p U, φ (z.map (dbl.inl P)) = f z) ∧ ∀ z : Sx P.right p U, φ (z.map (dbl.inr P)) = 0 := by
  have h := po P p U
  let d : (Fe p U).obj (dbl P) ⟶ T :=
    h.desc (TypeCat.ofHom fun z => f z.down) (TypeCat.ofHom fun _ => 0) (by
      ext y
      exact hf y.down)
  refine ⟨fun w => d (ULift.up w), fun z => ?_, fun z => ?_⟩
  · exact ConcreteCategory.congr_hom (CC := fun X => X) (h.inl_desc _ _ _)
      (ULift.up z : ULift.{1} (Sx P.right p U))
  · exact ConcreteCategory.congr_hom (CC := fun X => X) (h.inr_desc _ _ _)
      (ULift.up z : ULift.{1} (Sx P.right p U))

private theorem res_map {E E' : Spc} (f : E ⟶ E') {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (z : Sx E p U) :
    (z.map f).res g = (z.res g).map f := by
  exact (FunctorToTypes.naturality (f.app _) g.op z).symm

end UpperTheory.PushoutCovers

open UpperTheory.PushoutCovers in
theorem UpperTheory.doubleMappingCylinder_cochain_extension :
    ∀ (R : Type) [CommRing R] (P : Arrow Spc), (∀ (p : ℕ) (U : Scheme.{0}) (w : Sx (dbl P) p U), (∃ z : Sx P.right p U, z.map (dbl.inl P) = w) ∨ ∃ z : Sx P.right p U, z.map (dbl.inr P) = w) ∧
    ∀ (K : Cx R) (m N : ℤ) (x : (famDC (Sub.img P.hom) K m).Tot), ∃ γ : Cochain ((chains R).obj (dbl P)) K N, Comp (dbl.inl P) γ x ∧ ∀ (p : ℕ) (s : ℤ) h (U : Scheme.{0}) (z : Sx P.right p U), ev γ p s h U (z.map (dbl.inr P)) = 0 := by
  intro R _ P
  refine ⟨fun p U w => cover P p U w, ?_⟩
  intro K m N x
  have key : ∀ (p : ℕ) (s' : ℤ) (U : Scheme.{0}), ∃ φ : Sx (dbl P) p U → Sec (K.X s') U,
      ∀ (s : ℤ) (e : s + m = s'), ∀ z : Sx P.right p U,
        φ (z.map (dbl.inl P)) = e ▸ (x p s).1 U z ∧ φ (z.map (dbl.inr P)) = 0 := by
    intro p s' U
    obtain ⟨s, rfl⟩ : ∃ s, s' = s + m := ⟨s' - m, by ring⟩
    obtain ⟨φ, h1, h2⟩ := fn P p U (T := Sec (K.X (s + m)) U) ((x p s).1 U)
      (fun y => (x p s).2.2 U _ ⟨y, rfl⟩)
    refine ⟨φ, fun s1 e z => ?_⟩
    obtain rfl : s1 = s := by omega
    exact ⟨h1 z, h2 z⟩
  choose φ hφ using key
  have nat : ∀ (p : ℕ) (s' : ℤ) (_ : -(p : ℤ) + N = s') (V U : Scheme.{0}) (g : V ⟶ U)
      (w : Sx (dbl P) p U), Sec.res g (φ p s' U w) = φ p s' V (Sx.res g w) := by
    intro p s' _ V U g w
    obtain ⟨s, rfl⟩ : ∃ s, s' = s + m := ⟨s' - m, by ring⟩
    rcases cover P p U w with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · rw [(hφ p (s + m) U s rfl z).1, res_map, (hφ p (s + m) V s rfl _).1]
      exact (x p s).2.1 V U g z
    · rw [(hφ p (s + m) U s rfl z).2, res_map, (hφ p (s + m) V s rfl _).2]
      exact map_zero _
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' R (E := dbl P) (I := K) (n := N) (fun p s' _ U => φ p s' U) nat
  refine ⟨γ, fun p s h U z => ?_, fun p s h U z => ?_⟩
  · rw [hγ]
    exact ((hφ p (s + m) U s rfl z).1).symm
  · rw [hγ]
    exact (hφ p s U (s - m) (by ring) z).2
