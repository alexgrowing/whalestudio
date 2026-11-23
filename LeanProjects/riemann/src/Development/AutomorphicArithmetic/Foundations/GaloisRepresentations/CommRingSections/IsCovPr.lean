import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechSeparated

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GroundTheory.Arith.SchemeCoh (inter inter_le_comp)

namespace UpperTheory.Gal.DifferentialFormSections

variable {K : Type} [CommRing K]

abbrev Fm (K A : Type) [CommRing K] [CommRing A] [Algebra K A] : Type := ExteriorAlgebra A Ω[A⁄K]

section
variable {A B : Type} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

def dd (K : Type) [CommRing K] [Algebra K A] (a : A) : Fm K A := ExteriorAlgebra.ι A (KaehlerDifferential.D K A a)

def fmMap (φ : A →ₐ[K] B) : Fm K A →ₐ[K] Fm K B :=
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
  (ExteriorAlgebra.lift A ⟨((ExteriorAlgebra.ι B).restrictScalars A) ∘ₗ KaehlerDifferential.map K K A B,
    fun _ => ExteriorAlgebra.ι_sq_zero _⟩).restrictScalars K

def dlog (K : Type) [CommRing K] [Algebra K A] (u : Aˣ) : Fm K A := (↑u⁻¹ : A) • dd K (u : A)

def sgn (n : ℕ) : Fm K A →ₗ[K] Fm K A :=
  (((CliffordAlgebra.involute (Q := (0 : QuadraticForm A Ω[A⁄K]))) ^ n : _ →ₐ[A] _).toLinearMap).restrictScalars K
end

abbrev Sch (K : Type) [CommRing K] : Type 1 := Over (Spec (CommRingCat.of K))

def Sec (X : Sch K) (U : X.left.Opens) : Type := Γ(X.left, U)

instance (X : Sch K) (U : X.left.Opens) : CommRing (Sec X U) := inferInstanceAs (CommRing Γ(X.left, U))

instance (X : Sch K) (U : X.left.Opens) : Algebra K (Sec X U) :=
  (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ Scheme.Hom.appLE X.hom ⊤ U le_top).hom : K →+* Γ(X.left, U)).toAlgebra

def secMap {X Y : Sch K} (f : Y ⟶ X) {U : X.left.Opens} {V : Y.left.Opens} (h : V ≤ f.left ⁻¹ᵁ U) : Sec X U →ₐ[K] Sec Y V where
  toRingHom := (Scheme.Hom.appLE f.left U V h).hom
  commutes' r := by
    have e : Scheme.Hom.appLE X.hom ⊤ U le_top ≫ Scheme.Hom.appLE f.left U V h = Scheme.Hom.appLE Y.hom ⊤ V le_top := by
      refine (Scheme.Hom.appLE_comp_appLE f.left X.hom ⊤ U V le_top h).trans ?_
      have e2 := Over.w f
      revert e2
      generalize Y.hom = g
      rintro rfl
      rfl
    exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom r)) e

def secRes (X : Sch K) {U V : X.left.Opens} (h : V ≤ U) : Sec X U →ₐ[K] Sec X V := secMap (𝟙 X) h

variable {X Y : Sch K} {ι κ : Type}

abbrev cap (U : ι → X.left.Opens) {n : ℕ} (i : Fin n → ι) : X.left.Opens := inter (X := X.left.toTopCat) U i

abbrev Co (U : ι → X.left.Opens) (n : ℕ) : Type := ∀ i : Fin (n + 1) → ι, Fm K (Sec X (cap U i))

def dC (U : ι → X.left.Opens) (n : ℕ) : Co U n →ₗ[K] Co U (n + 1) :=
  LinearMap.pi fun i => ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
    ((fmMap (secRes X (inter_le_comp (X := X.left.toTopCat) U i k.succAbove))).toLinearMap ∘ₗ LinearMap.proj (i ∘ k.succAbove))

def Bd (U : ι → X.left.Opens) : (n : ℕ) → Submodule K (Co U n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (dC U n)

abbrev HC (U : ι → X.left.Opens) (n : ℕ) : Type := LinearMap.ker (dC U n) ⧸ (Bd U n).submoduleOf (LinearMap.ker (dC U n))

open Classical in

def cls {U : ι → X.left.Opens} {n : ℕ} (σ : Co U n) : HC U n :=
  if h : dC U n σ = 0 then Submodule.Quotient.mk ⟨σ, h⟩ else 0

def rep {U : ι → X.left.Opens} {n : ℕ} (x : HC U n) : Co U n := (Quotient.out x).1

def cupC {U : ι → X.left.Opens} {a b n : ℕ} (h : a + b = n) (σ : Co U a) (τ : Co U b) : Co U n := fun i =>
  fmMap (secRes X (inter_le_comp (X := X.left.toTopCat) U i fun s : Fin (a + 1) => ⟨s, by omega⟩)) (sgn b (σ _)) *
    fmMap (secRes X (inter_le_comp (X := X.left.toTopCat) U i fun s : Fin (b + 1) => ⟨a + s, by omega⟩)) (τ _)

def cupH {U : ι → X.left.Opens} {a b n : ℕ} (h : a + b = n) (x : HC U a) (y : HC U b) : HC U n := cls (cupC h (rep x) (rep y))

theorem cap_le (f : Y ⟶ X) {U : ι → X.left.Opens} {V : κ → Y.left.Opens} (t : κ → ι) (ht : ∀ j, V j ≤ f.left ⁻¹ᵁ U (t j))
    {n : ℕ} (j : Fin n → κ) : cap V j ≤ f.left ⁻¹ᵁ cap U (t ∘ j) := fun x hx =>
  (GroundTheory.Arith.SchemeCoh.mem_inter_iff (X := X.left.toTopCat) (U := U) (t ∘ j) _).2 fun a =>
    ht (j a) ((GroundTheory.Arith.SchemeCoh.mem_inter_iff (X := Y.left.toTopCat) (U := V) j x).1 hx a)

def pullC (f : Y ⟶ X) {U : ι → X.left.Opens} {V : κ → Y.left.Opens} (t : κ → ι) (ht : ∀ j, V j ≤ f.left ⁻¹ᵁ U (t j)) (n : ℕ) :
    Co U n →ₗ[K] Co V n :=
  LinearMap.pi fun j => (fmMap (secMap f (cap_le f t ht j))).toLinearMap ∘ₗ LinearMap.proj (t ∘ j)

def pullHC (f : Y ⟶ X) {U : ι → X.left.Opens} {V : κ → Y.left.Opens} (t : κ → ι) (ht : ∀ j, V j ≤ f.left ⁻¹ᵁ U (t j)) {n : ℕ}
    (x : HC U n) : HC V n := cls (pullC f t ht n (rep x))

abbrev all (X : Sch K) : X.left.affineOpens → X.left.Opens := Subtype.val

abbrev H (X : Sch K) (n : ℕ) : Type := HC (all X) n

def deg (U : ι → X.left.Opens) (a n : ℕ) : Submodule K (HC U n) :=
  Submodule.span K {x | ∃ σ : Co U n, (∀ i, σ i ∈ ⋀[Sec X (cap U i)]^a Ω[Sec X (cap U i)⁄K]) ∧ dC U n σ = 0 ∧ x = cls σ}

abbrev Hd (X : Sch K) (a n : ℕ) : Submodule K (H X n) := deg (all X) a n

structure IsCov (U : ι → X.left.Opens) : Prop where
  aff : ∀ i, IsAffineOpen (U i)
  cov : iSup U = ⊤

def down {U : ι → X.left.Opens} (hU : IsCov U) {n : ℕ} (x : H X n) : HC U n :=
  pullHC (𝟙 X) (U := all X) (V := U) (fun i => (⟨U i, hU.aff i⟩ : X.left.affineOpens)) (fun _ _ hx => hx) x

def up {U : ι → X.left.Opens} (hU : IsCov U) {n : ℕ} (y : HC U n) : H X n := Function.invFun (down hU) y

def Pr (f : Y ⟶ X) : Type := {p : Y.left.affineOpens × X.left.affineOpens // p.1.1 ≤ f.left ⁻¹ᵁ p.2.1}

theorem isCov_pr (f : Y ⟶ X) : IsCov fun p : Pr f => p.1.1.1 where
  aff p := p.1.1.2
  cov := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.left y)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hy', hVU⟩ := Y.left.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ (f.left ⁻¹ᵁ U : Y.left.Opens) from hy) (f.left ⁻¹ᵁ U).2
    exact Opens.mem_iSup.2 ⟨⟨(⟨V, hV⟩, ⟨U, hU⟩), hVU⟩, hy'⟩

def pull (f : Y ⟶ X) {n : ℕ} (x : H X n) : H Y n := up (isCov_pr f) (pullHC f (fun p : Pr f => p.1.2) (fun p => p.2) x)

abbrev cup {a b n : ℕ} (h : a + b = n) (x : H X a) (y : H X b) : H X n := cupH h x y

def one (X : Sch K) : H X 0 := cls fun _ => 1

structure Coc (X : Sch K) : Type 1 where
  ι : Type
  U : ι → X.left.Opens
  cov : IsCov U
  g : ∀ i : Fin 2 → ι, (Sec X (cap U i))ˣ
  coc : ∀ i : Fin 3 → ι,
    secRes X (inter_le_comp (X := X.left.toTopCat) U i (Fin.succAbove 2)) (g (i ∘ Fin.succAbove 2)).val *
      secRes X (inter_le_comp (X := X.left.toTopCat) U i (Fin.succAbove 0)) (g (i ∘ Fin.succAbove 0)).val =
      secRes X (inter_le_comp (X := X.left.toTopCat) U i (Fin.succAbove 1)) (g (i ∘ Fin.succAbove 1)).val

def c1 (L : Coc X) : H X 1 := up L.cov (cls fun i => dlog K (L.g i))

def Coc.triv (X : Sch K) : Coc X where
  ι := X.left.affineOpens
  U := all X
  cov := ⟨fun i => i.2, iSup_affineOpens_eq_top _⟩
  g _ := 1
  coc _ := by simp only [Units.val_one, map_one, mul_one]

end UpperTheory.Gal.DifferentialFormSections
