import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

noncomputable section

namespace GlobalTheory.DrinLev

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}}

structure FreeChart (Z : Over S) where

  R : Type
  [ringR : CommRing R]

  t : Sp R ⟶ S

  B : Type
  [ringB : CommRing B]
  [alg : Algebra R B]
  [free : Module.Free R B]
  [fin : Module.Finite R B]

  e : Sp B ≅ pullback Z.hom t

  e_snd : e.hom ≫ pullback.snd Z.hom t = spMap (algebraMap R B)

attribute [instance] FreeChart.ringR FreeChart.ringB FreeChart.alg FreeChart.free FreeChart.fin

def FreeChart.ev {Z : Over S} (c : FreeChart Z) (P : 𝟙_ (Over S) ⟶ Z) : c.B →+* c.R :=
  (Spec.preimage (pullback.lift (c.t ≫ P.left) (𝟙 _)
    (by rw [Category.assoc, Over.w P]; rfl) ≫ c.e.inv)).hom

def IsFinLocFree (Z : Over S) (N : ℕ) : Prop :=
  ∀ x : S, ∃ c : FreeChart Z, IsOpenImmersion c.t ∧ x ∈ Set.range c.t ∧ Module.finrank c.R c.B = N

def IsFullSet (Z : Over S) {J : Type} (P : J → (𝟙_ (Over S) ⟶ Z)) : Prop :=
  Finite J ∧ IsFinLocFree Z (Nat.card J) ∧
    ∀ (c : FreeChart Z) (f : c.B), Algebra.norm c.R f = ∏ᶠ i, c.ev (P i) f

variable {O : Type} [CommRing O]

structure DrinfeldLevel {G : Over S} [GrpObj G] [IsCommMonObj G] (a : OAct O G) (ϖ : O) (h m : ℕ) where

  α : (Fin h → O ⧸ Ideal.span {ϖ ^ m}) → (𝟙_ (Over S) ⟶ G)
  map_add : ∀ x y, α (x + y) = α x * α y
  map_smul : ∀ (c : O) x, α (c • x) = α x ≫ a.act c
  full : IsFullSet G α

end GlobalTheory.DrinLev

namespace GlobalTheory.DrinLev
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

def FreeChart.self (R : Type) [CommRing R] : FreeChart (Over.mk (𝟙 (Sp R))) where
  R := R
  t := 𝟙 _
  B := R
  e := (asIso (pullback.snd (𝟙 (Sp R)) (𝟙 (Sp R)))).symm
  e_snd := by
    simp only [Iso.symm_hom, asIso_inv, IsIso.inv_hom_id, Over.mk_hom]
    simp [spMap, Algebra.algebraMap_self]

example (R : Type) [CommRing R] [Nontrivial R] :
    Module.finrank (FreeChart.self R).R (FreeChart.self R).B = 1 :=
  Module.finrank_self R

example (R : Type) [CommRing R] : IsFinLocFree (Over.mk (𝟙 (Sp R))) 1 := by
  intro x
  have : Nontrivial R := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact (PrimeSpectrum.isEmpty_iff_subsingleton.mpr h).false x
  exact ⟨FreeChart.self R, inferInstanceAs (IsOpenImmersion (𝟙 _)), ⟨x, rfl⟩, Module.finrank_self R⟩

end GlobalTheory.DrinLev
