import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

open Module

theorem linearIndependent_span_of_toMatrix {S M C A : Type} [CommRing S] [AddCommGroup M] [Module S M]
    [Fintype C] [DecidableEq C] [Fintype A] [DecidableEq A] (e : Basis C S M) (w : A → M)
    (Q : Matrix A C S) (h₁ : e.toMatrix w * Q = 1) (h₂ : Q * e.toMatrix w = 1) :
    LinearIndependent S w ∧ Submodule.span S (Set.range w) = ⊤ := by
  let L : (A → S) ≃ₗ[S] (C → S) := LinearEquiv.ofLinearMap (Matrix.toLin' (e.toMatrix w)) (Matrix.toLin' Q)
    (by rw [← Matrix.toLin'_mul, h₁, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h₂, Matrix.toLin'_one])
  let b : Basis A S M := (Pi.basisFun S A).map (L ≪≫ₗ e.equivFun.symm)
  have hb : ⇑b = w := by
    funext i
    apply e.equivFun.injective
    ext a
    simp [b, L, Basis.toMatrix_apply, Matrix.toLin'_apply]
  exact ⟨hb ▸ b.linearIndependent, hb ▸ b.span_eq⟩

def pairBasis (R : Type) [CommRing R] (d : ℕ) : Basis (Fin d ⊕ Fin d) R ((Fin d → R) × (Fin d → R)) :=
  (Pi.basisFun R (Fin d)).prod (Pi.basisFun R (Fin d))

theorem pairBasis_repr_vmap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (y : (Fin d → R) × (Fin d → R)) (a : Fin d ⊕ Fin d) :
    (pairBasis S d).repr (vmap f y) a = f ((pairBasis R d).repr y a) := by
  cases a <;> simp [pairBasis, vmap]

theorem linearIndependent_span_vmap {R S A : Type} [CommRing R] [CommRing S] [Fintype A] (f : R →+* S) {d : ℕ}
    (v : A → (Fin d → R) × (Fin d → R)) (hli : LinearIndependent R v)
    (hsp : Submodule.span R (Set.range v) = ⊤) :
    LinearIndependent S (fun i => vmap f (v i)) ∧
      Submodule.span S (Set.range fun i => vmap f (v i)) = ⊤ := by
  classical
  let b : Basis A R ((Fin d → R) × (Fin d → R)) := Basis.mk hli hsp.ge
  have hb : ⇑b = v := Basis.coe_mk hli hsp.ge
  have hP : (pairBasis S d).toMatrix (fun i => vmap f (v i)) = ((pairBasis R d).toMatrix v).map f := by
    ext a i
    simp [Basis.toMatrix_apply, pairBasis_repr_vmap]
  have h₁ : (pairBasis R d).toMatrix v * b.toMatrix (pairBasis R d) = 1 := by
    rw [← hb]; exact Basis.toMatrix_mul_toMatrix_flip _ _
  have h₂ : b.toMatrix (pairBasis R d) * (pairBasis R d).toMatrix v = 1 := by
    rw [← hb]; exact Basis.toMatrix_mul_toMatrix_flip _ _
  refine linearIndependent_span_of_toMatrix (pairBasis S d) _ ((b.toMatrix (pairBasis R d)).map f) ?_ ?_
  · rw [hP, ← Matrix.map_mul, h₁, Matrix.map_one _ f.map_zero f.map_one]
  · rw [hP, ← Matrix.map_mul, h₂, Matrix.map_one _ f.map_zero f.map_one]

theorem isHBasis_map : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (R S : Type) [CommRing R]
    [Nontrivial R] [CommRing S] (f : R →+* S) (d r : ℕ) (B : Germ.FB R d (𝓞 E)) (B₂ : Germ.FB S d (𝓞 E))
    (x : Fin r → (Fin d → R) × (Fin d → R)), IsMapOf f B B₂ → IsHBasis B x →
      IsHBasis B₂ (fun j => vmap f (x j)) := by
  intro E _ _ _ R S _ _ _ f d r B B₂ x h hx
  have key := linearIndependent_span_vmap f _ hx.1 hx.2
  have he : (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B₂ (RingOfIntegers.basis E q.2) (vmap f (x q.1))) =
      fun q => vmap f (rhoH B (RingOfIntegers.basis E q.2) (x q.1)) :=
    funext fun q => (vmap_rhoH h _ _).symm
  unfold IsHBasis
  rw [he]
  exact key

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ
