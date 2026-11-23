import Development.EtaleCohomology.EtaleSheaves.ChartsGeomVpaPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.StdChartsProof
  LateralTheory.E.ChartsGeom_vpaPf

namespace LateralTheory.E.GeometricData

def rA {A : Type} [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (W : Z.Opens) : A →+* Γ(Z, W) :=
  (p.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

def NonDeg {A : Type} [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) : Prop :=
  ∃ (U V : Z.Opens) (s : Γ(Z, U)) (s' : Γ(Z, V)), IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ ∧
    Z.basicOpen s = U ⊓ V ∧ Z.basicOpen s' = U ⊓ V ∧ ((U ⊓ V : Z.Opens) : Set Z).Nonempty ∧
    Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s *
      Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s' = 1 ∧
    (Polynomial.eval₂RingHom (rA p U) s).IsIntegral ∧ (Polynomial.eval₂RingHom (rA p V) s').IsIntegral

def Concl {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Algebra A K) (B C : Subalgebra A K) (t : K), Charts B C t ∧
    (∀ x ∈ B, x ∈ C → IsIntegral A x) ∧ ChartData p B C t

def TopInt : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → (rA p ⊤).IsIntegral

def LineOpens : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z → IsAffineOpen (⊤ : Z.Opens) ∨ NonDeg p

def EmbedNonDeg : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IsIntegral Z → (rA p ⊤).IsIntegral → NonDeg p → Concl p

def EmbedAffine : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IsIntegral Z → (rA p ⊤).IsIntegral → IsAffineOpen (⊤ : Z.Opens) → Concl p

theorem GeoData_of (hT : TopInt) (hL : LineOpens) (hN : EmbedNonDeg) (hE : EmbedAffine) : GeoData := by
  intro A _ _ Z p hIL hZ
  have hI : IsIntegral Z := hZ.1
  have hTop := hT A p hIL
  rcases hL A p hIL hZ with h | h
  · exact hE A p hI hTop h
  · exact hN A p hI hTop h

end LateralTheory.E.GeometricData
