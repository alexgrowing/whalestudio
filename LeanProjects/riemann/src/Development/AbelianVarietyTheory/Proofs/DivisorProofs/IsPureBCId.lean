import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PureLift

def IsPure {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (W : A ⟶ A) [IsMonHom W] (r s : R) : Prop :=
  (∀ x ∈ Fil A, push (dp0 R) (𝟙 _) W x = r • x) ∧ ∀ y : HdR A, push (dp0 R) (𝟙 _) W y - s • y ∈ Fil A

def IsPureBC {S : Type} [CommRing S] (G : Over (Sp S)) [GrpObj G] (W : G ⟶ G) (r s : S) : Prop :=
  ∀ (R : Type) [CommRing R] (f : S →+* R) (A : Over (Sp R)) [GrpObj A] (φ : A.left ⟶ G.left),
    IsGrpPullback A G (spMap f) φ → ∀ (W' : A ⟶ A) [IsMonHom W'], W'.left ≫ φ = φ ≫ W.left → IsPure A W' (f r) (f s)

theorem IsPure.mem_Fil {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {W : A ⟶ A} [IsMonHom W] {r r' s : R}
    (h : IsPure A W r' s) (hu : IsUnit (r - s)) {y : HdR A} (hy : push (dp0 R) (𝟙 _) W y = r • y) : y ∈ Fil A := by
  have hm := h.2 y
  rw [hy, ← sub_smul] at hm
  obtain ⟨u, hu'⟩ := hu
  have hv := (Fil A).smul_mem (↑u⁻¹ : R) hm
  rwa [smul_smul, ← hu', Units.inv_mul, one_smul] at hv

end GlobalTheory.PureLift
