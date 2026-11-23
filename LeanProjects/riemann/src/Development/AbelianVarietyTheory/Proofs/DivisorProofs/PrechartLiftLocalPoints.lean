import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem exists_chart_of_residue : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ) (q : PrimeSpectrum R) (c : PreChart G N q) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (x : Tors G N B), Set.range (torsMap (IsScalarTower.toAlgHom R B (IsLocalRing.ResidueField B)) x).1.left ⊆ c.W → ∃ ψ : c.C →ₐ[R] B, torsMap ψ c.j = x := by
  intro R _ G _ _ N q c B _ _ _ x h
  have hx : Set.range x.1.left ⊆ c.W := by
    rintro _ ⟨y, rfl⟩
    have h1 : x.1.left (IsLocalRing.closedPoint B) ∈ c.W := by
      have h2 := h ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField B), rfl⟩
      have h3 : (spOver (IsScalarTower.toAlgHom R B (IsLocalRing.ResidueField B))).left
          (IsLocalRing.closedPoint (IsLocalRing.ResidueField B)) = IsLocalRing.closedPoint B :=
        IsLocalRing.comap_closedPoint (IsLocalRing.residue B)
      rw [← h3]
      exact h2
    have h4 : x.1.left y ⤳ x.1.left (IsLocalRing.closedPoint B) :=
      (IsLocalRing.specializes_closedPoint y).map x.1.left.continuous
    exact h4.mem_open c.W.isOpen h1
  obtain ⟨ψ, -, hψ⟩ := (c.bij B).surjOn hx
  exact ⟨ψ, hψ⟩

end GlobalTheory.GroupBplus.Aff
