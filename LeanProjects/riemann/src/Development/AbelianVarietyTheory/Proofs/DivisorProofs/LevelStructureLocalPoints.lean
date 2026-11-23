import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteHopfPointsSeparateStatement
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

attribute [local instance] GlobalTheory.HopfShear.pointsGroup

theorem range_spMap_subset_of_residue {A B : Type} [CommRing A] [CommRing B] [IsLocalRing B] (ψ : A →+* B)
    (V : (Sp A).Opens) (h : Set.range (spMap ((IsLocalRing.residue B).comp ψ)) ⊆ V) : Set.range (spMap ψ) ⊆ V := by
  rintro _ ⟨x, rfl⟩
  have h1 : spMap ψ (IsLocalRing.closedPoint B) ∈ V := by
    have h2 := h ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField B), rfl⟩
    have e : spMap ((IsLocalRing.residue B).comp ψ) (IsLocalRing.closedPoint (IsLocalRing.ResidueField B)) =
        spMap ψ (IsLocalRing.closedPoint B) :=
      congrArg (PrimeSpectrum.comap ψ) (IsLocalRing.comap_closedPoint (IsLocalRing.residue B))
    exact e ▸ h2
  have hs : x ⤳ IsLocalRing.closedPoint B := IsLocalRing.specializes_closedPoint x
  exact (hs.map (spMap ψ).continuous).mem_open V.isOpen h1

theorem level_point_eq_tors_mul_section : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (θ : TorsPt G N A), IsLevel K θ → ∀ (B : Type) [CommRing B] [Algebra R B] [IsLocalRing B] (φ : A →ₐ[R] B), ∃ (z : Tors G N B) (s : A →ₐ[R] R), toConv φ = toConv (θ.pt B z) * toConv ((Algebra.ofId R B).comp s) := by
  intro R K _ _ _ _ _ _ _ _ G _ _ _ N _ A _ _ _ _ _ θ hθ B _ _ _ φ
  obtain ⟨hfin, hsep, -⟩ := GlobalTheory.T.finite_hopf_points_separate R K A
  obtain ⟨V, hV⟩ := hθ.opn
  let k := IsLocalRing.ResidueField B
  let π : B →ₐ[R] k := IsScalarTower.toAlgHom R B k
  obtain ⟨s, hs⟩ := GlobalTheory.finiteAlg_fieldPoint_factors_through_base R K A hsep k (π.comp φ)
  let ψ : WithConv (A →ₐ[R] B) := toConv φ * (toConv ((Algebra.ofId R B).comp s))⁻¹
  have h1 : GlobalTheory.HopfShear.post π ψ = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
    show toConv (π.comp φ) = toConv (π.comp ((Algebra.ofId R B).comp s))
    rw [hs, ← AlgHom.comp_assoc, Subsingleton.elim (π.comp (Algebra.ofId R B)) (Algebra.ofId R k)]
  have h2 : toConv (θ.pt k 1) = 1 := by
    have := θ.mul k 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.mp this
  have h3 : π.comp ψ.ofConv = θ.pt k 1 := WithConv.toConv_injective (h1.trans h2.symm)
  have h4 := (hV k).mapsTo (Set.mem_univ 1)
  rw [← h3] at h4
  obtain ⟨z, -, hz⟩ := (hV B).surjOn (range_spMap_subset_of_residue (ψ.ofConv : A →+* B) V h4)
  refine ⟨z, s, ?_⟩
  rw [hz]
  show toConv φ = ψ * _
  rw [inv_mul_cancel_right]

end GlobalTheory.GroupBplus.Aff
