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

theorem tors_point_range_fld : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ) (B : Type) [CommRing B] [Algebra R B] (z : Tors G N B) (P : PrimeSpectrum B), z.1.left P ∈ Set.range (torsMap (IsScalarTower.toAlgHom R B (FractionRing (B ⧸ P.asIdeal))) z).1.left := by
  intro R _ G _ _ N B _ _ z P
  let k := FractionRing (B ⧸ P.asIdeal)
  let x : Sp k := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  refine ⟨x, ?_⟩
  rw [torsMap_val, Over.comp_left]
  rw [Scheme.Hom.comp_apply]
  congr 1
  apply PrimeSpectrum.ext
  ext a
  change algebraMap B k a ∈ (⊥ : Ideal k) ↔ a ∈ P.asIdeal
  rw [Ideal.mem_bot, IsScalarTower.algebraMap_apply B (B ⧸ P.asIdeal) k,
    IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.GroupBplus.Aff
