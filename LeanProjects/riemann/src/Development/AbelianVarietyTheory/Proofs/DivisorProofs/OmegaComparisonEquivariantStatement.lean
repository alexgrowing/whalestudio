import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaComparisonEquivariant
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omega_comparison_equivariant : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (GG : PDivGroup p R) (θ : TorsionMap A GG) (c : Pdiv.omega A →ₗ[R] GG.omega), θ.IsOmega c → ∀ (f : A ⟶ A) (g : GG ⟶ GG), IsMonHom f → θ.Intertwines f g → ∀ w w' : Pdiv.omega A, (∀ x x' : Pdiv.LieG A, x'.1 = x.1 ≫ f → w'.1 x = w.1 x') → c w' = omegaMap GG GG g (c w) := by
  first | exact @GlobalTheory.GroupBplus.Aff.omega_pullback_intertwines | exact GlobalTheory.GroupBplus.Aff.omega_pullback_intertwines | (intros; apply GlobalTheory.GroupBplus.Aff.omega_pullback_intertwines <;> assumption)
