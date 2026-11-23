import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleModelActionPolarization
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
theorem _root_.GlobalTheory.T.p_divisible_model_action_polarization : ∀ (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (G₀ : Over (Sp K)) [GrpObj G₀] [IsCommMonObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (spMap (algebraMap R K)) F → ∀ (GG : PDivGroup p R) (θ : TorsionMap G GG), IsModel K θ → ∀ (GG₀ : PDivGroup p K) (θ₀ : TorsionMap G₀ GG₀) (e : GG₀ ≅ GG.baseChange K), GenCompat F θ θ₀ e → (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra K B], Function.Bijective (θ₀.pt n B)) → ∀ (f : G ⟶ G) (f₀ : G₀ ⟶ G₀) [IsMonHom f₀] (g : GG ⟶ GG) (g₀ : GG₀ ⟶ GG₀), f₀.left ≫ F = F ≫ f.left → θ.Intertwines f g → θ₀.Intertwines f₀ g₀ → g₀ ≫ e.hom = e.hom ≫ PDivGroup.baseChangeMap K g := by
  first | exact @GlobalTheory.GroupBplus.Aff.induced_endo_compat | exact GlobalTheory.GroupBplus.Aff.induced_endo_compat | (intros; apply GlobalTheory.GroupBplus.Aff.induced_endo_compat <;> assumption)
