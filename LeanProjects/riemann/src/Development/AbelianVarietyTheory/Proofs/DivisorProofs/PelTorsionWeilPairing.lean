import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
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

theorem cubWeil_eq_polPairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (t₀ : SAB H (Sp K)) (GG₀ : PDivGroup p K) (act₀ : Action (𝓞 E) GG₀) (pol₀ : GG₀ ≅ GG₀.dual) (θ₀ : TorsionMap t₀.G GG₀) (ε₀ : (PDivGroup.mu p K).Tate) (τ₀ : Dw.La →+ GG₀.Tate), IsOfType Dw t₀ → IsPropG Dw t₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ → ∀ (n : ℕ) (x x' : Tors t₀.G (p ^ n) K) (y : Dw.La) (ζ : Kˣ), θ₀.pt n K x' = tatePt (τ₀ y) n K → GlobalTheory.UU.CubWeil t₀.cub (p ^ n) x.1 x'.1 (unitOn ζ) → (ζ : K) = θ₀.pt n K x (charElem (tateMap GG₀ GG₀.dual K pol₀.hom (τ₀ y)) n) := by
  intro E _ _ _ H Dw p _ K _ _ _ t₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ hT hP n x x' y ζ hx' hc
  have hpp : p.Prime := Fact.out
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  have hpr : IsProper t₀.G.hom := hT.1
  have hab : Set.range (spMap (algebraMap K K)) ⊆ abLocus t₀.G := fun _ _ _ _ _ _ _ => inferInstance
  have hv : (θ₀.pt n K x (charElem (tateMap GG₀ GG₀.dual K pol₀.hom (τ₀ y)) n)) ^ p ^ n = 1 := by
    rw [← map_pow, charElem_pow_self, map_one]
  let u : Kˣ := Units.ofPowEqOne _ (p ^ n) hv (pow_ne_zero _ hpp.ne_zero)
  have hw := hP.weil n K hp hab x x' y u hx' rfl
  have hA : IsAbelianScheme t₀.G := ⟨t₀.semi.comm, t₀.semi.smooth, hpr, t₀.semi.geomConnected⟩
  have hw' := (GlobalTheory.UU.cubWeil_iff_weilIs GlobalTheory.SemiRigid.globalFns hA hc.1 hc.2.1 _).1 hc
  have e := GlobalTheory.weilIs_unique_fieldPoint (Sp K) t₀.G t₀.PP.L t₀.PP.isLB K (spMap (algebraMap K K)) _ x.1 x'.1 u ζ hw hw'
  rw [← e]
  rfl

end GlobalTheory.GroupBplus.Aff
