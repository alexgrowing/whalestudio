import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelPDivisibleExtensionTate
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
theorem _root_.GlobalTheory.T.pel_p_divisible_extension_tate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (t : SAB H (Sp R)) (t₀ : SAB H (Sp K)) (mK : SABMap t₀ t (spMap (algebraMap R K))) (GG₀ : PDivGroup p K) (act₀ : Action (𝓞 E) GG₀) (pol₀ : GG₀ ≅ GG₀.dual) (θ₀ : TorsionMap t₀.G GG₀) (ε₀ : (PDivGroup.mu p K).Tate) (τ₀ : Dw.La →+ GG₀.Tate), IsOfType Dw t₀ → IsPropG Dw t₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ → ∀ (GG : PDivGroup p R) (θ : TorsionMap t.G GG) (e : GG₀ ≅ GG.baseChange K), IsModel K θ → GenCompat mK.φ θ θ₀ e → ∀ φ : GG ⟶ GG.dual, pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom = e.hom ≫ PDivGroup.baseChangeMap K φ → ∀ τ : Dw.La →+ GG.Tate, (∀ x, tateMap _ _ K e.hom (τ₀ x) = bcTate K (τ x)) → ∀ (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [Algebra R k], (p : k) ≠ 0 → Set.range (spMap (algebraMap R k)) ⊆ abLocus t.G → ∀ (x x' : Tors t.G (p ^ n) k) (y : Dw.La) (u : kˣ), θ.pt n k x' = tatePt (τ y) n k → (u : k) = θ.pt n k x (charElem (tateMap GG GG.dual R φ (τ y)) n) → Out.WeilIs t.G t.PP.L ((p ^ n : ℕ) : ℤ) x.1 x'.1 (unitOn u) := by
  first | exact @GlobalTheory.GroupBplus.Aff.weilIs_model_pol | exact GlobalTheory.GroupBplus.Aff.weilIs_model_pol | (intros; apply GlobalTheory.GroupBplus.Aff.weilIs_model_pol <;> assumption)
