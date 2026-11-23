import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelDomainOverInclusion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_domain_over_inclusion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (A : Type) [CommRing A] [IsDomain A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → (∀ a : c'.V W, a ≠ 0 → IsUnit (β a)) → ∀ (T₀ : CDVR) (α : A →+* T₀.V), Function.Injective α → ∀ yy₀ : Sp T₀.Fr ⟶ Xo'.XF c', yy₀ ≫ Y.j = spMap ((algebraMap T₀.V T₀.Fr).comp α) ≫ ξ → ∃ (T : CDVR) (i : T₀.V →+* T.V) (iF : T₀.Fr →+* T.Fr), (∀ a, algebraMap T.V T.Fr (i a) = iF (algebraMap T₀.V T₀.Fr a)) ∧ Function.Injective i ∧ IsLocalHom i ∧ ∃ (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) ∧ (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = spMap iF ≫ yy₀ ≫ r) := by
  first | exact @GlobalTheory.ModelIntFr.exists_intFr_of_modelPt | exact GlobalTheory.ModelIntFr.exists_intFr_of_modelPt | (intros; apply GlobalTheory.ModelIntFr.exists_intFr_of_modelPt <;> assumption)
