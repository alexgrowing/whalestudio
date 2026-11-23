import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelConjugateEmbedding
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
theorem _root_.GlobalTheory.T.integral_model_conjugate_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (τ : E →+* ℂ) (A : Type) [CommRing A] [IsDomain A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ) → Fin g → A) (U₂ h₂ : Fin (Dw.mult (conjEmb τ)) → Fin g → A), IsTanBasis Y.t ξ e → (∀ (S : Type) [CommRing S] (φ : A →+* S), EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧ EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) → IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) → ∀ (T : CDVR) (α : A →+* T.V) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (yy : Sp T.Fr ⟶ Xo'.XF c'), yy ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp α) ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) → ∃ (w₁ : Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left)) (w₂ : Fin (Dw.mult (conjEmb τ)) → (Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left)) (g₁ : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.Fr) (g₂ : Matrix (Fin (Dw.mult (conjEmb τ))) (Fin (Dw.mult (conjEmb τ))) T.Fr), (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t ((algebraMap T.V T.Fr).comp α) e) (fun b => (algebraMap T.V T.Fr).comp α (U₁ i b)) (w₁ i ≫ Y.m.φ)) ∧ (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t ((algebraMap T.V T.Fr).comp α) e) (fun b => (algebraMap T.V T.Fr).comp α (U₂ i b)) (w₂ i ≫ Y.m.φ)) ∧ (letI := io.toAlgebra; (∀ i, IsCombAt y₀.1.x (y₀.1.u τ) (g₁ i) (w₁ i ≫ ν.φ)) ∧ (∀ i, IsCombAt y₀.1.x (y₀.1.u (conjEmb τ)) (g₂ i) (w₂ i ≫ ν.φ))) ∧ (∃ u : T.Vˣ, algebraMap T.V T.Fr u = g₁.det) ∧ ∃ u : T.Vˣ, algebraMap T.V T.Fr u = g₂.det := by
  first | exact @GlobalTheory.FlatModel.frames_changeOfBasis_det_isUnit | exact GlobalTheory.FlatModel.frames_changeOfBasis_det_isUnit | (intros; apply GlobalTheory.FlatModel.frames_changeOfBasis_det_isUnit <;> assumption)
