import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentLiftCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelEmbeddingFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelEmbeddingSecondStatement

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem frames_changeOfBasis_det_isUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (τ : E →+* ℂ) (A : Type) [CommRing A] [IsDomain A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ) → Fin g → A) (U₂ h₂ : Fin (Dw.mult (conjEmb τ)) → Fin g → A), IsTanBasis Y.t ξ e → (∀ (S : Type) [CommRing S] (φ : A →+* S), EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧ EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) → IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) → ∀ (T : CDVR) (α : A →+* T.V) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (yy : Sp T.Fr ⟶ Xo'.XF c'), yy ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp α) ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) → ∃ (w₁ : Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left)) (w₂ : Fin (Dw.mult (conjEmb τ)) → (Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left)) (g₁ : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.Fr) (g₂ : Matrix (Fin (Dw.mult (conjEmb τ))) (Fin (Dw.mult (conjEmb τ))) T.Fr), (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t ((algebraMap T.V T.Fr).comp α) e) (fun b => (algebraMap T.V T.Fr).comp α (U₁ i b)) (w₁ i ≫ Y.m.φ)) ∧ (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t ((algebraMap T.V T.Fr).comp α) e) (fun b => (algebraMap T.V T.Fr).comp α (U₂ i b)) (w₂ i ≫ Y.m.φ)) ∧ (letI := io.toAlgebra; (∀ i, IsCombAt y₀.1.x (y₀.1.u τ) (g₁ i) (w₁ i ≫ ν.φ)) ∧ (∀ i, IsCombAt y₀.1.x (y₀.1.u (conjEmb τ)) (g₂ i) (w₂ i ≫ ν.φ))) ∧ (∃ u : T.Vˣ, algebraMap T.V T.Fr u = g₁.det) ∧ ∃ u : T.Vˣ, algebraMap T.V T.Fr u = g₂.det := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hOI τ A _ _ ξ β hξ g e U₁ h₁ U₂ h₂ he hU hP₁ hP₂ T α io y₀ yy hyy hpt
  letI := io.toAlgebra
  set φ₀ : A →+* T.Fr := (algebraMap T.V T.Fr).comp α with hφ₀
  have hbc := isTanBasis_bc he φ₀
  have htan : ∀ i, IsTanAtG Y.t (yy ≫ Y.j) (bcV Y.t φ₀ e i) := fun i => hyy ▸ hbc.1 i
  choose w₁ hw₁ using fun i : Fin (Dw.mult τ) =>
    GlobalTheory.T.exists_tangent_lift_coefficients E H Dw l' Xo' c' W Y T.Fr yy g (bcV Y.t φ₀ e) htan (fun b => φ₀ (U₁ i b))
  choose w₂ hw₂ using fun i : Fin (Dw.mult (conjEmb τ)) =>
    GlobalTheory.T.exists_tangent_lift_coefficients E H Dw l' Xo' c' W Y T.Fr yy g (bcV Y.t φ₀ e) htan (fun b => φ₀ (U₂ i b))
  have hE₁ := fun i => GlobalTheory.T.integral_model_embedding_first E H Dw l l' Xo Xo' c c' W Y r ν hle hOI τ A ξ β hξ g (Dw.mult τ) e U₁ he
    (fun S _ φ => (hU S φ).1) T.Fr φ₀ io y₀.1 yy hyy hpt i (w₁ i) (hw₁ i)
  have hE₂ := fun i => GlobalTheory.T.integral_model_embedding_first E H Dw l l' Xo Xo' c c' W Y r ν hle hOI (conjEmb τ) A ξ β hξ g (Dw.mult (conjEmb τ)) e U₂ he
    (fun S _ φ => (hU S φ).2) T.Fr φ₀ io y₀.1 yy hyy hpt i (w₂ i) (hw₂ i)
  choose g₁ hg₁ using fun i => (y₀.1.basis τ (w₁ i ≫ ν.φ) (hE₁ i).1 (hE₁ i).2).exists
  choose g₂ hg₂ using fun i => (y₀.1.basis (conjEmb τ) (w₂ i ≫ ν.φ) (hE₂ i).1 (hE₂ i).2).exists
  refine ⟨w₁, w₂, Matrix.of g₁, Matrix.of g₂, hw₁, hw₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
  · exact GlobalTheory.T.integral_model_embedding_second E H Dw l l' Xo Xo' c c' W Y r ν hle hOI τ A ξ β hξ g e U₁ h₁ he (fun S _ φ => (hU S φ).1) hP₁ T α io y₀ yy hyy hpt
      w₁ (Matrix.of g₁) hw₁ hg₁
  · exact GlobalTheory.T.integral_model_embedding_second E H Dw l l' Xo Xo' c c' W Y r ν hle hOI (conjEmb τ) A ξ β hξ g e U₂ h₂ he (fun S _ φ => (hU S φ).2) hP₂ T α io y₀ yy
      hyy hpt w₂ (Matrix.of g₂) hw₂ hg₂

end GlobalTheory.FlatModel
