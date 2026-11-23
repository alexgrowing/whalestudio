import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPointOverInclusionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingSectionCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisMapCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePointTangentMatricesStatement

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.FrameLoc

theorem exists_frPt_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (τ : Psi H) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∀ (L : Type) [CommRing L] [IsLocalRing L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∃ (_ : Algebra c.F L) (z : FrPt Xo c L) (w₁ : Fin (Dw.mult τ.1) → (Sp (DualNumber L) ⟶ Y.oF.t.G.left))
      (w₂ : Fin (Dw.mult (conjEmb τ.1)) → (Sp (DualNumber L) ⟶ Y.oF.t.G.left)),
      ptF z = yL ≫ r ∧
      (∀ i, IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) (fun b => io (U₁ i b)) (w₁ i ≫ Y.m.φ)) ∧
      (∀ i, IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) (fun b => io (U₂ i b)) (w₂ i ≫ Y.m.φ)) ∧
      (∀ i, z.u τ.1 i = w₁ i ≫ ν.φ) ∧ ∀ i, z.u (conjEmb τ.1) i = w₂ i ≫ ν.φ := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hov τ A _ ξ β hβ g e U₁ h₁ U₂ h₂ he heig hu₁ hu₂ L _ _ io yL hyL
  obtain ⟨alg, hs, hpt, hemb⟩ := GlobalTheory.T.integral_model_point_over_inclusion E H Dw l l' Xo Xo' c c' W Y r hle hov A ξ β hβ L io yL hyL
  letI := alg
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.FlagTan.exists_frPt (yL ≫ r ≫ pullback.fst _ _) hs
  choose w₁ hc₁ ht₁ using fun i => GlobalTheory.T.tangent_basis_generic_point E H Dw l' Xo' c' W Y A ξ g e he L io yL hyL (fun b => io (U₁ i b))
  choose w₂ hc₂ ht₂ using fun i => GlobalTheory.T.tangent_basis_generic_point E H Dw l' Xo' c' W Y A ξ g e he L io yL hyL (fun b => io (U₂ i b))
  have hE₁ := (heig L io).1
  have hE₂ := (heig L io).2
  rw [← hyL] at hE₁ hE₂
  have hp₁ := fun i => GlobalTheory.T.embedding_section_compatibility E H Dw l l' Xo Xo' c c' W Y r ν L yL τ.1
    (io.comp (β.comp (embV c' W τ.1))) (fun a => hemb _ a) (w₁ i) (ht₁ i) (hE₁ i _ (hc₁ i))
  have hp₂ := fun i => GlobalTheory.T.embedding_section_compatibility E H Dw l l' Xo Xo' c c' W Y r ν L yL (conjEmb τ.1)
    (io.comp (β.comp (embV c' W (conjEmb τ.1)))) (fun a => hemb _ a) (w₂ i) (ht₂ i) (hE₂ i _ (hc₂ i))
  obtain ⟨g₁, hg₁, hcg₁⟩ := GlobalTheory.T.tangent_basis_map_compatible E H Dw l l' Xo Xo' c c' W Y r ν A ξ g e he τ.1 U₁ h₁ hu₁ L io yL hyL z₀ hz₀
    w₁ hc₁ ht₁ fun i => (hp₁ i).2
  obtain ⟨g₂, hg₂, hcg₂⟩ := GlobalTheory.T.tangent_basis_map_compatible E H Dw l l' Xo Xo' c c' W Y r ν A ξ g e he (conjEmb τ.1) U₂ h₂ hu₂ L io yL hyL z₀ hz₀
    w₂ hc₂ ht₂ fun i => (hp₂ i).2
  obtain ⟨z, hzx, hz₁, hz₂⟩ := GlobalTheory.T.frame_point_tangent_matrices E H Dw l Xo c L z₀ τ g₁ g₂ (fun i => w₁ i ≫ ν.φ) (fun i => w₂ i ≫ ν.φ)
    hg₁ hg₂ hcg₁ hcg₂
  exact ⟨alg, z, w₁, w₂, hpt z (hzx.trans hz₀), hc₁, hc₂, hz₁, hz₂⟩

end GlobalTheory.FlatModel.FrameLoc
