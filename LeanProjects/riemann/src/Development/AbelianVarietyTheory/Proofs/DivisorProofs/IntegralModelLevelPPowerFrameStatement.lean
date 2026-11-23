import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelLevelPPowerFrame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_level_p_power_frame : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ n : ℕ,
    ∀ (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → l'.A = p ^ n →
    ∀ (N : ℕ) (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c'.V W), LatData Dw (embV c' W (conjEmb τ.1)) a T S →
    ∀ [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∃ (ta : Fin N → P.T) (w₁ : Fin (Dw.mult τ.1) → P.V) (w₂ : Fin (Dw.mult (conjEmb τ.1)) → P.V)
        (σ : Equiv.Perm (Ind Dw τ.1)),
        (∀ m, ((ta m).lev n).left ≫ ψ = yy ≫ (Y.oF.etaA (a m)).left) ∧
        (∀ k, w₁ k ∈ htLat c P τ.1 ∧ w₁ k ∈ Submodule.span ℂ_[p] (Set.range P.bLie) ∧
          w₁ k ∈ P.eigV (embInt c P.integers τ.1)) ∧
        (∀ k, w₂ k ∈ htLat c P (conjEmb τ.1) ∧ w₂ k ∈ Submodule.span ℂ_[p] (Set.range P.bLie) ∧
          w₂ k ∈ P.eigV (embInt c P.integers (conjEmb τ.1))) ∧
        ‖(Matrix.of fun k k' => P.pairV (w₁ k) (∑ m, (β (T (σ (Sum.inl k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m)).det‖ = 1 ∧
        ‖(Matrix.of fun k k' => P.pairV (w₂ k) (∑ m, (β (S (σ (Sum.inr k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m)).det‖ = 1 := by
  first | exact @GlobalTheory.FlatModel.htAt_dualFam_frame | exact GlobalTheory.FlatModel.htAt_dualFam_frame | (intros; apply GlobalTheory.FlatModel.htAt_dualFam_frame <;> assumption)
