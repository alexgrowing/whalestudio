import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicComparison

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem htAt_dualFam_frame : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt →
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
  intro hK hTate hVal E _ _ _ H Dw τ p _ _ hs n l l' Xo Xo' c c' W Y r ν hle hOv hA N a T S hLat _ yb yy P π ψ y hHT β hβ
  obtain ⟨ta, u, hlev, hDF⟩ := hTate E H Dw l' Xo' c' W Y p n hs hA yb yy P π ψ hHT.1 β (conjEmb τ.1) (Ind Dw τ.1)
    N a T S hLat
  rw [htAt_embV_eq E H Dw l l' Xo Xo' c c' W Y r ν hle hOv p yb yy P π ψ y hHT β hβ (conjEmb τ.1)] at hDF
  obtain ⟨hPt, -, -, z, g, a0, x, -, -, -, hTie, hLB⟩ := hHT
  obtain ⟨-, -, hπ, hψpb, hgen, -⟩ := hPt
  have hact : ∀ b, (P.oA.act b).left ≫ ψ = ψ ≫ (Y.oF.t.act.act b).left := fun b =>
    Y.m.cart.1.hom_ext
      (by rw [Category.assoc, Category.assoc, Y.m.act, hgen, ← Category.assoc ψ, hgen, ← Category.assoc, P.gen_act,
        Category.assoc, hπ, Category.assoc])
      (by rw [Category.assoc, Category.assoc, Over.w, hψpb.1.w, Over.w_assoc])
  have hact2 : ∀ b, (P.oA.act b).left ≫ (ψ ≫ ν.φ) = (ψ ≫ ν.φ) ≫ (Xo.univ.t.act.act b).left := fun b => by
    rw [← Category.assoc, hact, Category.assoc, ν.act, Category.assoc]
  have hpb2 := hψpb.comp ν.cart
  have heig : ∀ σ j, AvDefs.IsEig P.Gt P.oGt (embInt c P.integers σ) (x σ j) := fun σ j b =>
    ((hTie σ j).act b (hact2 b)).unique hpb2.1
      (by rw [z.eig σ j b, ← algebraMap_embInt P.integers]; exact (hTie σ j).scale _)
  have hK' := (hK p ℂ_[p] Valued.v 𝓞_ℂ_[p] (𝓞 E) P).2.2.2
  have hspan : ∀ σ i, (∑ j, g σ i j • P.bLie (x σ j)) ∈ Submodule.span ℂ_[p] (Set.range P.bLie) := fun σ i =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have heigV : ∀ σ i, (∑ j, g σ i j • P.bLie (x σ j)) ∈ P.eigV (embInt c P.integers σ) := fun σ i =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bLie_mem_eigV (heig σ j))
  have hmem : ∀ σ i, (∑ j, g σ i j • P.bLie (x σ j)) ∈ htLat c P σ := fun σ i =>
    ((hLB σ).2.le (Submodule.subset_span ⟨i, rfl⟩)).1
  have horth : ∀ k k', P.pairV (∑ j, g τ.1 k j • P.bLie (x τ.1 j))
      (∑ j, g (conjEmb τ.1) k' j • P.bLie (x (conjEmb τ.1) j)) = 0 := fun k k' => by
    have h1 : (∑ j, g τ.1 k j • P.bLie (x τ.1 j)) ∈ P.W := hK'.2.2.2.2.2.2 ▸ hspan _ _
    exact (hK'.2.2.2.2.1 _).1 h1 _ (hK'.2.2.2.2.2.2 ▸ hspan _ _)
  obtain ⟨lam, hlam, hsgn, σ, hσ⟩ := hVal E H Dw l c p hs P τ _ _ u hDF _ _ (fun k => heigV _ k) (fun k => heigV _ k)
    horth (hLB τ.1) (hLB (conjEmb τ.1))
  refine ⟨ta, _, _, σ, hlev, fun k => ⟨hmem _ k, hspan _ k, heigV _ k⟩, fun k => ⟨hmem _ k, hspan _ k, heigV _ k⟩,
    hσ, ?_⟩
  have e := congrArg norm (hsgn σ)
  have hs1 : ‖((Equiv.Perm.sign σ : ℤ) : ℂ_[p])‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [norm_mul, norm_mul, hlam, hσ, hs1, _root_.one_mul, _root_.one_mul] at e
  exact e.symm

end GlobalTheory.FlatModel
