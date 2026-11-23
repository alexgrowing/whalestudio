import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfConjEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointStalkFrameVectorsEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicEigenvectorCoordinatesHolomorphicUniforStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineLieEigenFrameNearComplexPointStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

theorem exists_holo_coord_frameAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ τ : GlobalTheory.AllWt.Psi H, ∀ (kU : U.Comp) (G : V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X kU).Ψ (Dw.p + Dw.q)), (∀ᶠ u in 𝓝 (c'.e y), ∃ h : G u ∈ (U.X kU).dom, cxPt T.Z (U.un kU ⟨G u, h⟩) = cxOf e σ hj (c'.e.symm u)) → (∀ τ' a b, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u) → ∃ M : V X.dim → Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) ℂ, (∀ a b, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => M u a b) u) ∧ IsUnit (M (c'.e y)).det ∧ ∀ᶠ u in 𝓝 (c'.e y), ∃ h : G u ∈ (U.X kU).dom, (∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm u)).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (c'.e.symm u) g) ∧ ∀ (x : Sp ℂ ⟶ T.Z.X) (g : EigFrame T.Z σ x), FrameAt e f₀ A₀ A (c'.e.symm u) g → ∀ i, IsCombAtG T.Z.t ((cxPt T.Z (U.un kU ⟨G u, h⟩)).1 ≫ genι T.Z) ((cxFrame T.Z (U.un kU ⟨G u, h⟩)).v τ.1) (fun b => M u b i) (g.v τ.1 i) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hLie y _ c' hyc A hA τ kU G hF hG
  obtain ⟨-, -, hTd⟩ := hLie
  obtain ⟨W, hW, φ, fW, hyW, hnear⟩ := GlobalTheory.T.exists_affine_lieEigenFrame_near_complexPoint E H Dw l Xo c O β T.Z F e σ X j f₀ Eb A₀ hj hTd y A hA
  classical
  let ev : V X.dim → (Γ(X.X, W) →+* ℂ) := fun u =>
    if h : c'.e.symm u ∈ ptsIn X.str (σ.comp e.toRingHom) W then evHom h else evHom hyW
  have hev : ∀ u (h : c'.e.symm u ∈ ptsIn X.str (σ.comp e.toRingHom) W), ev u = evHom h := fun u h => dif_pos h
  set S : Set (V X.dim) := c'.e.target ∩ c'.e.symm ⁻¹' ptsIn X.str (σ.comp e.toRingHom) W with hSdef
  have hSo : IsOpen S := c'.e.continuousOn_symm.isOpen_inter_preimage c'.e.open_target (isOpen_ptsIn _)
  have hu0 : c'.e y ∈ S := ⟨c'.e.map_source hyc, by show c'.e.symm (c'.e y) ∈ ptsIn X.str (σ.comp e.toRingHom) W; rw [c'.e.left_inv hyc]; exact hyW⟩
  have hSn : ∀ᶠ u in 𝓝 (c'.e y), u ∈ S := hSo.mem_nhds hu0
  have hevd : ∀ t, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => ev u t) u := by
    intro t
    filter_upwards [hSn] with u hu
    refine ((c'.holo W t).differentiableAt (hSo.mem_nhds hu)).congr_of_eventuallyEq ?_
    filter_upwards [hSo.mem_nhds hu] with v hv
    simp only [Function.comp_apply, hev v hv.2, ev_eq hv.2]
  have hφ : ∀ᶠ u in 𝓝 (c'.e y), (ev u).comp φ = σ := by
    filter_upwards [hSn] with u hu
    rw [hev u hu.2]; exact (hnear _ hu.2).1
  have hpt : ∀ᶠ u in 𝓝 (c'.e y), ∃ h : G u ∈ (U.X kU).dom, (cxPt T.Z (U.un kU ⟨G u, h⟩)).1 ≫ genι T.Z =
      spMap (ev u) ≫ ((show Sp Γ(X.X, W) ⟶ X.X from hW.fromSpec) ≫ j) ≫ genι T.Z := by
    filter_upwards [hSn, hF] with u hu ⟨h, hc⟩
    refine ⟨h, ?_⟩
    rw [hc, hev u hu.2]
    have := GlobalTheory.Points.specMap_valMap_fromSpec hW (c'.e.symm u).1 hu.2
    show (c'.e.symm u).1 ≫ j ≫ genι T.Z = _
    rw [← this]
    simp only [Category.assoc]
    rfl
  obtain ⟨M, hMd, hMc⟩ := GlobalTheory.T.algebraic_eigenvector_coordinates_holomorphic_uniformisation E H Dw l Xo c O β T.Z σ U hσ hU X.dim (c'.e y) Γ(X.X, W) φ _ fW ev kU G τ.1 hevd hG hφ hpt
  refine ⟨M, hMd, ?_, ?_⟩
  · obtain ⟨h0, hc0⟩ := hMc.self_of_nhds
    obtain ⟨h0', hF0⟩ := hF.self_of_nhds
    obtain ⟨-, g0, -, hm0⟩ := hnear _ hu0.2
    have hx : (cxOf e σ hj (c'.e.symm (c'.e y))).1 ≫ genι T.Z = (cxPt T.Z (U.un kU ⟨G (c'.e y), h0⟩)).1 ≫ genι T.Z := by
      rw [hF0]
    have key : ∀ {x x' : Sp ℂ ⟶ T.Z.X} (hx : x = x') (g : EigFrame T.Z σ x) (G' : EigFrame T.Z σ x')
        (N : Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) ℂ),
        (∀ i, IsCombAtG T.Z.t x' (G'.v τ.1) (fun b => N b i) (g.v τ.1 i)) → IsUnit N.det := by
      intro x x' hx g G' N h
      subst hx
      rw [← EigFrame.co_eq (f := G') (g := g) h]
      exact EigFrame.isUnit_det_co _ _ _
    refine key hx g0 (cxFrame T.Z (U.un kU ⟨G (c'.e y), h0⟩)) (M (c'.e y)) fun i => ?_
    rw [hm0 τ.1 i, ← hev _ hu0.2]
    exact hc0 i
  · filter_upwards [hMc, hSn] with u ⟨h, hc⟩ hu
    obtain ⟨-, g0, hg0, hm0⟩ := hnear _ hu.2
    refine ⟨h, ⟨g0, hg0⟩, fun x g hg i => ?_⟩
    rw [GlobalTheory.T.complexPoint_stalkFrame_vectors_eq E H Dw l Xo c O β T.Z F e σ X j f₀ A₀ A _ _ _ g g0 hg hg0 τ.1 i, hm0 τ.1 i, ← hev _ hu.2]
    exact hc i

end GlobalTheory.LieBase
