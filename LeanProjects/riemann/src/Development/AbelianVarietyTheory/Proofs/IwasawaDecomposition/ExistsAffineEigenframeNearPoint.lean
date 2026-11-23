import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPoints
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHolomorphicLieFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Topology ComplexOrder
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor

theorem exists_frameFam_of_isExpChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g), IsExpChart e ex → ∀ y₀ ∈ e.source, ∃ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (B : Set (Fin n → ℂ)) (a : (Fin n → ℂ) → CxFr Z σ), IsOpen B ∧ e y₀ ∈ B ∧ B ⊆ e.target ∧ HolFam B a ∧ ∀ b ∈ B, (a b).1 = e.symm b ∧ ∃ hy : (a b).1 ∈ ptsIn (genStr Z) σ V.1, F.IsMap (evHom hy) (a b).2 := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ n g e ex hex y₀ hy₀
  classical
  obtain ⟨U, hU, φ, F, hzU, hφ, -⟩ :=
    EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z (y₀.1 (IsLocalRing.closedPoint ℂ))
  let V : (gen Z).affineOpens := ⟨U, hU⟩
  have hφ' : LogKS.chart V ≫ genStr Z = spMap φ := hφ
  have hy₀V : y₀ ∈ ptsIn (genStr Z) σ V.1 := CxPts.mem_ptsIn.2 hzU
  have hov : ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1), σ = (evHom hy).comp φ := fun y hy =>
    EigLoc.spMap_inj (y.2.symm.trans (by
      rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ', ← Category.assoc, spMap_evHom hy]))
  have hx : ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1),
      y.1 ≫ genι Z = spMap (evHom hy) ≫ LogKS.chart V ≫ genι Z := fun y hy => by
    rw [← Category.assoc, spMap_evHom hy]
  have hfr : ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1),
      ∃ f : EigFrame Z σ (y.1 ≫ genι Z), EigFrame.IsMap (F : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (evHom hy) f :=
    fun y hy => EigFrame.exists_isMap F (evHom hy) (hov y hy) (hx y hy)
  choose fr hfr using hfr
  have h0 : e.symm (e y₀) ∈ ptsIn (genStr Z) σ V.1 := by rw [e.left_inv hy₀]; exact hy₀V
  let a : (Fin n → ℂ) → CxFr Z σ := fun b =>
    if h : e.symm b ∈ ptsIn (genStr Z) σ V.1 then ⟨e.symm b, fr _ h⟩ else ⟨e.symm (e y₀), fr _ h0⟩
  have ha : ∀ b (h : e.symm b ∈ ptsIn (genStr Z) σ V.1), a b = ⟨e.symm b, fr _ h⟩ := fun b h => dif_pos h
  let B : Set (Fin n → ℂ) := e.target ∩ e.symm ⁻¹' ptsIn (genStr Z) σ V.1
  have hB : IsOpen B := e.continuousOn_symm.isOpen_inter_preimage e.open_target (isOpen_ptsIn _)
  have hBt : B ⊆ e.target := Set.inter_subset_left
  have hyB : IsHolTo B (fun b => (e.symm b).1) := LocLift.isHolTo_mono hex.2.2.1 hB hBt
  let ev : (Fin n → ℂ) → (Γ(gen Z, V.1) →+* ℂ) := fun b =>
    if h : e.symm b ∈ ptsIn (genStr Z) σ V.1 then evHom h else evHom h0
  have hev : ∀ b (h : e.symm b ∈ ptsIn (genStr Z) σ V.1), ev b = evHom h := fun b h => dif_pos h
  have : IsOpenImmersion (LogKS.chart V) := IsAffineOpen.isOpenImmersion_fromSpec V.2
  have hd : ∀ r : Γ(gen Z, V.1), DifferentiableOn ℂ (fun b => ev b r) B := fun r b hb =>
    (HolLieFrame.differentiableAt_ev hyB (LogKS.chart V) ev
      (fun b' hb' => by rw [hev b' hb'.2]; exact (spMap_evHom hb'.2).symm) hb r).differentiableWithinAt
  refine ⟨V, φ, F, B, a, hB, ⟨e.map_source hy₀, h0⟩, hBt, ⟨?_, fun ρ i => ?_⟩, fun b hb => ?_⟩
  · exact LocLift.isHolTo_congr hyB fun b hb => by rw [ha b hb.2]
  · exact HolFrames.holTan_dualMap hB (F.v ρ i) (fun b hb => evHom hb.2)
      (fun r => ⟨fun b => ev b r, hd r, fun b hb => (RingHom.congr_fun (hev b hb.2) r).symm⟩)
      (fun b hb => by rw [ha b hb.2]; exact hfr _ hb.2 ρ i)
  · rw [ha b hb.2]
    exact ⟨rfl, hb.2, hfr _ hb.2⟩

end GlobalTheory.ShFam.Hor
