import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexPointDerivationSeparatingParamsCharStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDerivationAffineOpenEqFderivEtaleChartStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleChartHolomorphicCoordinateChangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompleteHolomorphicCoordinatesIndependentDiffereStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointMemClosedIffFactorVanishesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory
namespace SncChart

theorem linearIndependent_fderiv_params (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ)
    [SmoothOfRelativeDimension n p] (c : AlgChart p σ n) (x₀ : CxPts p σ) (hx : x₀ ∈ c.e.source)
    (U : Y.affineOpens) (hy : x₀.1 (IsLocalRing.closedPoint ℂ) ∈ U.1) (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hR : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) m
      (fun i => Y.presheaf.germ U.1 _ hy (f i))) :
    LinearIndependent ℂ (fun i => fderiv ℂ (CxPts.ev p σ U.1 (f i) ∘ c.e.symm) (c.e x₀)) := by
  rw [Fintype.linearIndependent_iff]
  intro l hl
  by_contra hne
  push_neg at hne
  have hl0 : l ≠ 0 := fun h => by obtain ⟨i, hi⟩ := hne; exact hi (congrFun h i)
  obtain ⟨δ, hc0, hlb, hne'⟩ := GlobalTheory.T.exists_complexPointDerivation_separating_params_charZero k Y p n σ inferInstance x₀ U hy m f hR l hl0
  obtain ⟨v, hv⟩ := GlobalTheory.T.pointDerivation_affineOpen_eq_fderiv_etaleChart k Y p n σ c x₀ hx U (CxPts.mem_ptsIn.2 hy) δ hc0 hlb
  apply hne'
  have := congrArg (fun F => F v) hl
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.zero_apply] at this
  simpa [hv] using this

theorem exists_chart_of_fderiv (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ)
    (c : AlgChart p σ n) (x₀ : CxPts p σ) (hx : x₀ ∈ c.e.source) (W : Y.Opens)
    (hW : x₀ ∈ CxPts.ptsIn p σ W) (a : ℕ) (g : Fin a → Γ(Y, W))
    (h0 : ∀ i, CxPts.ev p σ W (g i) x₀ = 0)
    (hli : LinearIndependent ℂ (fun i => fderiv ℂ (CxPts.ev p σ W (g i) ∘ c.e.symm) (c.e x₀))) :
    ∃ e : OpenPartialHomeomorph (CxPts p σ) (Fin n → ℂ), x₀ ∈ e.source ∧ e.source ⊆ CxPts.ptsIn p σ W ∧
      e x₀ = 0 ∧ (∀ j, HolAlong e.source fun x => e x j) ∧ IsHolTo e.target (fun z => (e.symm z).1) ∧
      ∀ x ∈ e.source, ∀ (j : Fin n) (hj : (j : ℕ) < a), e x j = CxPts.ev p σ W (g ⟨j, hj⟩) x := by
  let c' := c.restr (CxPts.ptsIn p σ W) (CxPts.isOpen_ptsIn W)
  have hx' : x₀ ∈ c'.e.source := ⟨hx, hW⟩
  let G : Fin a → ReciprocityTheory.L2DbarEstimates.V n → ℂ := fun i => CxPts.ev p σ W (g i) ∘ c.e.symm
  have hv0 : c.e x₀ ∈ c'.e.target := c'.e.map_source hx'
  have hG : ∀ i, DifferentiableOn ℂ (G i) c'.e.target := fun i =>
    (c.holo W (g i)).mono (fun v hv => ⟨hv.1, hv.2⟩)
  have hG0 : ∀ i, G i (c.e x₀) = 0 := by
    intro i
    simp only [G, Function.comp_apply, c.e.left_inv hx, h0]
  obtain ⟨ψ, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.complete_holomorphic_coordinates_independent_differentials n a (c.e x₀) c'.e.target G c'.e.open_target hv0 hG hG0 hli
  obtain ⟨hh, hs⟩ := GlobalTheory.T.etaleChart_holomorphic_coordinate_change k Y p n σ c' ψ h4 h5
  refine ⟨c'.e.trans ψ, ⟨hx', h1⟩, fun x hx => hx.1.2, h3, hh, hs, fun x hx j hj => ?_⟩
  have := h6 _ hx.2 j hj
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply] at this ⊢
  refine this.trans ?_
  simp only [G, Function.comp_apply]
  exact congrArg _ (c'.e.left_inv hx.1)

theorem exists_coords : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (D : TopologicalSpace.Closeds Y) (σ : k →+* ℂ), SmoothOfRelativeDimension n p → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal D) → ∀ x₀ : CxPts p σ, ∃ (a : ℕ) (e : OpenPartialHomeomorph (CxPts p σ) (Fin n → ℂ)), x₀ ∈ e.source ∧ e x₀ = 0 ∧ (∀ j, HolAlong e.source fun x => e x j) ∧ IsHolTo e.target (fun z => (e.symm z).1) ∧ ∀ x ∈ e.source, (x.1 (IsLocalRing.closedPoint ℂ) ∉ D ↔ ∀ j : Fin n, (j : ℕ) < a → e x j ≠ 0) := by
  intro k _ _ Y p n D σ hsm hsnc x₀
  haveI := hsm
  obtain ⟨-, U, hy, m, f, J, hR, hD⟩ := hsnc (x₀.1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := n) (p := p) (σ := σ) x₀
  have hli := linearIndependent_fderiv_params k Y p n σ c x₀ hc U hy m f hR
  let ix : Fin J.card → Fin m := fun i => (J.equivFin.symm i).1
  have hix : Function.Injective ix := fun i j h => J.equivFin.symm.injective (Subtype.ext h)
  have hxU : x₀ ∈ CxPts.ptsIn p σ U.1 := CxPts.mem_ptsIn.2 hy
  have h0 : ∀ i, CxPts.ev p σ U.1 (f (ix i)) x₀ = 0 := by
    intro i
    by_contra hne
    have hb := CxPts.mem_ptsIn.1 ((CxPts.mem_ptsIn_basicOpen hxU (f (ix i))).2 hne)
    rw [Scheme.mem_basicOpen _ _ _ hy] at hb
    have hmem : Y.presheaf.germ U.1 _ hy (f (ix i)) ∈ IsLocalRing.maximalIdeal _ := by
      rw [← hR.1]; exact Ideal.subset_span ⟨ix i, rfl⟩
    exact hmem hb
  have hli' := hli.comp ix hix
  have hcard : J.card ≤ n := by
    have := hli'.fintype_card_le_finrank
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ReciprocityTheory.L2DbarEstimates.V n) (F' := ℂ)).finrank_eq,
      Module.finrank_linearMap, Module.finrank_self, _root_.mul_one] at this
    simpa [ReciprocityTheory.L2DbarEstimates.V] using this
  obtain ⟨e, hx0, hsub, he0, hhol, hsymm, hev⟩ :=
    exists_chart_of_fderiv k Y p n σ c x₀ hc U.1 hxU J.card (fun i => f (ix i)) h0 hli'
  refine ⟨J.card, e, hx0, he0, hhol, hsymm, fun x hx => ?_⟩
  rw [GlobalTheory.T.complexPoint_mem_closed_iff_factor_vanishes k Y p σ D U m f J hD x (hsub hx)]
  constructor
  · intro h j hj he
    exact h ⟨ix ⟨j, hj⟩, (J.equivFin.symm _).2, by rw [← hev x hx j hj]; exact he⟩
  · rintro h ⟨i, hi, hi0⟩
    have ht : ix (J.equivFin ⟨i, hi⟩) = i := by simp [ix]
    have hlt : ((J.equivFin ⟨i, hi⟩ : Fin J.card) : ℕ) < n := lt_of_lt_of_le (Fin.isLt _) hcard
    refine h ⟨_, hlt⟩ (J.equivFin ⟨i, hi⟩).isLt ?_
    rw [hev x hx ⟨_, hlt⟩ (J.equivFin ⟨i, hi⟩).isLt]
    simpa [ht] using hi0

end SncChart
end GlobalTheory
