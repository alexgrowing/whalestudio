import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.DifferentiableAtChart

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open ReciprocityTheory.L2DbarEstimates (V bas wd wdb leviV)
open Filter Topology
open scoped ContDiff

namespace GlobalTheory.ShFam

attribute [local instance] Over.cartesianMonoidalCategory

def conjV (n : ℕ) : V n ≃ₗᵢ[ℝ] V n := LinearIsometryEquiv.piLpCongrRight 2 fun _ => Complex.conjLIE

theorem conjV_apply (n : ℕ) (v : V n) (a : Fin n) : conjV n v a = starRingEnd ℂ (v a) := rfl

theorem conjV_bas (n : ℕ) (j : Fin n) : conjV n (bas n j) = bas n j := by
  ext a
  simp only [conjV_apply, bas, EuclideanSpace.single_apply]
  split_ifs <;> simp

theorem conjV_I_smul_bas (n : ℕ) (j : Fin n) : conjV n (Complex.I • bas n j) = -(Complex.I • bas n j) := by
  ext a
  simp only [conjV_apply, bas, PiLp.smul_apply, PiLp.neg_apply, EuclideanSpace.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem fderiv_comp_conjV (n : ℕ) (F : V n → ℂ) (y w : V n) :
    fderiv ℝ (F ∘ conjV n) y w = fderiv ℝ F (conjV n y) (conjV n w) := by
  change fderiv ℝ (F ∘ (conjV n).toContinuousLinearEquiv) y w = _
  rw [ContinuousLinearEquiv.comp_right_fderiv]
  rfl

theorem wd_comp_conjV (n : ℕ) (j : Fin n) (F : V n → ℂ) (y : V n) :
    wd n j (F ∘ conjV n) y = wdb n j F (conjV n y) := by
  simp only [wd, wdb, fderiv_comp_conjV, conjV_bas, conjV_I_smul_bas, map_neg]
  ring

theorem wdb_comp_conjV (n : ℕ) (j : Fin n) (F : V n → ℂ) (y : V n) :
    wdb n j (F ∘ conjV n) y = wd n j F (conjV n y) := by
  simp only [wd, wdb, fderiv_comp_conjV, conjV_bas, conjV_I_smul_bas, map_neg]
  ring

theorem leviV_comp_conjV (n : ℕ) (g : V n → ℝ) (y : V n) (ξ : Fin n → ℂ) :
    leviV n ((fun v => (g v : ℂ)) ∘ conjV n) y ξ =
      starRingEnd ℂ (leviV n (fun v => (g v : ℂ)) (conjV n y) (star ξ)) := by
  set G : V n → ℂ := fun v => (g v : ℂ) with hGdef
  have hG : ∀ k, wd n k G = fun w => starRingEnd ℂ (wdb n k G w) := fun k => by
    have e : G = fun w => starRingEnd ℂ (G w) := funext fun w => (Complex.conj_ofReal _).symm
    funext w
    conv_lhs => rw [e]
    exact ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wd_conj' n k G w
  have h1 : ∀ k, wdb n k (G ∘ conjV n) = (wd n k G) ∘ conjV n := fun k =>
    funext fun w => wdb_comp_conjV n k G w
  have h2 : ∀ j k w, wd n j (wdb n k (G ∘ conjV n)) w =
      starRingEnd ℂ (wd n j (wdb n k G) (conjV n w)) := fun j k w => by
    rw [h1, wd_comp_conjV, hG, ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.wdb_conj']
  simp only [leviV, h2, map_sum, map_mul, Complex.conj_conj, Pi.star_apply, Complex.star_def]

theorem smoothOn_comp_ddcForm_of_isConjMap : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ)
    [SmoothOfRelativeDimension d p] (σ σ' : k →+* ℂ) (j : CxPts p σ' → CxPts p σ), IsConjMap j →
    ∀ (W : Set (CxPts p σ)) (φ : CxPts p σ → ℝ), IsOpen W → (AnRead.all p σ d).SmoothOn W φ →
    IsOpen (j ⁻¹' W) ∧ (AnRead.all p σ' d).SmoothOn (j ⁻¹' W) (φ ∘ j) ∧
    ∀ (c' : AlgChart p σ' d), ∀ z ∈ c'.e.source, ∃ c : AlgChart p σ d, j z ∈ c.e.source ∧
      ∀ (ψ : CxPts p σ → ℝ) (ξ : Fin d → ℂ), ddcForm (ψ ∘ j) c' z ξ = ddcForm ψ c (j z) (star ξ) := by
  intro k _ Y p d _ σ σ' j hj W φ hW hφ
  rcases isEmpty_or_nonempty (CxPts p σ') with hE | ⟨⟨z0⟩⟩
  · refine ⟨?_, fun c' => ?_, fun c' z => (hE.false z).elim⟩
    · rw [Set.eq_empty_of_isEmpty (j ⁻¹' W)]
      exact isOpen_empty
    · rw [Set.eq_empty_of_isEmpty (j ⁻¹' W)]
      simp
  · have hσ : σ = (starRingEnd ℂ).comp σ' := by
      have h1 := (j z0).2
      rw [hj z0, Category.assoc, z0.2, spMap, spMap, spMap, ← Spec.map_comp] at h1
      have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
      exact h2.symm
    obtain ⟨hcont, hch⟩ := GlobalTheory.ConjChart.continuous_and_exists_conj_chart k Y p d σ σ' j hσ hj
    have key : ∀ c' : AlgChart p σ' d, ∃ c : AlgChart p σ d, (∀ z, j z ∈ c.e.source ↔ z ∈ c'.e.source) ∧
        (∀ z ∈ c'.e.source, c.e (j z) = conjV d (c'.e z)) ∧
        ∀ v ∈ c'.e.target, j (c'.e.symm v) = c.e.symm (conjV d v) := fun c' => by
      obtain ⟨c, hs, he⟩ := hch c'
      have e1 : ∀ z ∈ c'.e.source, c.e (j z) = conjV d (c'.e z) := fun z hz => by
        ext a
        rw [he z hz a, conjV_apply]
      refine ⟨c, hs, e1, fun v hv => ?_⟩
      have hz : c'.e.symm v ∈ c'.e.source := c'.e.map_target hv
      rw [← c.e.left_inv ((hs _).2 hz), e1 _ hz, c'.e.right_inv hv]
    refine ⟨hW.preimage hcont, fun c' => ?_, fun c' z hz => ?_⟩
    · obtain ⟨c, hs, e1, e2⟩ := key c'
      show ContDiffOn ℝ ∞ ((φ ∘ j) ∘ c'.e.symm) (c'.e.target ∩ c'.e.symm ⁻¹' (j ⁻¹' W))
      have hc := hφ.chart hW c
      refine ((hc.comp (conjV d).contDiff.contDiffOn fun v hv => ?_).congr fun v hv => ?_)
      · have hz : c'.e.symm v ∈ c'.e.source := c'.e.map_target hv.1
        refine ⟨?_, ?_⟩
        · have e3 : conjV d v = c.e (j (c'.e.symm v)) := by rw [e1 _ hz, c'.e.right_inv hv.1]
          rw [e3]
          exact c.e.map_source ((hs _).2 hz)
        · show c.e.symm (conjV d v) ∈ W
          rw [← e2 v hv.1]
          exact hv.2
      · show (φ ∘ j) (c'.e.symm v) = (φ ∘ c.e.symm) (conjV d v)
        simp only [Function.comp_apply, e2 v hv.1]
    · obtain ⟨c, hs, e1, e2⟩ := key c'
      refine ⟨c, (hs z).2 hz, fun ψ ξ => ?_⟩
      have h := leviV_comp_conjV d (fun v => ψ (c.e.symm v)) (c'.e z) ξ
      simp only [ddcForm, AlgChart.levi]
      congr 1
      rw [e1 z hz]
      refine Eq.trans (congrArg Complex.re (ReciprocityTheory.L2DbarEstimates.leviV_congr ?_ ξ))
        (Eq.trans (congrArg Complex.re h) (Complex.conj_re _))
      refine eventually_of_mem (c'.e.open_target.mem_nhds (c'.e.map_source hz)) fun v hv => ?_
      simp only [Function.comp_apply, e2 v hv]

end GlobalTheory.ShFam
