import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackChartMetricBlockForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartOffClosedSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernLowDim

open MeasureTheory Set GlobalTheory.ChartGlue GlobalTheory.Points

theorem det_mul_mul_eq_zero {m n : ℕ} (hmn : m < n) (P : Matrix (Fin n) (Fin m) ℂ)
    (K : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin m) (Fin n) ℂ) : (P * K * Q).det = 0 := by
  by_contra h
  have hu : IsUnit (P * K * Q) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 : (P * K * Q).rank ≤ m :=
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)).trans
      ((Matrix.rank_le_card_width P).trans (by simp))
  simp only [Fintype.card_fin] at h1
  omega

theorem chernPart_pull_of_lt : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (e e' : ℕ), IsArithVar p e → IsArithVar q e' → e < e' → ∀ (g : Y ⟶ X) (hg : g ≫ p = q), g (genericPoint Y) = genericPoint X → ∀ (N : HermLB p) (σ : k →+* ℂ) (ε : ℤˣ), ((N.pull g hg).φ σ).chernPart e' ε = 0 := by
  intro k _ X Y _ _ p q e e' hX hY hlt g hg hgen N σ ε
  obtain ⟨T, hT, hTg, hc⟩ := GlobalTheory.GenericChart.exists_isClosed_chart k X p e hX
  set Z : Set Y := (⇑g) ⁻¹' T with hZdef
  have hZ : IsClosed Z := hT.preimage g.continuous
  have hZg : genericPoint Y ∉ Z := by
    simp only [hZdef, mem_preimage, hgen]
    exact hTg
  set φ := (N.pull g hg).φ σ
  set A : Set (CxPts q σ) := {y | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} with hAdef
  have h0 : φ.chernPart e' ε A = 0 := GlobalTheory.ChernNull.chernPart_over_closed hY Z hZ hZg σ φ ε
  have hA : MeasurableSet A := by
    have : A = (ptsIn q σ ⟨Zᶜ, hZ.isOpen_compl⟩)ᶜ := by
      ext y
      simp [hAdef, mem_ptsIn]
    rw [this]
    exact (isOpen_ptsIn _).measurableSet.compl

  have hdens : ∀ (c : AlgChart q σ e') (y : CxPts q σ), y ∈ c.e.source → y ∉ A →
      c.chernDens φ y = 0 := by
    intro c y hys hyA
    have hy' : (PtsOver.map g hg (spMap σ) y).1 (IsLocalRing.closedPoint ℂ) ∉ T := by
      intro hT'
      exact hyA (show g (y.1 (IsLocalRing.closedPoint ℂ)) ∈ T from hT')
    obtain ⟨c', hc'⟩ := hc σ _ hy'
    obtain ⟨P, Q, hPQ⟩ := GlobalTheory.HessPull.hess_pull_factor k X Y p q g hg σ e' e c c' y hys hc'
    obtain ⟨K, hK⟩ := hPQ N (pick φ.isLB y) (mem_pick _ y)
    rw [AlgChart.chernDens, hK, det_mul_mul_eq_zero hlt, Complex.zero_re, mul_zero]
  have key : φ.chernPart e' ε ≤ (φ.chernPart e' ε).restrict A := iSup_le fun c => by
    have e0 : chartMeas c.e (fun y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)) Aᶜ = 0 := by
      rw [chartMeas_apply _ _ hA.compl]
      have hm := measurableSet_image c.e (c.e.open_source.measurableSet.inter hA.compl)
        inter_subset_left
      rw [setLIntegral_congr_fun hm (g := fun _ => 0) ?_, lintegral_zero]
      rintro _ ⟨y, hy, rfl⟩
      simp only [c.e.left_inv hy.1, hdens c y hy.1 hy.2, mul_zero, ENNReal.ofReal_zero]
    rw [← Measure.restrict_eq_self_of_ae_mem (s := A) (mem_ae_iff.2 e0)]
    exact Measure.restrict_mono le_rfl (le_iSup (fun c : AlgChart q σ e' =>
      chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)) c)
  refine Measure.measure_univ_eq_zero.1 (le_antisymm ((key univ).trans_eq ?_) zero_le)
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, h0]

end GlobalTheory.ChernLowDim
