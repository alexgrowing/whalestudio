import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinateNearGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchDimZero

theorem volume_univ_zero : (volume : Measure (ReciprocityTheory.L2DbarEstimates.V 0)) Set.univ = 1 := by
  have h := (stdOrthonormalBasis ℝ (ReciprocityTheory.L2DbarEstimates.V 0)).volume_parallelepiped
  rwa [Set.eq_univ_of_forall (s := parallelepiped _) fun v =>
    (Subsingleton.elim 0 v) ▸ ⟨0, by simp, by simp⟩] at h

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem exists_chart (hq : IsArithVar q 0) {σ : k →+* ℂ} (y : CxPts q σ) :
    ∃ c : AlgChart q σ 0, y ∈ c.e.source := by
  obtain ⟨U, x, hU, hg, hx⟩ := GenericEtale.exists_etale_coords hq
  have hy : y ∈ ptsIn q σ U := by
    rw [mem_ptsIn, show y.1 (IsLocalRing.closedPoint ℂ) = genericPoint Y from
      TwistTop.under_eq_genericPoint hq y]
    exact hg
  obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hU x hx hy
  exact ⟨c, hc⟩

theorem isProper (hq : IsArithVar q 0) : IsProper q := by
  obtain ⟨N, j, _, hj⟩ := hq.isProjOver
  have := isProper_str k N
  exact hj ▸ inferInstance

theorem chernPart_singleton (hq : IsArithVar q 0) (L : HermLB q) (σ : k →+* ℂ) (ε : ℤˣ)
    (y : CxPts q σ) : (L.φ σ).chernPart 0 ε {y} = ENNReal.ofReal (ε : ℤ) := by
  have := isProper hq
  obtain ⟨c, hc⟩ := exists_chart hq y
  rw [Weight.chernPart_apply (L.cInf σ) ε c (measurableSet_singleton y)
    (Set.singleton_subset_iff.2 hc)]
  have e : c.e '' {y} = Set.univ := Set.eq_univ_of_forall fun v => ⟨y, rfl, Subsingleton.elim _ _⟩
  simp [e, AlgChart.chernDens_zero, volume_univ_zero]

theorem finite_cxPts (hq : IsArithVar q 0) (σ : k →+* ℂ) : Finite (CxPts q σ) := by
  have := HtSelfInter.finite_ringHom hq
  obtain ⟨e⟩ := HtSelfInter.nonempty_equiv hq
  have : Finite (Σ σ : k →+* ℂ, CxPts q σ) := .of_equiv _ e.symm
  exact .of_injective _ (sigma_mk_injective (i := σ))

theorem chernInt_univ (hq : IsArithVar q 0) (L : HermLB q) (σ : k →+* ℂ) (f : CxPts q σ → ℝ) :
    (L.φ σ).chernInt 0 Set.univ f = ∑ᶠ y, f y := by
  have := isProper hq
  have := finite_cxPts hq σ
  let := Fintype.ofFinite (CxPts q σ)
  have h₁ : (L.φ σ).chernPart 0 1 = Measure.count := Measure.ext_iff_singleton.2 fun y => by
    rw [chernPart_singleton hq L σ 1 y, Measure.count_singleton]
    simp
  have h₂ : (L.φ σ).chernPart 0 (-1) = 0 := Measure.ext_iff_singleton.2 fun y => by
    rw [chernPart_singleton hq L σ (-1) y]
    simp
  rw [Weight.chernInt, h₁, h₂, Measure.restrict_univ, Measure.restrict_univ, integral_zero_measure,
    sub_zero, integral_fintype (Integrable.of_finite (μ := Measure.count) (f := f)), finsum_eq_sum_of_fintype]
  simp [Measure.real]

theorem main : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ (M N : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.archInt M 0 hr = ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts q σ, logNorm (M.φ σ) r y := by
  intro k _ Y _ q hq M N r hr
  unfold HermLB.archInt
  refine finsum_congr fun σ => ?_
  have hS : offSupp q σ (M.div hr) = Set.univ := Set.eq_univ_of_forall fun y => mem_offSupp.2 fun h =>
    CartierDiv.genericPoint_notMem_supp _ (TwistTop.under_eq_genericPoint hq y ▸ h)
  rw [hS, chernInt_univ hq]

end GlobalTheory.ArchDimZero
