import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralOfEqMul
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp GlobalTheory.ChartGlue GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.ChPow

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB X}

theorem cHess_zero' (v : ReciprocityTheory.L2DbarEstimates.V D) :
    ReciprocityTheory.L2DbarEstimates.cHess D (fun _ => ((0 : ℝ) : ℂ)) v = 0 := by
  have h := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul isOpen_univ (p := fun _ => (0 : ℝ)) (q := fun _ => (0 : ℝ))
    contDiffOn_const contDiffOn_const 1 (Set.mem_univ v)
  simp only [mul_zero, add_zero, Complex.ofReal_one, one_smul] at h
  simpa using h

theorem hess_pow {φ : Weight p σ B} (hφ : φ.IsCInf) (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (n : ℕ) {j : PUnit → B.ι} (hj : y ∈ ptsIn p σ (B.U (j PUnit.unit))) :
    c.hess (φ.pow n) j y = (n : ℂ) • c.hess φ (j PUnit.unit) y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U (j PUnit.unit)))
  have hm := mem_over c.e hy hj
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho (p := fun _ => (0 : ℝ)) contDiffOn_const
    (contDiffOn_chart (hφ (j PUnit.unit)) c) (n : ℝ) hm
  rw [cHess_zero', zero_add] at e
  simp only [zero_add, Complex.ofReal_natCast] at e
  refine Eq.trans ?_ e
  show ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (((φ.pow n).φ j (c.e.symm v) : ℝ) : ℂ)) (c.e y) = _
  congr 1
  funext v
  simp only [Function.comp_apply, Weight.zpow_φ]
  push_cast
  rfl

theorem chernDens_pow {φ : Weight p σ B} (hφ : φ.IsCInf) (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (n : ℕ) : c.chernDens (φ.pow n) y = (n : ℝ) ^ D * c.chernDens φ y := by
  have hj := (mem_pow_iff (n := (n : ℤ))).1 (mem_pick (φ.pow n).isLB y)
  rw [c.chernDens_eq hφ hy hj, AlgChart.chernDens, hess_pow hφ c hy n hj, Matrix.det_smul, Fintype.card_fin,
    ← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  ring

theorem chernPart_pow {φ : Weight p σ B} (hφ : φ.IsCInf) (n : ℕ) (ε : ℤˣ) :
    (φ.pow n).chernPart D ε = ENNReal.ofReal ((n : ℝ) ^ D) • φ.chernPart D ε := by
  have h := GlobalTheory.ChernScale.glueMeas_restrict_eq (fun c : AlgChart p σ D => c.e)
    (ρ := fun c y => ENNReal.ofReal ((ε : ℤ) * c.chernDens (φ.pow n) y))
    (ρ' := fun c y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)) ENNReal.ofReal_ne_top MeasurableSet.univ
    fun c y hy _ => by
      rw [chernDens_pow hφ c hy n, mul_left_comm, ENNReal.ofReal_mul (by positivity)]
  rw [Weight.chernPart, Weight.chernPart]
  simpa only [Measure.restrict_univ] using h

end GlobalTheory.HSAmp.ChPow

namespace GlobalTheory.HSAmp

open ChPow in

theorem chInt_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (L : HermLB p) (n : ℕ) (w : ∀ σ, CxPts p σ → ℝ), chInt (L.pow n) D w = (n : ℝ) ^ D * chInt L D w := by
  intro k _ X _ p D _ L n w
  rw [chInt, chInt, mul_finsum]
  refine finsum_congr fun σ => ?_
  show ((L.φ σ).pow n).chernInt D Set.univ (w σ) = _
  rw [Weight.chernInt, Weight.chernInt, chernPart_pow (L.cInf σ), chernPart_pow (L.cInf σ), Measure.restrict_smul,
    Measure.restrict_smul, integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul, smul_eq_mul, mul_sub]

end GlobalTheory.HSAmp
