import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralOfEqMul
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaTop

theorem glueMeas_univ_eq {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {n : ℕ} {ι : Type*}
    (e : ι → OpenPartialHomeomorph X (ReciprocityTheory.L2DbarEstimates.V n)) {ρ ρ' : ι → X → ℝ≥0∞} {a : ℝ≥0∞} (ha : a ≠ ⊤)
    (h : ∀ i, ∀ y ∈ (e i).source, ρ i y = a * ρ' i y) :
    ChartGlue.glueMeas e ρ univ = a * ChartGlue.glueMeas e ρ' univ := by
  have := GlobalTheory.ChernScale.glueMeas_restrict_eq e ha MeasurableSet.univ (fun i y hy _ => h i y hy)
  simpa only [Measure.restrict_univ, Measure.smul_apply, smul_eq_mul] using
    congrArg (fun μ : Measure X => μ univ) this

theorem topForm_eq_mul_gdeg : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (N : HermLB p) (ρ : ∀ σ : k →+* ℂ, AlgChart p σ 1 → CxPts p σ → ℝ) (I l : ℝ), IsTopForm ρ I → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ c : AlgChart p σ 1, y ∈ c.e.source ∧ ρ σ c y = l * c.chernDens (N.φ σ) y) → I = l * gdeg N 1 := by
  intro k _ S p hp N ρ I l hI hρ
  have hall : ∀ σ (c : AlgChart p σ 1) y, y ∈ c.e.source → ρ σ c y = l * c.chernDens (N.φ σ) y := by
    intro σ c y hy
    obtain ⟨c', hy', hc'⟩ := hρ σ y
    rw [(hI.1 σ c).2 c' y hy hy', hc', c.chernDens_trans c' (N.cInf σ) hy hy']
    ring
  rw [hI.2.2, gdeg_eq, mul_finsum]
  refine finsum_congr fun σ => ?_
  rw [UnitsInt.univ, Finset.sum_pair (by decide), Finset.sum_pair (by decide)]
  rcases le_or_gt 0 l with hl | hl
  · have key : ∀ ε : ℤˣ, ChartGlue.glueMeas (fun c : AlgChart p σ 1 => c.e)
        (fun c y => ENNReal.ofReal ((ε : ℤ) * ρ σ c y)) univ = ENNReal.ofReal l *
        ChartGlue.glueMeas (fun c : AlgChart p σ 1 => c.e)
        (fun c y => ENNReal.ofReal ((ε : ℤ) * c.chernDens (N.φ σ) y)) univ := fun ε =>
      glueMeas_univ_eq _ ENNReal.ofReal_ne_top fun c y hy => by
        rw [hall σ c y hy, ← ENNReal.ofReal_mul hl]
        ring_nf
    rw [key, key, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hl]
    ring
  · have key : ∀ ε : ℤˣ, ChartGlue.glueMeas (fun c : AlgChart p σ 1 => c.e)
        (fun c y => ENNReal.ofReal ((ε : ℤ) * ρ σ c y)) univ = ENNReal.ofReal (-l) *
        ChartGlue.glueMeas (fun c : AlgChart p σ 1 => c.e)
        (fun c y => ENNReal.ofReal (((-ε : ℤˣ) : ℤ) * c.chernDens (N.φ σ) y)) univ := fun ε =>
      glueMeas_univ_eq _ ENNReal.ofReal_ne_top fun c y hy => by
        rw [hall σ c y hy, ← ENNReal.ofReal_mul (by linarith)]
        push_cast
        ring_nf
    rw [key, key, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), neg_neg]
    push_cast
    ring

end GlobalTheory.ThetaTop
