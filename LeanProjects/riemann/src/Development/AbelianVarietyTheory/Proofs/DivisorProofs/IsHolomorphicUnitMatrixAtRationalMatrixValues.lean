import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointTwo
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem holUnitAt_ratVal : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (s : ℕ) (T : Matrix (Fin s) (Fin s) X.Fn)
    (y : CxPts X.str σ), (∀ i j, RegAt (under y) (T i j)) → T.det ≠ 0 → RegAt (under y) (T.det)⁻¹ →
    HolUnitAt (atlas X σ) (fun z => T.map (ratVal · z)) y := by
  intro F _ σ X s T y hT hd hdi
  refine ⟨?_, fun c hc a b => ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
    let T' : Matrix (Fin s) (Fin s) ((ratOf X).O (under y)).toSubring :=
      Matrix.of fun i j => ⟨T i j, mem_O_ratOf.2 (hT i j)⟩
    have e1 : T.map (ratVal · y) = T'.map ψ := by
      ext i j
      exact hψ (T' i j)
    have e2 : ((T'.det : ((ratOf X).O (under y)).toSubring) : X.Fn) = T.det :=
      (RingHom.map_det (((ratOf X).O (under y)).toSubring.subtype) T').trans rfl
    have hu : UnitAt (under y) T.det := (unitAt_iff hd).2 ⟨e2 ▸ mem_O_ratOf.1 T'.det.2, hdi⟩
    have hne := ratVal_ne_zero (y := y) hu
    rw [← e2, hψ] at hne
    show IsUnit (T.map (ratVal · y)).det
    rw [e1, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 hne
  · obtain ⟨U, hU, g, e⟩ := (hT a b).exists_fnOf
    have hyU : y ∈ ptsIn X.str σ U := mem_ptsIn.2 hU
    filter_upwards [(GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds (GlobalTheory.ChartGlue.mem_over c.e hc hyU)] with v hv
    have hdv : DifferentiableAt ℂ (ev X.str σ U g ∘ c.e.symm) v :=
      (c.holo U g).differentiableAt ((GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds hv)
    refine hdv.congr_of_eventuallyEq ?_
    filter_upwards [(GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds hv] with u hu
    show ratVal (T a b) (c.e.symm u) = ev X.str σ U g (c.e.symm u)
    rw [← e, ratVal_fnOf hu.2]

end GlobalTheory.ChernCalc
