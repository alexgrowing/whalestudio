import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameEqLocalFunctionUnitScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionLocalFunctionContinuousOnHolomorphicChartStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem continuous_val_mul_conj (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p)
    (a b : ℤ) (σ : k →+* ℂ) (f : X.functionField) (hf : f ∈ P.H a b) (g : X.functionField) (hg : g ∈ P.H a b) :
    Continuous fun y : CxPts p σ => val P a b σ y f * (starRingEnd ℂ) (val P a b σ y g) := by
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  set i := pick (P.L.φ σ).isLB y₀
  set j := pick (P.A.φ σ).isLB y₀
  have hi : y₀ ∈ ptsIn p σ (P.L.B.U i) := mem_pick _ y₀
  have hj : y₀ ∈ ptsIn p σ (P.A.B.U j) := mem_pick _ y₀
  have hW : IsOpen (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j)) := (isOpen_ptsIn _).inter (isOpen_ptsIn _)
  have hWn := hW.mem_nhds ⟨hi, hj⟩
  have hrf : ContinuousAt (fun y : CxPts p σ => ratVal (P.loc a b f i j) y) y₀ :=
    (GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart k X p P a b σ f hf i j).1.continuousAt hWn
  have hrg : ContinuousAt (fun y : CxPts p σ => ratVal (P.loc a b g i j) y) y₀ :=
    (GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart k X p P a b σ g hg i j).1.continuousAt hWn
  have hφ : ContinuousAt ((P.L.φ σ).φ i) y₀ := CInfAt.continuousAt (P.L.cInf σ i y₀ hi)
  have hψ : ContinuousAt ((P.A.φ σ).φ j) y₀ := CInfAt.continuousAt (P.A.cInf σ j y₀ hj)
  have he : ContinuousAt (fun y : CxPts p σ =>
      ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ)) y₀ :=
    Complex.continuous_ofReal.continuousAt.comp (Real.continuous_exp.continuousAt.comp
      (((continuousAt_const.mul hφ).add (continuousAt_const.mul hψ)).neg.div_const 2))
  have hF : ContinuousAt (fun y : CxPts p σ =>
      ratVal (P.loc a b f i j) y * ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ) *
        (starRingEnd ℂ) (ratVal (P.loc a b g i j) y *
          ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ))) y₀ :=
    (hrf.mul he).mul (Complex.continuous_conj.continuousAt.comp (hrg.mul he))
  refine hF.congr ?_
  filter_upwards [hWn] with y hy
  obtain ⟨θ, hθ, hv⟩ := GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P a b σ y i j hy.1 hy.2
  have h1 : θ * (starRingEnd ℂ) θ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hθ]; simp
  rw [hv f hf, hv g hg]
  generalize ratVal (P.loc a b f i j) y * ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ) = A
  generalize ratVal (P.loc a b g i j) y * ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ) = B
  rw [map_mul]
  linear_combination (-(A * (starRingEnd ℂ) B)) * h1

theorem nu_eq_sqrt {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    P.nu a b σ y f = Real.sqrt ((val P a b σ y f * (starRingEnd ℂ) (val P a b σ y f)).re) := by
  rw [← norm_val, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem continuous_val_and_bounded : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (a b : ℤ),
      (∀ (σ : k →+* ℂ), ∀ f ∈ P.H a b, ∀ g ∈ P.H a b,
        Continuous fun y : CxPts p σ => val P a b σ y f * (starRingEnd ℂ) (val P a b σ y g)) ∧
      ∀ f ∈ P.H a b, (∀ σ, Continuous fun y : CxPts p σ => P.nu a b σ y f) ∧
        ∃ C : ℝ, ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y f ≤ C := by
  intro k _ X _ p D hX P a b
  refine ⟨fun σ f hf g hg => continuous_val_mul_conj k X p P a b σ f hf g hg, fun f hf => ?_⟩
  have hc : ∀ σ, Continuous fun y : CxPts p σ => P.nu a b σ y f := fun σ => by
    simp_rw [nu_eq_sqrt]
    exact Real.continuous_sqrt.comp (Complex.continuous_re.comp (continuous_val_mul_conj k X p P a b σ f hf f hf))
  refine ⟨hc, ?_⟩
  have hb : ∀ σ : k →+* ℂ, ∃ C : ℝ, ∀ y : CxPts p σ, P.nu a b σ y f ≤ C := fun σ => by
    haveI := hX.compactSpace σ
    obtain ⟨C, hC⟩ := (isCompact_range (hc σ)).bddAbove
    exact ⟨C, fun y => hC ⟨y, rfl⟩⟩
  choose C hC using hb
  haveI := hX.finite_emb
  obtain ⟨M, hM⟩ := (Set.finite_range C).bddAbove
  exact ⟨M, fun σ y => (hC σ y).trans (hM ⟨σ, rfl⟩)⟩

end GlobalTheory.HSAmp
