import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSemipositiveWeightOfGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightsDifferBySmoothFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocityFormulaLeSemipositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocityDefectIndependentFirstMetricStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem semiPosReg_of_eqOn {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {B : LB X}
    {φ ψ : Weight p σ B} {D : ℕ} (h : φ.SemiPosReg D)
    (e : ∀ i, ∀ y ∈ ptsIn p σ (B.U i), ψ.φ i y = φ.φ i y) : ψ.SemiPosReg D := by
  intro i c y hy ξ
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hm := ChartGlue.mem_over c.e hy.1 hy.2
  have ee : (fun v => (ψ.φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] (fun v => (φ.φ i (c.e.symm v) : ℂ)) :=
    Filter.eventually_of_mem (ho.mem_nhds hm) fun v hv => by simp only [e i _ hv.2]
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr ee]
  exact h i c y hy ξ

theorem exists_addFn_semiPosReg {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    (M : MLine p σ) (D : ℕ) (hg : ∃ (n : ℕ) (u : Fin n → M.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) :
    ∃ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), (M.addFn u hu).φ.SemiPosReg D := by
  obtain ⟨ψ, hψ, hψp⟩ := GlobalTheory.T.exists_smooth_semipositive_weight_of_generated k X p σ M.B M.φ.isLB hg
  obtain ⟨u, hu, he⟩ := GlobalTheory.T.smooth_weights_differ_by_smooth_function k X p σ M.B M.φ ψ M.cInf hψ
  exact ⟨u, hu, semiPosReg_of_eqOn (hψp D) fun i y hy => (he i y hy).symm⟩

end GlobalTheory.Mix

theorem GlobalTheory.Mix.side_eq_of_generated : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∀ i, (L i).φ.SemiPosReg (e + 1)) → (∃ (n : ℕ) (u : Fin n → M.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → (∃ (n : ℕ) (u : Fin n → N.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP F _ X _ _ p σ e hproj hdim L M N s hs t ht hz hL hgM hgN
  obtain ⟨u, hu, hMu⟩ := GlobalTheory.Mix.exists_addFn_semiPosReg M (e + 1) hgM
  obtain ⟨v, hv, hNv⟩ := GlobalTheory.Mix.exists_addFn_semiPosReg N (e + 1) hgN
  have hz' : ∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus t ∨ z ∈ nonzeroLocus s := fun z h => (hz z h).symm
  have h1 := GlobalTheory.T.reciprocityDefect_independent_firstMetric hP F X p σ e hproj hdim L M N s hs t ht hz u hu
  have h2 := GlobalTheory.T.reciprocityDefect_independent_firstMetric hP F X p σ e hproj hdim L N (M.addFn u hu) t ht s hs hz' v hv
  have h3 := GlobalTheory.T.reciprocityFormula_le_semipositive hP F X p σ e hproj hdim L (M.addFn u hu) (N.addFn v hv) s hs t ht hz hL hNv
  have h4 := GlobalTheory.T.reciprocityFormula_le_semipositive hP F X p σ e hproj hdim L (N.addFn v hv) (M.addFn u hu) t ht s hs hz' hL hMu
  have d1 : divOfSec (M.addFn u hu).φ.isLB s hs = divOfSec M.φ.isLB s hs := rfl
  have d2 : divOfSec (N.addFn v hv).φ.isLB t ht = divOfSec N.φ.isLB t ht := rfl
  rw [d1, d2] at h3 h4
  rw [d1] at h2
  linarith
