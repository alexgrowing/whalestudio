import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamilyMetricsSmooth
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry MeasureTheory GlobalTheory.ChernReg GlobalTheory.ShFam GlobalTheory.CxPts Filter Topology

namespace GlobalTheory.HodgeChgCont

open GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Toroidal
open scoped ContDiff

theorem continuousOn_psi_chart : ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) (i : Fin O.N)
    (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (y : GlobalTheory.TrueGeo.Pts (O.var c) σ), y ∈ ch.e.source → y ∈ offBd O.Φ c σ →
    ∃ U ∈ 𝓝 (ch.e y), ContinuousOn (GlobalTheory.HeightParts.psi O x c σ τ i ∘ ch.e.symm) U := by
  intro D O x c σ τ i ch y hy hyb
  have hS : IsOpen (offBd O.Φ c σ) := by
    have := isOpen_not_liesIn (p := (O.var c).str) (σ := σ) ⟨(O.Φ.C c).π ⁻¹' (genBd O.s.T.Z : Set _),
      (genBd O.s.T.Z).isClosed.preimage (O.Φ.C c).π.continuous⟩
    exact this
  have hl : ∀ n, ((O.var c).an σ).SmoothOn (offBd O.Φ c σ)
      (lnRatio (metsOf x O.Φ c none σ n) (refMet x O.Φ c σ n)) := fun n => by
    have h := GlobalTheory.metsOf_smooth D _ _ _ _ _ _ x O.Φ c σ n
    refine GlobalTheory.HodgeChgSmooth.smoothOn_lnRatio h.2.2 ⟨fun _ _ => h.2.1.1 (Set.mem_univ _), fun g => ?_⟩
    exact (h.2.1.2 g).mono (Set.inter_subset_inter_left _ (Set.subset_univ _))
  refine ⟨ch.e.target ∩ ch.e.symm ⁻¹' offBd O.Φ c σ, (GlobalTheory.ChartGlue.isOpen_over ch.e hS).mem_nhds
    (GlobalTheory.ChartGlue.mem_over ch.e hy hyb), ?_⟩
  have hc : ContDiffOn ℝ ∞ (GlobalTheory.HeightParts.psi O x c σ τ i ∘ ch.e.symm)
      (ch.e.target ∩ ch.e.symm ⁻¹' offBd O.Φ c σ) := by
    have := (contDiffOn_const (c := (2 : ℝ))).mul (ContDiffOn.sum (s := Finset.univ) fun r _ =>
      (contDiffOn_const (c := fund τ i r.1 r.2)).mul ((hl (rootExp _ r)).chart hS ch))
    refine this.congr fun v _ => ?_
    simp [GlobalTheory.HeightParts.psi, phW, refMet]
  exact hc.continuousOn

end GlobalTheory.HodgeChgCont
