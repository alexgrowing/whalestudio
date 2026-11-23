import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightGreenContinuousOffBoundary
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry MeasureTheory GlobalTheory.ChernReg GlobalTheory.ShFam GlobalTheory.CxPts Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_green_continuous_off_boundary : ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) (i : Fin O.N)
    (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (y : GlobalTheory.TrueGeo.Pts (O.var c) σ), y ∈ ch.e.source → y ∈ offBd O.Φ c σ →
    ∃ U ∈ 𝓝 (ch.e y), ContinuousOn (GlobalTheory.HeightParts.psi O x c σ τ i ∘ ch.e.symm) U := by
  first | exact @GlobalTheory.HodgeChgCont.continuousOn_psi_chart | exact GlobalTheory.HodgeChgCont.continuousOn_psi_chart | (intros; apply GlobalTheory.HodgeChgCont.continuousOn_psi_chart <;> assumption)
