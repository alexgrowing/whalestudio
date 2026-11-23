import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ExValCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.OneOf
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DifferentiableSchwartzTranslate
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.HmEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.IsRealComp

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.dLDer :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D), DLDer O W := by
  intro F E _ _ _ _ _ _ _ D O W Y hY
  have hOne : ∀ t, One F (ex Y t) := by
    intro t
    refine oneOf F E D (ex Y t) fun w => ?_
    rw [(exPar E Y).2.2.2.1 hY t]
    simp
  have hL : ∀ (s : ℝ) (ψ : S4 F) (u : V4 F),
      (W.L (infGL E 2 (ex Y s)) ψ).1 u = ψ.1 (D.act (infGL E 2 (ex Y s))⁻¹ u) := by
    intro s ψ u
    have h1 : nu F (infGL E 2 (ex Y s)) = 1 := hOne s
    rw [W.L_apply, h1]
    have h2 : ab (1 : (A F)ˣ) = 1 := by simp [ab]
    rw [h2]
    simp
  refine ⟨hOne, fun φ t v => ?_⟩
  set v' : V4 F := D.act (infGL E 2 (ex Y t))⁻¹ v with hv'
  obtain ⟨x, x', hx0, hx, hact, hH⟩ := vfDer F E D Y v'
  have h0 : HasDerivAt (fun s => φ.1 fun i => v' i + TR.sInf F (x s i))
      ((O.dL D Y φ).1 v') 0 := by
    have h := sDiff F O φ v' x x' hx0 hx
    rwa [vfOps F E D O Y hY v' x' hH φ] at h
  have hshift : ∀ s, (W.L (infGL E 2 (ex Y (t + s))) φ).1 v =
      φ.1 fun i => v' i + TR.sInf F (x s i) := by
    intro s
    rw [(exPar E Y).1 t s, map_mul, map_mul]
    change (W.L (infGL E 2 (ex Y t)) (W.L (infGL E 2 (ex Y s)) φ)).1 v = _
    rw [hL t, hL s, hact s]
  have h1 : HasDerivAt (fun s => (W.L (infGL E 2 (ex Y (t + s))) φ).1 v)
      ((O.dL D Y φ).1 v') 0 := by
    simpa only [hshift] using h0
  have h2 : HasDerivAt (fun s => (W.L (infGL E 2 (ex Y (t + (s - t)))) φ).1 v)
      ((O.dL D Y φ).1 v') t :=
    HasDerivAt.comp_sub_const t t (by simpa using h1)
  rw [hL t (O.dL D Y φ) v]
  simpa only [add_sub_cancel] using h2
