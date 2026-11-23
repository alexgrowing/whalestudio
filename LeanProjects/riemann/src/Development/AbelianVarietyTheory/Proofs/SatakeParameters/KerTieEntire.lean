import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DifferentiableSumU

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerTieEntire

theorem kerTie_entire : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ, ∀ i < D.R.m, ∀ c c', Differentiable ℂ ((t.O u μ).Th i c c') := by
  intro D L hT Gi Gl K Y cX ex t u μ i _ c c'
  have hEven : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add (D.R.t_odd.add_one.mul_left j)
  have hAdm : TaylorLogMetric.admitted D _ _ ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1 :=
    ⟨hEven i, hEven (i + 1), ((t.O u μ).lat i c).2, ((t.O u μ).lat (i + 1) c').2⟩
  rw [t.O_lat u μ i c, t.O_lat u μ (i + 1) c'] at hAdm
  rw [t.O_Th u μ i c c']
  have hF := GlobalTheory.KerFinEntire.kerFin_entire D t.X t.seam t.cc t.δ t.B t.χ t.cD t.seam_ok t.cc_ok t.δ_ok t.χ_ok _ _
    ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c') hAdm (t.rd u μ).SS (t.rd u μ).lev ((t.rd u μ).Xi i c c')
  let T : TaylorLogMetric.VC D (D.R.N i) (D.R.N (i + 1)) →L[ℂ] VCx t.X.Tau (D.R.N i) (D.R.N (i + 1)) :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (t.seam.iT τ)
  exact hF.comp T.differentiable

end GlobalTheory.KerTieEntire
