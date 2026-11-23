import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelFinitePointMemSpanRationalFormLifts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFourth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom
open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_finitePoint_mem_span_rationalFormLifts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ h ∈ GfC (Vc D i), ∀ (w : (R.cV i).W) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (fun g : GA D (Wc D i) => thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w))) ∈ Submodule.span ℂ (Set.range fun x₀ : A.fam.amb.FL i t => (R.thF i t (jVx R i t x₀) (fun ρ => u ρ) : GA D (Wc D i) → ℂ)) := by
  first | exact @GlobalTheory.KernelSpanCore.kernel_mem_span_core | exact GlobalTheory.KernelSpanCore.kernel_mem_span_core | (intros; apply GlobalTheory.KernelSpanCore.kernel_mem_span_core <;> assumption)
