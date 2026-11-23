import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerFinEntire

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem differentiable_opU (H : Sesq V) {F : V → ℂ} (hF : Differentiable ℂ F) (x : V) :
    Differentiable ℂ (opU H x F) := by
  have h : Differentiable ℂ fun z => H z x := (LinearMap.toContinuousLinearMap (H.flip x)).differentiable
  unfold opU
  fun_prop

theorem differentiable_sumU (H : Sesq V) (α : V → ℂ) (S : Finset V) {F : V → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (sumU H α S F) := by
  unfold sumU
  exact Differentiable.fun_sum fun x _ => (differentiable_opU H hF x).const_mul _

theorem differentiable_xiL (H : Sesq V) (α : V → ℂ) (vol : ℝ) (SX SA SB : Finset V) (Φ : V → ℂ) {e : V → ℂ}
    (he : Differentiable ℂ e) : Differentiable ℂ (xiL H α vol SX SA SB Φ e) := by
  unfold xiL xiS
  exact Differentiable.fun_sum fun x _ => (differentiable_opU H (differentiable_sumU H _ SB he) x).const_mul _

end General

theorem differentiable_thC {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}
    (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ) (Ξ : HomE E a b → ℂ) {θ : VV ι a b → ℂ}
    (hθ : Differentiable ℂ θ) : Differentiable ℂ (thC emb δ d sc AA0 SS N N' c Ξ θ) := by
  unfold thC xiV
  exact differentiable_xiL _ _ _ _ _ _ _ hθ

theorem kerFin_entire : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') → ∀ (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (c : ℕ) (Ξ : HomE X.E a b → ℂ), Differentiable ℂ (thC (X.embC (ambOf s B χ cD : Amb X).σ₀) (ambOf s B χ cD : Amb X).δ (ambOf s B χ cD : Amb X).d (ambOf s B χ cD : Amb X).sc (ambOf s B χ cD : Amb X).AA SS N N' c Ξ ((ambOf s B χ cD : Amb X).e a b N N')) := by
  intro D X s cc δ B χ cD _ hcc hδ hχ a b N N' hA SS c Ξ
  have hE : Differentiable ℂ (B.eNat χ a b (s.lat N) (s.lat N')) :=
    (B.vec_mem_ne hcc hδ (Formalism.L2.Ker.KS.Lat.delta_ne hcc hδ) (B.stdOK hcc hδ) χ hχ a b _ _ hA).1.1
  let T : VCx X.Tau a b →L[ℂ] TaylorLogMetric.VC D a b := ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (s.iT.symm τ)
  have he : Differentiable ℂ ((ambOf s B χ cD : Amb X).e a b N N') := hE.comp T.differentiable
  exact differentiable_thC _ _ _ _ _ _ _ _ _ _ he

end GlobalTheory.KerFinEntire
