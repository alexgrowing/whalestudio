import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.WaveField

open PositivityTheory.RgBcC PositivityTheory.RgBcC.VC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiffOn_clm_apply {M V : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup V] [NormedSpace ℂ V] {s : Set M} {B : M → (V →L[ℂ] V)} {f : M → V}
    (hB : ContDiffOn ℝ ∞ B s) (hf : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞ (fun x => B x (f x)) s := by
  have hL : ContDiffOn ℝ ∞ (fun x => (B x).restrictScalars ℝ) s :=
    (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).contDiff.comp_contDiffOn hB
  exact hL.clm_apply hf

theorem deriv_clm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (B : V →L[ℂ] V) {h : ℝ → V} (hh : Differentiable ℝ h) (s : ℝ) :
    deriv (fun r => B (h r)) s = B (deriv h s) :=
  ((B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hh s).hasDerivAt).deriv

theorem iteratedDeriv_two_clm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (B : V →L[ℂ] V) {f : ℝ → V} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    iteratedDeriv 2 (fun s => B (f s)) t = B (iteratedDeriv 2 f t) := by
  have h1 : Differentiable ℝ f := hf.differentiable (by simp)
  have h2 : Differentiable ℝ (deriv f) :=
    (contDiff_infty_iff_deriv.1 hf).2.differentiable (by simp)
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have : deriv (fun s => B (f s)) = fun s => B (deriv f s) := funext (deriv_clm B h1)
  rw [this, deriv_clm B h2, iteratedDeriv_succ, iteratedDeriv_one]

theorem waveA : WaveA := by
  intro hGF n E W₁ W₂ hW A u hA hQ hu hN
  obtain ⟨hs, hce, heq, hd0⟩ := hu
  have hline : ∀ g ∈ GLs n, ContDiff ℝ ∞ (fun s => u s g) := by
    intro g hg
    have hc : ContDiff ℝ ∞ (fun s : ℝ => (s, g)) := contDiff_id.prodMk contDiff_const
    exact contDiffOn_univ.1 (hs.comp hc.contDiffOn fun s _ => ⟨trivial, hg⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => A p.2) (Set.univ ×ˢ GLs n) :=
      hA.1.comp contDiff_snd.contDiffOn fun p hp => hp.2
    exact contDiffOn_clm_apply h1 hs
  · intro t
    refine ⟨contDiffOn_clm_apply hA.1 (hce t).1, fun g hg k => ?_⟩
    show A (g * k.1) (u t (g * k.1)) = E.ρ k⁻¹ (A g (u t g))
    rw [(hce t).2 g hg k, hA.2 g hg k]
    simp only [ContinuousLinearMap.mul_apply]
    have : E.ρ k (E.ρ k⁻¹ (u t g)) = u t g := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul]; simp
    rw [this]
  · intro t g hg
    rw [iteratedDeriv_two_clm (A g) (hline g hg), heq t g hg]
    have hG := fun s => hGF n E.V W₁ W₂ hW A (u t) hA.1 (hce t).1 hQ (hN t) s 2 g hg
    simp only [Om, Pi.smul_apply, Pi.add_apply, hG, map_smul, map_add]
  · intro g hg
    rw [deriv_clm (A g) ((hline g hg).differentiable (by simp)), hd0 g hg, map_zero]

end GlobalTheory.CompanionTheory.WaveField
