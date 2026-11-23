import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Uniq

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : GLs n = (fun g : Mat n => g.det) ⁻¹' {0}ᶜ := rfl
  rw [this]
  exact isOpen_compl_singleton.preimage (Continuous.matrix_det continuous_id)

section Rd

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem rd_congr (X : Mat n) {f f' : Mat n → V} (h : ∀ y ∈ GLs n, f y = f' y) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X f g = Rd X f' g := by
  have e : f =ᶠ[𝓝 g] f' := Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg) h
  simp only [Rd, e.fderiv_eq]

theorem rd_sub (X : Mat n) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (f - f') g = Rd X f g - Rd X f' g := by
  have ho := isOpen_GLs.mem_nhds hg
  have d1 : DifferentiableAt ℝ f g := (hf.contDiffAt ho).differentiableAt (by simp)
  have d2 : DifferentiableAt ℝ f' g := (hf'.contDiffAt ho).differentiableAt (by simp)
  have e := (d1.hasFDerivAt.sub d2.hasFDerivAt).fderiv
  exact DFunLike.congr_fun e (g * X)

theorem rd_rd_sub (hR : RCalc) (X Y : Mat n) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (Rd Y (f - f')) g = Rd X (Rd Y f) g - Rd X (Rd Y f') g := by
  rw [rd_congr X (f' := Rd Y f - Rd Y f') (fun y hy => rd_sub Y hf hf' hy) hg]
  exact rd_sub X (((hR n).1 V f hf).1 Y) (((hR n).1 V f' hf').1 Y) hg

theorem om_sub (hO : OmFormula) (hR : RCalc) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) {g : Mat n} (hg : g ∈ GLs n) : Om (f - f') g = Om f g - Om f' g := by
  have hs : ContDiffOn ℝ ∞ (f - f') (GLs n) := hf.sub hf'
  rw [hO n V _ hs g hg, hO n V f hf g hg, hO n V f' hf' g hg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [rd_rd_sub hR _ _ hf hf' hg, rd_rd_sub hR _ _ hf hf' hg]
  abel

end Rd

theorem wave_line {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u) {g : Mat n} (hg : g ∈ GLs n) :
    ContDiff ℝ ∞ (fun s => u s g) := by
  have h := hu.1.comp (contDiff_prodMk_left (𝕜 := ℝ) (n := ∞) g).contDiffOn (s := Set.univ)
    (fun s _ => ⟨trivial, hg⟩)
  exact contDiffOn_univ.1 h

theorem wave_sub (hO : OmFormula) (hR : RCalc) {E : KMod n} {u u' : ℝ → Mat n → E.V} (hu : IsWave E u)
    (hu' : IsWave E u') : IsWave E (fun t => u t - u' t) := by
  refine ⟨hu.1.sub hu'.1, fun t => ⟨(hu.2.1 t).1.sub (hu'.2.1 t).1, fun g hg k => ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · show u t (g * k.1) - u' t (g * k.1) = E.ρ k⁻¹ (u t g - u' t g)
    rw [(hu.2.1 t).2 g hg k, (hu'.2.1 t).2 g hg k, map_sub]
  · have l := wave_line hu hg
    have l' := wave_line hu' hg
    have e : (fun s => (u s - u' s) g) = (fun s => u s g) - (fun s => u' s g) := rfl
    rw [e, iteratedDeriv_sub (contDiff_infty.1 l 2).contDiffAt (contDiff_infty.1 l' 2).contDiffAt,
      om_sub hO hR (hu.2.1 t).1 (hu'.2.1 t).1 hg, hu.2.2.1 t g hg, hu'.2.2.1 t g hg]
  · have d := (wave_line hu hg).differentiable (by simp)
    have d' := (wave_line hu' hg).differentiable (by simp)
    have e : (fun s => (u s - u' s) g) = (fun s => u s g) - (fun s => u' s g) := rfl
    rw [e, deriv_sub (d 0) (d' 0), hu.2.2.2 g hg, hu'.2.2.2 g hg, sub_zero]

end Uniq

theorem waveUniq : WaveUniq := by
  intro hS hC hR n E u u' hu hu' h0 t x hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hO, -, -⟩ := hC
  obtain ⟨c, hc⟩ := hS n
  have h := hc E _ (Uniq.wave_sub hO hR hu hu') t x hx (fun y hy _ => by
    have hxy : x * y ∈ GLs n := by
      show (x * y).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero hx hy
    exact sub_eq_zero.2 (h0 _ hxy))
  exact sub_eq_zero.1 h

end GlobalTheory.CompanionTheory.KerFc
