import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder ComplexConjugate

noncomputable section
namespace GlobalTheory.CurveDens.FrameIndep

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem ofReal_norm_sq (w : ℂ) : ((‖w‖ : ℂ)) ^ 2 = w * conj w := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

theorem dR_conj {f : E → ℂ} {z : E} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun x => conj (f x)) z := by
  simpa using hf.star

theorem dR_ofReal {a : E → ℝ} {z : E} (ha : DifferentiableAt ℝ a z) :
    DifferentiableAt ℝ (fun x => (a x : ℂ)) z :=
  (Complex.ofRealCLM.differentiableAt.comp z ha : _)

theorem dR_normSq {f : E → ℂ} {z : E} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun x => ‖f x‖ ^ 2) z :=
  hf.norm_sq ℝ

theorem del_log {t : E → ℝ} {z : E} (ht : DifferentiableAt ℝ t z) (h0 : 0 < t z) (ξ : E) :
    del (fun x => (Real.log (t x) : ℂ)) z ξ = ((t z : ℂ))⁻¹ * del (fun x => (t x : ℂ)) z ξ := by
  rw [del_ofReal_comp (Real.hasDerivAt_log (ne_of_gt h0)) ht ξ]; push_cast; rfl

theorem dbar_log {t : E → ℝ} {z : E} (ht : DifferentiableAt ℝ t z) (h0 : 0 < t z) (ξ : E) :
    dbar (fun x => (Real.log (t x) : ℂ)) z ξ = ((t z : ℂ))⁻¹ * dbar (fun x => (t x : ℂ)) z ξ := by
  rw [dbar_ofReal_comp (Real.hasDerivAt_log (ne_of_gt h0)) ht ξ]; push_cast; rfl

theorem ofReal_congr {b c : E → ℝ} {g : E → ℂ} {z : E} (e : b =ᶠ[𝓝 z] fun x => ‖g x‖ ^ 2 * c x) :
    (fun x => (b x : ℂ)) =ᶠ[𝓝 z] fun x => g x * conj (g x) * (c x : ℂ) := by
  filter_upwards [e] with x hx
  rw [hx]; push_cast; rw [ofReal_norm_sq]

theorem del_scaled {b c : E → ℝ} {g : E → ℂ} {z : E} (hc : DifferentiableAt ℝ c z) (h0 : 0 < c z)
    (hg : DifferentiableAt ℂ g z) (hg0 : g z ≠ 0) (e : b =ᶠ[𝓝 z] fun x => ‖g x‖ ^ 2 * c x) (ξ : E) :
    del (fun x => (Real.log (b x) : ℂ)) z ξ =
      del (fun x => (Real.log (c x) : ℂ)) z ξ + del g z ξ / g z := by
  have hgR := hg.restrictScalars ℝ
  have hbD : DifferentiableAt ℝ b z := e.differentiableAt_iff.2 ((dR_normSq hgR).mul hc)
  have hz : dbar g z ξ = 0 := by rw [dbar_eq_zero hg]; rfl
  have hbz : b z = ‖g z‖ ^ 2 * c z := e.eq_of_nhds
  have hb0 : 0 < b z := by rw [hbz]; have := norm_pos_iff.2 hg0; positivity
  rw [del_log hbD hb0, del_log hc h0, del_congr (ofReal_congr e),
    del_mul (a := fun x => g x * conj (g x)) (hgR.fun_mul (dR_conj hgR)) (dR_ofReal hc), del_mul hgR (dR_conj hgR), del_conj,
    hz, hbz]
  push_cast
  rw [ofReal_norm_sq]
  have h1 : conj (g z) ≠ 0 := (map_ne_zero _).2 hg0
  have h2 : (c z : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  simp only [map_zero]
  field_simp
  ring

theorem dbar_scaled {b c : E → ℝ} {g : E → ℂ} {z : E} (hc : DifferentiableAt ℝ c z) (h0 : 0 < c z)
    (hg : DifferentiableAt ℂ g z) (hg0 : g z ≠ 0) (e : b =ᶠ[𝓝 z] fun x => ‖g x‖ ^ 2 * c x) (ξ : E) :
    dbar (fun x => (Real.log (b x) : ℂ)) z ξ =
      dbar (fun x => (Real.log (c x) : ℂ)) z ξ + conj (del g z ξ / g z) := by
  have hgR := hg.restrictScalars ℝ
  have hbD : DifferentiableAt ℝ b z := e.differentiableAt_iff.2 ((dR_normSq hgR).mul hc)
  have hz : dbar g z ξ = 0 := by rw [dbar_eq_zero hg]; rfl
  have hbz : b z = ‖g z‖ ^ 2 * c z := e.eq_of_nhds
  have hb0 : 0 < b z := by rw [hbz]; have := norm_pos_iff.2 hg0; positivity
  rw [dbar_log hbD hb0, dbar_log hc h0, dbar_congr (ofReal_congr e),
    dbar_mul (a := fun x => g x * conj (g x)) (hgR.fun_mul (dR_conj hgR)) (dR_ofReal hc), dbar_mul hgR (dR_conj hgR), dbar_conj,
    hz, hbz]
  push_cast
  rw [ofReal_norm_sq]
  have h1 : conj (g z) ≠ 0 := (map_ne_zero _).2 hg0
  have h2 : (c z : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  simp only [map_zero, map_div₀]
  field_simp
  ring

theorem del_prod {q f g : E → ℂ} {z : E} (hq : DifferentiableAt ℝ q z) (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) (ξ : E) :
    del (fun x => g x * conj (f x) * q x) z ξ =
      g z * conj (f z) * del q z ξ + del g z ξ * conj (f z) * q z := by
  have hfR := hf.restrictScalars ℝ
  have hgR := hg.restrictScalars ℝ
  have hz : dbar f z ξ = 0 := by rw [dbar_eq_zero hf]; rfl
  rw [del_mul (a := fun x => g x * conj (f x)) (hgR.fun_mul (dR_conj hfR)) hq,
    del_mul hgR (dR_conj hfR), del_conj, hz, map_zero]
  ring

theorem dbar_prod {q f g : E → ℂ} {z : E} (hq : DifferentiableAt ℝ q z) (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) (ξ : E) :
    dbar (fun x => g x * conj (f x) * q x) z ξ =
      g z * conj (f z) * dbar q z ξ + g z * conj (del f z ξ) * q z := by
  have hfR := hf.restrictScalars ℝ
  have hgR := hg.restrictScalars ℝ
  have hz : dbar g z ξ = 0 := by rw [dbar_eq_zero hg]; rfl
  rw [dbar_mul (a := fun x => g x * conj (f x)) (hgR.fun_mul (dR_conj hfR)) hq,
    dbar_mul hgR (dR_conj hfR), dbar_conj, hz]
  ring

end GlobalTheory.CurveDens.FrameIndep

open GlobalTheory.CurveDens.FrameIndep in

theorem GlobalTheory.CurveDens.angleForm_frame_indep (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (n : ℕ) (a a' a₂ a₂' : E → ℝ) (q q₂ f g : E → ℂ)
    (ξ z : E) (ha : DifferentiableAt ℝ a z) (ha' : DifferentiableAt ℝ a' z)
    (hq : DifferentiableAt ℝ q z) (ha0 : 0 < a z) (ha0' : 0 < a' z) (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) (hf0 : f z ≠ 0) (hg0 : g z ≠ 0)
    (e₂ : a₂ =ᶠ[𝓝 z] fun x => ‖f x‖ ^ 2 * a x) (e₂' : a₂' =ᶠ[𝓝 z] fun x => ‖g x‖ ^ 2 * a' x)
    (eq : q₂ =ᶠ[𝓝 z] fun x => g x * starRingEnd ℂ (f x) * q x) :
    angleForm n a₂ a₂' q₂ ξ z = angleForm n a a' q ξ z := by
  have hqz : q₂ z = g z * conj (f z) * q z := eq.eq_of_nhds
  have haz : a₂ z = ‖f z‖ ^ 2 * a z := e₂.eq_of_nhds
  have haz' : a₂' z = ‖g z‖ ^ 2 * a' z := e₂'.eq_of_nhds
  have hF : ‖f z‖ ≠ 0 := norm_ne_zero_iff.2 hf0
  have hG : ‖g z‖ ≠ 0 := norm_ne_zero_iff.2 hg0
  have hv : ‖q₂ z‖ ^ 2 / (a₂ z * a₂' z) = ‖q z‖ ^ 2 / (a z * a' z) := by
    rw [hqz, haz, haz', norm_mul, norm_mul, Complex.norm_conj]
    field_simp
  unfold angleForm
  rw [hv]
  generalize (((‖q z‖ ^ 2 / (a z * a' z)) ^ n : ℝ) : ℂ) = V
  rw [del_congr eq, dbar_congr eq, del_prod hq hf hg, dbar_prod hq hf hg,
    del_scaled ha' ha0' hg hg0 e₂', dbar_scaled ha ha0 hf hf0 e₂, hqz, haz, haz']
  push_cast
  rw [ofReal_norm_sq, ofReal_norm_sq]
  have h1 : conj (f z) ≠ 0 := (map_ne_zero _).2 hf0
  have h2 : conj (g z) ≠ 0 := (map_ne_zero _).2 hg0
  have h3 : (a z : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have h4 : (a' z : ℂ) ≠ 0 := by exact_mod_cast ha0'.ne'
  simp only [map_mul, map_sub, map_add, map_div₀, map_inv₀, Complex.conj_conj]
  generalize del (fun x => (Real.log (a' x) : ℂ)) z ξ = A
  generalize dbar (fun x => (Real.log (a x) : ℂ)) z ξ = B
  generalize del q z ξ = Q1
  generalize dbar q z ξ = Q2
  generalize del f z ξ = F1
  generalize del g z ξ = G1
  field_simp
  ring
