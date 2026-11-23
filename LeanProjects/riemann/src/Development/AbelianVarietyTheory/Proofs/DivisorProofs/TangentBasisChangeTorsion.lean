import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HtGen.DlogClose

theorem dlog_sub_norm_lt_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X) (g g' : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)) (e' : Fin g' → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)), IsTanBasis t x e → IsTanBasis t x e' → ∀ (c : TorsChar t x (p ^ 2)) (h : Fin g → ↥(intO ℂ_[p])) (h' : Fin g' → ↥(intO ℂ_[p])), DlogIs t p 2 c e h → DlogIs t p 2 c e' h' → ∀ (a : Fin g → ℂ_[p]) (a' : Fin g' → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left), IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) a w → IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e' i) a' w → w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) → ‖∑ i, (h i : ℂ_[p]) * a i - ∑ i, (h' i : ℂ_[p]) * a' i‖ < 1 := by
  intro E _ _ _ H X _ t hX p hp x g g' e e' he he' c h h' hD hD' a a' w hw hw' hL
  have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  obtain ⟨x', hx', vO, hv, hs⟩ := GlobalTheory.ShFam.Pad.HTBound.htBound E H X t p ℂ_[p] hn x
    (fun x' hx' => GlobalTheory.LineNorm.WedgeMax.ext_intO hX x x' hx') w hL p (by
      rw [hn, ← Real.rpow_neg_one]
      refine Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg ?_)
      rw [div_le_one (by linarith)]
      linarith)
  obtain rfl := GlobalTheory.LineNorm.WedgeMax.ext_intO hX x x' hx'
  obtain ⟨b, hbv, hb⟩ := GlobalTheory.HTLevel.coords he hw _ hv hs
  obtain ⟨b', hbv', hb'⟩ := GlobalTheory.HTLevel.coords he' hw' _ hv hs
  obtain ⟨u, hu⟩ := GlobalTheory.HTLevel.red_ex (Ideal.span {(p : ↥(intO ℂ_[p])) ^ 2}) hv
  have h1 := hD b vO hbv u hu
  have h2 := hD' b' vO hbv' u hu
  rw [h1, Ideal.Quotient.eq] at h2
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h2
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have h3 : ∑ i, (h i : ℂ_[p]) * a i - ∑ i, (h' i : ℂ_[p]) * a' i = (r : ℂ_[p]) * p := by
    apply mul_left_cancel₀ hp0
    have := congrArg (intO ℂ_[p]).subtype hr
    simp only [map_mul, map_pow, map_natCast, map_sum, map_sub, Subring.subtype_apply, hb, hb'] at this
    have e1 : ∑ i, (h i : ℂ_[p]) * ((p : ℂ_[p]) * a i) = (p : ℂ_[p]) * ∑ i, (h i : ℂ_[p]) * a i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, (h' i : ℂ_[p]) * ((p : ℂ_[p]) * a' i) = (p : ℂ_[p]) * ∑ i, (h' i : ℂ_[p]) * a' i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2] at this
    linear_combination (-1 : ℂ_[p]) * this
  rw [h3, norm_mul, hn]
  have hr1 : ‖(r : ℂ_[p])‖ ≤ 1 := r.2
  have hpi : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  calc ‖(r : ℂ_[p])‖ * (p : ℝ)⁻¹ ≤ 1 * (p : ℝ)⁻¹ := by gcongr
    _ < 1 := by rw [_root_.one_mul]; exact hpi

end GlobalTheory.HtGen.DlogClose
