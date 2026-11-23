import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverse
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

theorem UpperTheory.tangent_basis_change_torsion_character :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (p : ℕ) [Fact p.Prime] (n : ℕ) (x : Sp ↥(intO ℂ_[p]) ⟶ X) (g g' : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)) (e' : Fin g' → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)), IsTanBasis t x e → IsTanBasis t x e' → ∀ (χ : TorsChar t x (p ^ n)) (h : Fin g → ↥(intO ℂ_[p])) (h' : Fin g' → ↥(intO ℂ_[p])), DlogIs t p n χ e h → DlogIs t p n χ e' h' → ∀ (a : Fin g → ℂ_[p]) (a' : Fin g' → ℂ_[p]) (w : (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)), IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) a w → IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e' i) a' w → ∀ s : ℂ_[p], (∀ i, ‖s * a i‖ ≤ 1) → ‖s * (∑ i, (h i : ℂ_[p]) * a i - ∑ i, (h' i : ℂ_[p]) * a' i)‖ ≤ (p : ℝ)⁻¹ ^ n := by
  intro E _ _ _ H X t p hp n x g g' e e' he he' c h h' hD hD' a a' w hw hw' s hsa
  have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]
  let b₀ : Fin g → ↥(intO ℂ_[p]) := fun i => ⟨s * a i, hsa i⟩
  obtain ⟨vO, hv, hbv₀⟩ := Guard.exists_comb he.1 b₀
  have heC := fun j => GlobalTheory.FactorDepth.isTanAtG_map t (intO ℂ_[p]).subtype (he.1 j)
  have hs : spMap (dualMap (intO ℂ_[p]).subtype) ≫ vO = spMap (epsMul s) ≫ w :=
    Guard.comb_unique heC (GlobalTheory.LatDRFree.comb_map t (intO ℂ_[p]).subtype hbv₀) (Guard.comb_smul heC hw s)
  obtain ⟨b, hbv, hb⟩ := GlobalTheory.HTLevel.coords he hw _ hv hs
  obtain ⟨b', hbv', hb'⟩ := GlobalTheory.HTLevel.coords he' hw' _ hv hs
  obtain ⟨u, hu⟩ := GlobalTheory.HTLevel.red_ex (Ideal.span {(p : ↥(intO ℂ_[p])) ^ n}) hv
  have h1 := hD b vO hbv u hu
  have h2 := hD' b' vO hbv' u hu
  rw [h1, Ideal.Quotient.eq] at h2
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h2
  have h3 : s * (∑ i, (h i : ℂ_[p]) * a i - ∑ i, (h' i : ℂ_[p]) * a' i) = (r : ℂ_[p]) * (p : ℂ_[p]) ^ n := by
    have := congrArg (intO ℂ_[p]).subtype hr
    simp only [map_mul, map_pow, map_natCast, map_sum, map_sub, Subring.subtype_apply, hb, hb'] at this
    have e1 : ∑ i, (h i : ℂ_[p]) * (s * a i) = s * ∑ i, (h i : ℂ_[p]) * a i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, (h' i : ℂ_[p]) * (s * a' i) = s * ∑ i, (h' i : ℂ_[p]) * a' i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2] at this
    linear_combination (-1 : ℂ_[p]) * this
  rw [h3, norm_mul, norm_pow, hn]
  have hr1 : ‖(r : ℂ_[p])‖ ≤ 1 := r.2
  exact mul_le_of_le_one_left (by positivity) hr1
