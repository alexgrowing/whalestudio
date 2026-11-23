import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousPeriodLatticeBasisArc
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLatticeBasisPunctPolydiscCoverPStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_period_lattice_basis_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (g' : ℕ) (ρ : ℝ) (e' : ∀ u, (Fin g' → ℂ) → (Over.mk (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G)), GoodEmb c σ → 1 ≤ Dw.p + Dw.q → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ∀ s, (spMap (ψ u) ≫ x) s ∉ genBd Z) → 0 < ρ → ρ ≤ r → IsHolTo (Metric.ball (0 : ℂ) ρ ×ˢ Set.univ) (fun q : ℂ × (Fin g' → ℂ) => (show Sp ℂ ⟶ Z.t.G.left from (e' q.1 q.2).left)) → (∀ u ∈ Metric.ball (0 : ℂ) ρ, (∀ z w, e' u (z + w) = e' u z * e' u w) ∧ Function.Surjective (e' u) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (e' u z).left)) ∧ (∀ w, ∃! v : epsPt (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G, IsDerivAt0 (fun z => (e' u z).left) w v.left) ∧ (∀ v : epsPt (spMap (ψ u) ≫ x ≫ genι Z) ⟶ Z.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' u 0).left → ∃! w, IsDerivAt0 (fun z => (e' u z).left) w v.left)) → ∃ (ρ₀ : ℝ) (m : ℕ) (lamE : ℂ → Fin m → Fin g' → ℂ), 0 < ρ₀ ∧ ρ₀ < ρ ∧ ContinuousOn lamE {s : ℂ | s.re < 0} ∧ (∀ s : ℂ, s.re < 0 → LinearIndependent ℝ (lamE s) ∧ Submodule.span ℝ (Set.range (lamE s)) = ⊤ ∧ ∀ z, e' ((ρ₀ : ℂ) * Complex.exp s) z = 1 ↔ ∃ n : Fin m → ℤ, z = ∑ j, n j • lamE s j) ∧ ∃ (C : ℝ) (k : ℕ), ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ Real.pi → ‖lamE s‖ ≤ C * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.ShFam.BdArc.ArcLat.exists_continuous_latBasis_of_arc | exact GlobalTheory.ShFam.BdArc.ArcLat.exists_continuous_latBasis_of_arc | (intros; apply GlobalTheory.ShFam.BdArc.ArcLat.exists_continuous_latBasis_of_arc <;> assumption)
