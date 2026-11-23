import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanNormSquareBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_norm_square_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (t : SAB H (Sp k)) (t' : SAB H (Sp k')) (n : SABMap t' t (spMap i)) (m : ℕ) (x : Fin m → (epsR k ⟶ t.G)) (x' : Fin m → (epsR k' ⟶ t'.G)) (σ : k' →+* ℂ) (N : ℝ), (∀ a, IsVecOver i n.φ (x a) (x' a)) → AdelicDegreeTameRamification.IsArchNormSq t x (σ.comp i) N → AdelicDegreeTameRamification.IsArchNormSq t' x' σ N := by
  first | exact @GlobalTheory.FlatDegreeCompare.isArchNormSq_up | exact GlobalTheory.FlatDegreeCompare.isArchNormSq_up | (intros; apply GlobalTheory.FlatDegreeCompare.isArchNormSq_up <;> assumption)
