import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonarchimedeanNormBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonarchimedean_norm_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (t : SAB H (Sp k)) (t' : SAB H (Sp k')) (n : SABMap t' t (spMap i)) (m : ℕ) (x : Fin m → (epsR k ⟶ t.G)) (x' : Fin m → (epsR k' ⟶ t'.G)) (𝔭 : HeightOneSpectrum (𝓞 k)) (𝔓 : HeightOneSpectrum (𝓞 k')) (ε : ℕ) (r : ℝ), Indep x → (∀ a, IsVecOver i n.φ (x a) (x' a)) → (∀ z : k, 𝔓.valuation k' (i z) = 𝔭.valuation k z ^ ε) → EigenvectorLieDegree.IsLocOrd t.G x 𝔭 r → EigenvectorLieDegree.IsLocOrd t'.G x' 𝔓 (ε * r) := by
  first | exact @GlobalTheory.LocOrdUp.isLocOrd_up | exact GlobalTheory.LocOrdUp.isLocOrd_up | (intros; apply GlobalTheory.LocOrdUp.isLocOrd_up <;> assumption)
