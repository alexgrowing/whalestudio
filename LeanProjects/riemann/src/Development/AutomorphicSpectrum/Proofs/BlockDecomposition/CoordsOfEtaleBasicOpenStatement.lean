import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordsOfEtaleBasicOpen
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_of_etale_basic_open : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens}, IsAffineOpen W → ∀ (g : Γ(X, W)) {d : ℕ} (s : Fin d → Γ(X, W)), letI := (strV q W).toAlgebra; (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g)) (fun k => algebraMap Γ(X, W) (Localization.Away g) (s k)) : MvPolynomial (Fin d) K →+* Localization.Away g).Etale → ∃ c : Coord q (X.basicOpen g) d, ∀ k, c.t k = resO (X.basicOpen_le g) (s k) := by
  first | exact @GlobalTheory.CompanionTheory.GeoCoord.exists_coord_basicOpen | exact GlobalTheory.CompanionTheory.GeoCoord.exists_coord_basicOpen | (intros; apply GlobalTheory.CompanionTheory.GeoCoord.exists_coord_basicOpen <;> assumption)
