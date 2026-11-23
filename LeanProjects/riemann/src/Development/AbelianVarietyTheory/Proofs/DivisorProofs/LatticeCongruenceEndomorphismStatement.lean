import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceEndomorphism
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_congruence_endomorphism : ∀ (D : D7) (V : HSp D) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ (N : ℕ), 0 < N → ∀ κ : GA D V, FinCong V 1 κ → ∃ γ₀ : La →ₗ[𝓞 D.host.E] La, ∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι (γ₀ a)) = N • w := by
  first | exact @GlobalTheory.GeoLevel.exists_endo_approx | exact GlobalTheory.GeoLevel.exists_endo_approx | (intros; apply GlobalTheory.GeoLevel.exists_endo_approx <;> assumption)
