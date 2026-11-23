import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralAdelicCoordinatesLatticeMod
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_adelic_coordinates_lattice_mod : ∀ (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)), LatticeBasisLifts.IsLatBasis V hr β → ∀ (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ M : ℕ, 0 < M → ∃ ρ : La →+ (Fin r → LatticeBasisLifts.OAf D), (∀ (b : 𝓞 D.host.E) (a : La), ρ (b • a) = Formalism.L2.DIV.oToS D.host.F D.host.E b • ρ a) ∧ (∀ s : Fin r → LatticeBasisLifts.OAf D, ∃ (a : La) (s' : Fin r → LatticeBasisLifts.OAf D), s = ρ a + M • s') ∧ (∀ I J : Ideal (𝓞 D.host.E), I * J = Ideal.span {(M : 𝓞 D.host.E)} → ∀ a : La, (∀ i, ρ a i ∈ Formalism.L2.DIV.idS D.host.F I) → a ∈ I • (⊤ : Submodule (𝓞 D.host.E) La)) ∧ ∀ (κ : GA D V) (y : GL (Fin r) (LatticeBasisLifts.OAf D)), LatticeBasisLifts.finR V hr κ = Formalism.L2.DIV.frGL β y → ∀ a a' : La, (∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι a') = M • w) ↔ ∃ s : Fin r → LatticeBasisLifts.OAf D, y.1.mulVec (ρ a) - ρ a' = M • s := by
  first | exact @GlobalTheory.GeoActCompare.exists_lattice_coord | exact GlobalTheory.GeoActCompare.exists_lattice_coord | (intros; apply GlobalTheory.GeoActCompare.exists_lattice_coord <;> assumption)
