import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCoordinatesModPrimeSelfDualStabilizer
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU)
open GlobalTheory.LevPull (CongMod)
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_coordinates_mod_prime_selfDual_stabilizer : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ PP : Formalism.L2.DIV.Pl D.host.E, ∃ φ : La →ₗ[𝓞 D.host.E] (Fin V.rank → kP PP), Function.Surjective φ ∧ ∀ k : GA D V, Lev.finE V k ∈ Formalism.L2.DIV.St β → ∀ M : ℕ, (M : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ a b : La, (∃ w ∈ latGHat V 1, finVec V (ι b) - (finHom V k).1.mulVec (finVec V (ι a)) = M • w) → φ b = (redFn β PP (Lev.finE V k)).1.mulVec (φ a) := by
  first | exact @GlobalTheory.LatCoordRed.coord_red | exact GlobalTheory.LatCoordRed.coord_red | (intros; apply GlobalTheory.LatCoordRed.coord_red <;> assumption)
