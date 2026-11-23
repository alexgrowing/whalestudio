import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelSchemeUniversalReducedBases
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeKernelScheme_universal_reduced_bases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), admitted l 𝔓 p → ∃ Z : KerScheme Xo 𝔓 p i, EtSet Z.o₁.t.G Z.K := by
  first | exact @GlobalTheory.HkFam.exists_kerScheme | exact GlobalTheory.HkFam.exists_kerScheme | (intros; apply GlobalTheory.HkFam.exists_kerScheme <;> assumption)
