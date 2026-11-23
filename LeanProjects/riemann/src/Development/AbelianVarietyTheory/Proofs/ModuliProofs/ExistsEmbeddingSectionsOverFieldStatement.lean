import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEmbeddingSectionsOverField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_embeddingSections_over_field : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (K : Type) [Field K] (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (w : Ix g (N' ^ 2) → K), m ^ 2 ∣ N' → 2 ≤ m → t.HasTh (𝟙 _) w → ∃ (σ : Ix g (N' ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 _)))), t.Emb m (Over.mk (𝟙 _)) σ ∧ ProjRep (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ := by
  first | exact @GlobalTheory.ZM.EmbField.exists_emb_field | exact GlobalTheory.ZM.EmbField.exists_emb_field | (intros; apply GlobalTheory.ZM.EmbField.exists_emb_field <;> assumption)
