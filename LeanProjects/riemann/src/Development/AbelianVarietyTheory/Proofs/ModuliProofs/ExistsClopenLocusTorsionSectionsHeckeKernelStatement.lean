import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_clopen_locus_torsionSections_heckeKernel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over S) ⟶ o.t.G)), admitted l 𝔓 p → (∀ j, σ j ^ p ^ 2 = 1) → ∃ V : S.Opens, IsClosed (V : Set S) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), Set.range x ⊆ V ↔ (Function.Injective fun j => x ≫ (σ j).left) ∧ ∃ C : Subgroup (Over.mk x ⟶ o.t.G), (C : Set _) = Set.range (fun j => toUnit (Over.mk x) ≫ σ j) ∧ o.t.HeckeKer (Over.mk x) D 𝔓 p i C := by
  first | exact @GlobalTheory.exists_clopen_heckeKer_iff | exact GlobalTheory.exists_clopen_heckeKer_iff | (intros; apply GlobalTheory.exists_clopen_heckeKer_iff <;> assumption)
