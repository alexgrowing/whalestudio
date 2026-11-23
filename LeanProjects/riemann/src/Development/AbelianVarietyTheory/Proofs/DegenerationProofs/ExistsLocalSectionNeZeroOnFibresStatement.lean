import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalSectionNeZeroOnFibres
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.exists_local_section_ne_zero_on_fibres' : ∀ (C : Core) (L : C.Law) (T : C.Theta) (Om : Set C.G.toScheme) (ν), IsOpen Om → T.Norms Om ν → L.CompanionTheory Om → (∃ (M : LB C.G.toScheme) (w : LB.Iso (M.pull C.a) T.L.L) (D : M.ι → C.A.left.Opens), M.IsLB ∧ w.IsGen ∧ (∀ i, (D i : Set C.A.left).Nonempty) ∧ ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ C.A.left) (i : M.ι) (j : T.L.L.ι), IntAt C.a (M.U i) x → Set.range x ⊆ T.L.L.U j → Set.range x ⊆ D i → ‖valF x _ (w.s (j, fun _ => i)).val‖ * ν p x j = 1) → ∃ M : LB C.G.toScheme, M.IsLB ∧ LBIso (M.pull C.a) T.L.L ∧ ∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (M.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z' := by
  first | exact @GlobalTheory.exists_local_section_ne_zero_on_fibres | exact GlobalTheory.exists_local_section_ne_zero_on_fibres | (intros; apply GlobalTheory.exists_local_section_ne_zero_on_fibres <;> assumption)
