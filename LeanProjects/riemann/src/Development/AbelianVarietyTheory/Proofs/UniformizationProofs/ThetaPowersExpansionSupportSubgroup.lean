import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpansionSectionLineBundlePower
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductSupportInSubgroupThetaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_mul_pow_sec {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Y ⟶ X) (k l : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (k : ℤ))))
    (t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (l : ℤ)))) :
    ∃ u : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => ((k + l : ℕ) : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval u r z J = sval s r z J * sval t r z J := by
  obtain ⟨u, hu⟩ := exists_sec hL (φ' := fun _ : Fin 1 => p) (ε' := fun _ => ((k + l : ℕ) : ℤ))
    (fun U _ h => by simp [Fintype.prod_sum_type, zpow_add]) (H1.SectionArithmetic.mulSec s t)
  exact ⟨u, fun Z r z J hJ => (hu Z r z J hJ).trans (H1.SectionArithmetic.sval_mulSec s t r z hJ)⟩

theorem exists_pow_exp_supp : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (Λ : AddSubgroup D.X) (θ : U.SecGT (𝟙_ _) 1) f, U.ExpT (𝟙_ _) 1 θ f → (∀ α ∉ Λ, ∀ j, (f α).f j = 0) → ∀ l : ℕ, 1 ≤ l → ∃ (σ : U.SecGT (𝟙_ _) l) (g : ∀ α, SecBT D (𝟙_ _) l α), U.ExpT (𝟙_ _) l σ g ∧ (∀ α ∉ Λ, ∀ j, (g α).f j = 0) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ r z J = sval θ r z J ^ l) := by
  intro h₁ h₂ V _ _ _ hV D A G _ _ U Λ θ f hθ hf l hl
  induction l, hl using Nat.le_induction with
  | base => exact ⟨θ, f, hθ, hf, fun Z r z J _ => (pow_one _).symm⟩
  | succ l hl ih =>
    obtain ⟨σ, g, hσ, hg, hv⟩ := ih
    obtain ⟨u, hu⟩ := exists_mul_pow_sec U.P.L.isLB _ l 1 σ θ
    obtain ⟨g', hg'⟩ := GlobalTheory.BaseExpansionExists.main h₁ h₂ V hV D A G U (l + 1) (Nat.le_add_left 1 l) u
    exact ⟨u, g', hg', GlobalTheory.T.product_support_in_subgroup_theta V hV D A G U Λ l 1 σ θ u g f g' hσ hθ hg' hu hg hf,
      fun Z r z J hJ => by rw [hu Z r z J hJ, hv Z r z J hJ, pow_succ]⟩

end GlobalTheory.UU
