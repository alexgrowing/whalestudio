import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpansionSectionLineBundlePower
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAdditionFactorGeneratorTransported
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullBValues
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaCoefficientsAbelianSquareStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralAdditionFormulaGroupStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AddClosure

theorem addB_of_pull {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (f₀ : ∀ α, SecBT D (𝟙_ _) 1 α) (s₀ : Raw D F 1) (r : R) {n : ℕ}
    (f f' : Fin n → ∀ α, SecBT D (𝟙_ _) 2 α) (s s' : Fin n → Raw D F 2)
    (h₀ : PullB D F (toUnit _) 1 f₀ s₀) (h : ∀ i, PullB D F (toUnit _) 2 (f i) (s i))
    (h' : ∀ i, PullB D F (toUnit _) 2 (f' i) (s' i)) (hB : AddB D (𝟙_ _) f₀ r f f') :
    AddB D (TF (R := R) F) s₀ r s s' := by
  intro T ρ x y z J hJ
  obtain ⟨h1, h2⟩ := hB T (ρ ≫ toUnit _) x y z J hJ
  have e₀ := fun α w => GlobalTheory.pullB_values R D F _ _ 1 f₀ s₀ h₀ α T ρ w z J hJ
  have e := fun i α w => GlobalTheory.pullB_values R D F _ _ 2 (f i) (s i) (h i) α T ρ w z J hJ
  have e' := fun i α w => GlobalTheory.pullB_values R D F _ _ 2 (f' i) (s' i) (h' i) α T ρ w z J hJ
  refine ⟨fun a b α β ha hb => ?_, fun α β hn => ?_⟩
  · refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ((h1 a b α β ha hb).trans ?_)
    · exact congrArg₂ (· * ·) (e i α x) (e' i β y)
    · exact congrArg _ (congrArg₂ (· * ·) (e₀ a _).symm (e₀ b _).symm)
  · refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (h2 α β hn)
    exact congrArg₂ (· * ·) (e i α x) (e' i β y)

theorem main : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s₀ : Raw D (Kbar V) 1), U.PullG (Kbar V) (toUnit _) 1 θ th → PullB D (Kbar V) (toUnit _) 1 f s₀ → ∃ (r : V) (n : ℕ) (t t' : Fin n → LB.Sec (LPow A.A A.L ((2 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s s' : Fin n → Raw D (Kbar V) 2), r ≠ 0 ∧ (∀ i, U.ExpF (Kbar V) 2 (t i) (s i) ∧ U.ExpF (Kbar V) 2 (t' i) (s' i)) ∧ AddA A (TFK (R := V) (Kbar V)) th t t' ∧ AddB D (TF (R := V) (Kbar V)) s₀ r s s') := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ th s₀ hth hs₀
  obtain ⟨r, n, σ, σ', hr, hG⟩ := GlobalTheory.T.exists_integral_addition_formula_group V hV D A G U θ
  have hexp := GlobalTheory.BaseExpansionExists.main hL hL2 V hV D A G U 2 (by norm_num)
  choose g hg using hexp
  obtain ⟨hpG, hpB⟩ := GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 2
  choose pt hpt using fun σ => (hpG σ).exists
  choose ps hps using fun f => (hpB f).exists
  have hB := GlobalTheory.T.additionFormula_coefficients_abelian_square hL.globalFns V hV D A G U θ f r n σ σ' (fun i => g (σ i)) (fun i => g (σ' i)) hG hθ.1
    (fun i => ⟨hg _, hg _⟩)
  refine ⟨r, n, fun i => pt (σ i), fun i => pt (σ' i), fun i => ps (g (σ i)), fun i => ps (g (σ' i)), hr,
    fun i => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact GlobalTheory.expF_of_pull V D _ A G U (Kbar V) 2 _ _ _ _ (hg _) (hpt _) (hps _)
  · exact GlobalTheory.expF_of_pull V D _ A G U (Kbar V) 2 _ _ _ _ (hg _) (hpt _) (hps _)
  · exact GlobalTheory.AddGeneric.addA_of_addG V D _ A G U (Kbar V) θ r n σ σ' th _ _ hr hG hth (fun i => ⟨hpt _, hpt _⟩)
  · exact addB_of_pull D (Kbar V) f s₀ r _ _ _ _ hs₀ (fun i => hps _) (fun i => hps _) hB

end GlobalTheory.AddClosure
