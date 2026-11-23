import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationChartValueFormsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_chart_value_forms_correspond : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → (∀ U₀ : UnifPre I D A G, ∃ U : PreU I D.toPre A G, Under U U₀) ∧ (∀ U : PreU I D.toPre A G, ∃ U₀ : UnifPre I D A G, Under U U₀) ∧ ∀ (U : PreU I D.toPre A G) (U₀ : UnifPre I D A G), Under U U₀ → ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D.toPre (𝟙_ _) k α) (σ₀ : H0 U₀.LG.L k) (f₀ : ∀ α, D.toPre.SecB k α), (∀ σ₁ : H0 U.P.L.L k, HEq σ₁ σ₀ → ∀ z J, Good U.P.L.L z J → sval σ (𝟙 _) z J = sval σ₁ (snd (𝟙_ _) G).left z J) → (∀ α z J, Good D.toPre.P.L z J → sval (f α) (𝟙 _) z J = sval (f₀ α) (snd (𝟙_ _) D.toPre.P.A).left z J) → (U.ExpT (𝟙_ _) k σ f ↔ ∀ e, U₀.ExpandsAt e k σ₀ f₀) := by
  first | exact @GlobalTheory.LN.PreForm.under_exists_and_expands | exact GlobalTheory.LN.PreForm.under_exists_and_expands | (intros; apply GlobalTheory.LN.PreForm.under_exists_and_expands <;> assumption)
