import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectOfGaloisDescendedData
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelObject_of_galois_descended_data : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (X Y : Scheme.{0}) (π : X ⟶ Y) (s : X ⟶ Sp o) (sY : Y ⟶ Sp o) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (c : SiegPre h M ζ s) (A₀ : Over Y) [GrpObj A₀] (φ : c.A.left ⟶ A₀.left) (φ₂ : (G2 c.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y) ⟶ A₀)), s = π ≫ sY → IsGaloisCover Ga ρ π → IsAbelianScheme A₀ → IsGrpPullback c.A A₀ π φ → IsSquare φ φ₂ → P₀.IsLB → LBIso c.P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∀ a, (c.lev a).left ≫ φ = π ≫ (lev₀ a).left) → ∃ c₀ : SiegPre h M ζ sY, SiegPB c c₀ π := by
  first | exact @GlobalTheory.exists_siegPre_of_galois_descended_data | exact GlobalTheory.exists_siegPre_of_galois_descended_data | (intros; apply GlobalTheory.exists_siegPre_of_galois_descended_data <;> assumption)
