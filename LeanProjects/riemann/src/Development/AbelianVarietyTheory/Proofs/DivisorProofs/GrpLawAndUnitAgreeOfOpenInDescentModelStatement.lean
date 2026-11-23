import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpLawAndUnitAgreeOfOpenInDescentModel
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpLaw_and_unit_agree_of_openIn_descentModel : ∀ (σ : Setup) (E : Emb σ) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp σ.R) (s₂ : S₂ ⟶ Sp σ.R) (H₁ : Over S₁) [GrpObj H₁] (H₂ : Over S₂) [GrpObj H₂] (h₁ : H₁.left ⟶ E.P) (h₂ : H₂.left ⟶ E.P), Flat s₁ → Flat s₂ → Flat H₁.hom → Flat H₂.hom → OpenIn h₁ H₁.hom E.p s₁ → OpenIn h₂ H₂.hom E.p s₂ → MulAgree H₁ σ.A h₁ E.ιA → MulAgree H₂ σ.A h₂ E.ιA → MulAgree H₁ H₂ h₁ h₂ ∧ OneAgree s₁ s₂ H₁ H₂ h₁ h₂ := by
  first | exact @GlobalTheory.Desc.mulAgree_oneAgree_of_openIn | exact GlobalTheory.Desc.mulAgree_oneAgree_of_openIn | (intros; apply GlobalTheory.Desc.mulAgree_oneAgree_of_openIn <;> assumption)
