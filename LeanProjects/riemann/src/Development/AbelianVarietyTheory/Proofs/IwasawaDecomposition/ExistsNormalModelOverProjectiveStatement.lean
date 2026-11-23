import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelOverProjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_model_over_projective : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (O : Type) [CommRing O] (ε : 𝓞 F ≃+* O) (X : Scheme.{0}) (sX : X ⟶ Sp O) (ρ : Y.X ⟶ X), IsProjOver sX → ρ ≫ sX ≫ spMap ε.toRingHom = Y.str ≫ spMap (algebraMap (𝓞 F) F) → X.IsSeparated ∧ IsLocallyNoetherian X ∧ ∃ (M : GlobalTheory.TrueGeo.Model Y) (ρ' : M.X ⟶ X), IsNormalScheme M.X ∧ M.j ≫ ρ' = ρ := by
  first | exact @GlobalTheory.ModelOver.exists_normal_model | exact GlobalTheory.ModelOver.exists_normal_model | (intros; apply GlobalTheory.ModelOver.exists_normal_model <;> assumption)
