import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelMapGenericallyOpenImmersionCalculus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → (∀ (A : Over (Sp K)) (M N : Model R A), M.Irr → M.Le N → GenIso M N (𝟙 A)) ∧ (∀ (A A' A'' : Over (Sp K)) (M : Model R A) (N : Model R A') (P : Model R A'') (f : A ⟶ A') (g : A' ⟶ A''), N.Irr → GenIso M N f → GenIso N P g → GenIso M P (f ≫ g)) ∧ (∀ (A A' : Over (Sp K)) (M : Model R A) (N : Model R A') (f : A ≅ A'), (GenIso M N f.hom → GenIso N M f.inv) ∧ (GenIso M N f.hom ↔ GenIso (M.twist f) N (𝟙 A')) ∧ (M.Irr → (M.twist f).Irr)) ∧ (∀ (A A' B B' : Over (Sp K)) (M : Model R A) (N : Model R A') (P : Model R B) (Q : Model R B') (f : A ⟶ B) (g : A' ⟶ B'), GenIso M P f → GenIso N Q g → GenIso (M.prod N) (P.prod Q) (f ⊗ₘ g)) ∧ (∀ (A A' A'' : Over (Sp K)) (M : Model R A) (N : Model R A') (P : Model R A''), M.Irr → N.Irr → P.Irr → GenIso ((M.prod N).prod P) (M.prod (N.prod P)) (α_ A A' A'').hom ∧ GenIso (M.prod N) (N.prod M) (β_ A A').hom) := by
  first | exact @GlobalTheory.SS.GI.genIso_calculus | exact GlobalTheory.SS.GI.genIso_calculus | (intros; apply GlobalTheory.SS.GI.genIso_calculus <;> assumption)
