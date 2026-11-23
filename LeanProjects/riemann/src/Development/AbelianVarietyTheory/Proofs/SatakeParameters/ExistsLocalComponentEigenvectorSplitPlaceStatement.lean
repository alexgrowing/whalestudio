import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorSplitPlace
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localComponent_eigenvector_splitPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Submodule ℂ (UA E n → ℂ)), IsAutRepU U → ∀ w, IsSplitAt w → ∀ (J : Subgroup (GL (Fin n) (w.adicCompletion E))), IsOpen (J : Set (GL (Fin n) (w.adicCompletion E))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion E))) → ∀ (χ : J →* ℂˣ) (φ : UA E n → ℂ), φ ∈ U → φ ≠ 0 → (∀ x ∈ locU n w, ∀ hx : cLoc w x ∈ J, RU E n x φ = (χ ⟨_, hx⟩ : ℂ) • φ) → ∃ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ ∃ v : σ.V, v ≠ 0 ∧ ∀ g : J, σ.ρ g v = (χ g : ℂ) • v := by
  first | (exact @GlobalTheory.SplitEigen.exists_locComp_eigen) | (exact GlobalTheory.SplitEigen.exists_locComp_eigen) | (intros; apply GlobalTheory.SplitEigen.exists_locComp_eigen  <;> assumption)
