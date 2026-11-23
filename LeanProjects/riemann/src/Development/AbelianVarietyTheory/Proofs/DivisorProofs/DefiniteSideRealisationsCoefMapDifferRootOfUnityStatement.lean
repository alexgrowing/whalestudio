import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteSideRealisationsCoefMapDifferRootOfUnity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesUnitOfReadInjScaleRootConjRootCoordRange
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteSideRealisations_coefMap_differ_rootOfUnity : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
    {A : FamIn D.what₂.LL G Pl0 T m} {cR : Bridge.CoefDat D D.sp.X'} {cL : ∀ i : Fin m, Bridge.CoefDat D (D.sp.V ((i : ℕ) + 1))}
    {lR : ∀ t, Bridge.LevEnv D D.sp.X' (A.ok t × ℕ)} {lL : ∀ (i : Fin m) t, Bridge.LevEnv D (D.sp.V ((i : ℕ) + 1)) (A.ok t × ℕ)}
    (B : Bridge.FamReal D A cR cL lR lL) (pl : Pl0 → Pl D.host.E) (S : Set (Pl D.host.E)) (Qt : T → Finset (Pl D.host.E))
    (tauL : D.what₂.Tau → (D.host.E →+* D.what₂.LL)) (lamR : D.what₂.Tau → DomWeight D.sp.X'.rank)
    (lamL : ∀ i : Fin m, D.what₂.Tau → DomWeight (D.sp.V ((i : ℕ) + 1)).rank)
    (gramR gramR' : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R c0R' : VV D.what₂.LL lamR →ₛₗ[D.what₂.embLL] cR.W)
    (c0L c0L' : ∀ i : Fin m, VV D.what₂.LL (lamL i) →ₛₗ[D.what₂.embLL] (cL i).W),
    Bridge.FamTie B pl S Qt tauL lamR lamL gramR c0R c0L → Bridge.FamTie B pl S Qt tauL lamR lamL gramR' c0R' c0L' →
    ∀ i : Fin m, ∃ a : D.what₂.LL, (∃ k : ℕ, k ≠ 0 ∧ a ^ k = 1) ∧ ∀ F, c0L' i F = D.what₂.embLL a • c0L i F := by
  first | exact @GlobalTheory.CoefRoot.coef_root | exact GlobalTheory.CoefRoot.coef_root | (intros; apply GlobalTheory.CoefRoot.coef_root <;> assumption)
