import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLawsCentralMovedReadings
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullHeckeRealDatMovedReadings
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationLaws_centralMovedReadings : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G), (∀ i σ, w i σ ∈ Subgroup.center G) → R.LUnif → (moveR R w).LUnif := by
  first | exact @GlobalTheory.Unframe.lUnif_moveR | exact GlobalTheory.Unframe.lUnif_moveR | (intros; apply GlobalTheory.Unframe.lUnif_moveR <;> assumption)
