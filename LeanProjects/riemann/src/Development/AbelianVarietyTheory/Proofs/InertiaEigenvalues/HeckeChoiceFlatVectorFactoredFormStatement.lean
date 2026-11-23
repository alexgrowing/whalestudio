import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeChoiceFlatVectorFactoredForm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussGLZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChoice_flatVector_factoredForm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∃ (z : GA D (Vc D i)) (B : ℂ) (ε : ℤ) (r : ℕ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsCentAt i (R.Q t) z ∧ (∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → τ B = B) ∧ (∀ PP ∈ R.Q t, (ψP PP).IsPrimitive) ∧ ∀ t' : T0, R.Q t' = R.Q t → ∀ f', IsFlatVec R i t' f' → ∃ s : (AE D)ˣ, f' = (B * (∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r) ^ ε * ((R.xi t' s : Circle) : ℂ)) • R.ωP i t' (z, 1) (R.vP i t') := by
  first | exact @GlobalTheory.FlatConj.flatVec_factored_form | exact GlobalTheory.FlatConj.flatVec_factored_form | (intros; apply GlobalTheory.FlatConj.flatVec_factored_form <;> assumption)
