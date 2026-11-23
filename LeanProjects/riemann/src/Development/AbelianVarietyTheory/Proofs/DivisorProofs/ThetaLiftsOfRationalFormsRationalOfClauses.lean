import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PbEqOfPins
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvaluatesOfUnif
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatOfOneMapOverL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTupleDataOverRowFieldConditionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceTupleLiftsSpanAllTuplesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapAllTuplesCoeffFieldOfClausesStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistField

set_option maxHeartbeats 2000000 in

theorem ratG_of_clauses : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → (∀ i, OMPins T R κ v₀ O i) → (∀ i, PhaseTie T R κ v₀ O ph i) → IoExt R → (∀ i, OneMapRow0 T R κ v₀ O i) → QGuard R → R.LUnif → EvInj T R v₀ → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.RatG R ph := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hnV hC hoff hused hW hO hph hio h0 hQ hU hinj hcov i t x
  obtain ⟨fw⟩ := id hW
  have hpb : T.pb = R.C.P.pb := GlobalTheory.PinsFixHalf.pb_eq_of_pins T R κ v₀ O hC.lev fw.laws hO
  have hex : PinsOverL T R κ v₀ i := GlobalTheory.T.exists_normalisedTupleData_over_rowField_conditions D G Pl0 T0 A T R F κ v₀ O i hC hoff hused hW (hO i) hQ hcov
  have hsp : GlobalTheory.OneMapTuples.LiftsSpan R i (v₀ i (sg0 D A)) :=
    GlobalTheory.T.referenceTuple_lifts_span_all_tuples D G Pl0 T0 A T R F κ v₀ O i hnV hC hoff hused hW hio (hO i) (h0 i) hQ
  have hone : OneMapOverL T R κ v₀ (ph i) i :=
    GlobalTheory.T.oneFormMap_allTuples_coeffField_of_clauses D G Pl0 T0 A T R F κ v₀ O ph i hC hoff hused hW hpb (hO i) (hph i) hio (h0 i) hex hsp
  have hev : fw.Evaluates := GlobalTheory.evaluates_of_unif D G Pl0 T0 A T R F κ v₀ fw hU
  have hrat := GlobalTheory.TwistField.Read.rat_of_oneMapOverL D G Pl0 T0 A T R F κ v₀ fw (ph i) i hC.lev hC.grp hC.models hC.thP hU
    hev hinj hone t x
  obtain ⟨y, -, hy⟩ := hrat
  exact ⟨_, hy.symm⟩

end GlobalTheory.TwistField
