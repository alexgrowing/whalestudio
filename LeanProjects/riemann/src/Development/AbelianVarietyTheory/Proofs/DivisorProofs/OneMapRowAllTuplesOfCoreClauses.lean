import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRowOfBaseTupleIdentityRowSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapIdentityEveryNormalisedFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapBaseTupleOfCharacterisationExtremalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedDataAllTuplesOfBaseTupleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsAgreementContainsFormIndependentFieldsStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapCore

theorem oneMapRowR_of_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ i, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → OneMapRowR T R κ v₀ O ph i := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hR hoff hused hfw hio i hpins htie hspan
  have hin : TieIn T R κ v₀ := GlobalTheory.T.cuspFormsAgreement_contains_formIndependentFields D G Pl0 T0 A T R κ v₀ hfw
  refine GlobalTheory.T.oneMapRow_of_baseTuple_identityRow_span D G Pl0 T0 A T R κ v₀ O ph i hR.lev hR.grp.chiW hR.fam hR.models hpins htie
    (GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hCI D G Pl0 T0 A T R F κ v₀ hR hin hio O i hpins) (fun hG => ?_)
    (GlobalTheory.T.thetaOneMap_identity_every_normalised_family hCI D G Pl0 T0 A T R F κ v₀ hR hin hio i) hspan
  obtain ⟨O', h1, h2, -⟩ := GlobalTheory.T.exists_normalisedData_allTuples_of_baseTuple D G Pl0 T0 A T R κ v₀ O hR.lev hR.grp.chiW hR.fam hR.models hR.thP.vP hoff hused
    hfw i hpins hG
  exact ⟨O', h1, h2⟩

end GlobalTheory.OneMapCore
