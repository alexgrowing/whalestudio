import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterUpdateOfWeakRealisation
import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.LowRow.baseLinks_of_prims : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ s : ℕ, A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → GlobalTheory.Hk3.Core R.toRealDat F.lv2 ∧ A3.A.fam.Ok s ∧ BaseLinks R.toRealDat F.lv2 := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F s hOk hsep hC hE hP hph
  have c := RealDat3.characterisation_of_weak hC hE
  have hR := complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP
  refine ⟨⟨c.lev, c.grp, c.fam, c.models, c.chain, c.thP⟩, hOk.ok2, ?_, ?_, ?_⟩
  · have h := hR.lifts0.1
    rw [GlobalTheory.CharRealise.toCx3_eq_one R F hph] at h
    exact h
  · have h := hR.ratTh
    rw [GlobalTheory.CharRealise.toCx3_eq_one R F hph] at h
    exact h
  · have h := hR.proviso0
    rw [GlobalTheory.CharRealise.toCx3_eq_one R F hph] at h
    exact h
