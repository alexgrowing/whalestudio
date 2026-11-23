import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSixthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRowOfSerOf
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem exists_ccIs_equivAt_serOf_oneMapRow : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ O.EquivAt (κ i) (u • cc) ∧ SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1 ∧ OneMapRow (T.Q.Xo ((i : ℕ) + 1)) O.c' (Wc D i) (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) O.dict O.mu (xiR D) (wtA (κ i)) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc D.what₂.embLL.toRatAlgHom.fieldRange (cusp (T.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank) (u • cc) 1 := by
  intro hC D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT hI i Tp tup O hP
  obtain ⟨cc, hcc⟩ := GlobalTheory.T.oscillator_model_exists_ccIs_of_pins hC D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup O hP
  obtain ⟨u, hu, hS⟩ := GlobalTheory.T.oscillator_model_extension_second hC D G Pl0 T0 A T R F κ v₀ hR hT hI i Tp tup O hP cc hcc
  exact ⟨cc, hcc, u, hu, GlobalTheory.T.oscillator_model_values_second hC D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup O hP cc hcc u, hS,
    GlobalTheory.AdTh.oneMapRow_of_serOf D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup O hP (u • cc) hS
      (GlobalTheory.T.oscillator_model_values_sixth hC D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup O hP)⟩

end GlobalTheory.AdTh
