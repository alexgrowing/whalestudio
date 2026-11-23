import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConvolutionSingleFactorGoodProjectorEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicAverageEqCoeffSinglePlaceElementStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterTeichmullerLabelOfGoodTypesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.GoodNoChiTr

open Polynomial

theorem not_root_of_good (N g : ℕ) [Fact g.Prime] {PP J : Type} (f : PP → (ZMod g)[X])
    (χ : PP → J → (ZMod g)ˣ) (h : Formalism.CyclotomicNorms.IsGood N g f χ) (v : PP) (j : J) :
    ¬ (f v).IsRoot (χ v j : ZMod g) := by
  intro hr
  have hne : f v ≠ 0 := (h.1 v).1.ne_zero
  have hmem : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (χ v j : ZMod g) ∈ Formalism.CyclotomicNorms.rootsBar (f v) := by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [Polynomial.mem_roots (Polynomial.map_ne_zero hne), Polynomial.IsRoot, Polynomial.eval_map,
      Polynomial.eval₂_hom, hr.eq_zero, map_zero]
  obtain ⟨ℓ, hℓ, hℓg⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ g := by
    by_cases h2 : g = 2
    · exact ⟨3, Nat.prime_three, by omega⟩
    · exact ⟨2, Nat.prime_two, fun e => h2 e.symm⟩
  exact h.2.2.2.1 ℓ hℓ hℓg v j _ hmem rfl

theorem conv_mirC_eC : GlobalTheory.MirAvg.SeriesKillsAvg → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), GlobalTheory.LiftRows.Given R F → ∀ (i : Fin D.R.m) (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 →
    ∀ (b : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ x : G,
      ∑ y : G, GlobalTheory.DownLift.mirC R i PP a b ε y * RealDat.eC (A := A) (sg0 D A) (y⁻¹ * x) = 0 := by
  intro hS D G _ _ Pl0 T A Ks _ _ _ R F hG i PP a ha b ε hε x
  obtain ⟨eR, plg, iso, hcoef, hdiv, hrec⟩ := hG.core.grp.record
  obtain ⟨kv0, rfl⟩ := plg.surjective PP
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  have heC : ∀ g, RealDat.eC (A := A) (sg0 D A) g = D.ntypes.e0.coeff (eR g) := by
    intro g
    rw [← hcoef g]
    unfold RealDat.eC sg0
    rw [sgAt_mk _ R.hv0]
  rw [Finset.sum_congr rfl (fun y _ => by rw [GlobalTheory.T.mirabolicAverage_eq_coeff_singlePlaceElement D G Pl0 T A Ks R eR plg iso hrec i kv0 a b ε y, heC])]
  refine GlobalTheory.T.convolution_singleFactor_goodProjector_eq_zero D G eR kv0 _ ?_ x
  intro a' hgood
  obtain ⟨L, hL, c, hc, hcc⟩ := GlobalTheory.T.levelCharacter_teichmullerLabel_of_goodTypes D G Pl0 T A Ks R hG.types kv0.1 kv0.2 i (plg kv0).1 (hdiv kv0) (iso kv0) ε hε
  rw [← D.ntypes.eSer_central, hL]
  have h1 := not_root_of_good _ _ _ _ (hgood kv0.1).1 kv0.2 i
  have h2 := not_root_of_good _ _ _ _ (hgood kv0.1).2 kv0.2 i
  have ha' : (fun j => (iso kv0).symm (a j)) ≠ 0 := by
    intro h; apply ha; funext j
    have := congrArg (iso kv0) (congrFun h j)
    simpa using this
  refine hS _ L _ _ _ c hc ?_ ?_ _ b ha'
  · rcases hcc with rfl | rfl
    · exact h1
    · exact h2
  · rcases hcc with rfl | rfl
    · rw [← Units.val_inv_eq_inv_val]; exact h2
    · rw [Units.val_inv_eq_inv_val, inv_inv]; exact h1

end GlobalTheory.GoodNoChiTr
