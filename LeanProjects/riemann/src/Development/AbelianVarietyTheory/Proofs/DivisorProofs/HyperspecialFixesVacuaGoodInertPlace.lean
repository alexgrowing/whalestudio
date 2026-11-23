import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateSplittingUnramifiedHyperspecialFix
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingCharactersUnramifiedOffLevelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
namespace GlobalTheory.FixAllGood
open GlobalTheory.Hk3 (UnrPl VacFix)

theorem unrPl_mul {D : D7} {P : Pl D.host.E} {χ χ' : (AE D)ˣ →* Circle} (h : UnrPl P χ) (h' : UnrPl P χ') :
    UnrPl P (χ * χ') := fun e f hP x a b c => by
  rw [MonoidHom.mul_apply, h e f hP x a b c, h' e f hP x a b c, mul_one]

theorem unrPl_inv {D : D7} {P : Pl D.host.E} {χ : (AE D)ˣ →* Circle} (h : UnrPl P χ) :
    UnrPl P χ⁻¹ := fun e f hP x a b c => by
  rw [MonoidHom.inv_apply, h e f hP x a b c, inv_one]

theorem unrPl_chrStep {D : D7} {P : Pl D.host.E} {μ : ℕ → (AE D)ˣ →* Circle} {η : (AE D)ˣ →* Circle} {j : ℕ}
    (hμ : UnrPl P (μ j)) (hη : UnrPl P η) :
    UnrPl P (Lift.chrStep μ η j).1 ∧ UnrPl P (Lift.chrStep μ η j).2 := by
  unfold Lift.chrStep
  split_ifs
  · exact ⟨unrPl_mul hμ (unrPl_inv hη), hμ⟩
  · exact ⟨hμ, unrPl_mul hμ (unrPl_inv hη)⟩

theorem unrPl_chrTh {D : D7} {P : Pl D.host.E} {μ : ℕ → (AE D)ˣ →* Circle} {η : (AE D)ˣ →* Circle} {j : ℕ}
    (hμ : UnrPl P (μ j)) (hη : UnrPl P η) :
    UnrPl P (Lift.chrTh μ η j).1 ∧ UnrPl P (Lift.chrTh μ η j).2 :=
  ⟨hμ, unrPl_mul hμ (unrPl_inv hη)⟩

theorem fixAll_of_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → ∀ t P, Good R.toRealDat t P → conjPl P = P → FixAll R.toRealDat t P := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h _ t P hP _
  have hu := GlobalTheory.T.splittingCharacters_unramified_offLevels R.toRealDat F.lv2 h.base.lev t P hP
  have hm := D.R.two_le_m
  refine ⟨fun k hk => ?_, ?_, fun i => ?_⟩
  · have hc := unrPl_chrStep (hu.2 (k + 1) (Nat.le_add_left _ _) hk.le) hu.1
    exact GlobalTheory.ConjVacFix.vacFix_of_unrPl _ _ _ _ _ _ P (h.fullY t k hk).datum hc.1 hc.2
  · have hc := unrPl_chrStep (hu.2 D.R.m (by omega) le_rfl) hu.1
    exact GlobalTheory.ConjVacFix.vacFix_of_unrPl _ _ _ _ _ _ P (h.fullX t).datum hc.1 hc.2
  · have hc := unrPl_chrTh (hu.2 ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2) hu.1
    exact GlobalTheory.ConjVacFix.vacFix_of_unrPl _ _ _ _ _ _ P (h.fullP i t).datum hc.1 hc.2

end GlobalTheory.FixAllGood
