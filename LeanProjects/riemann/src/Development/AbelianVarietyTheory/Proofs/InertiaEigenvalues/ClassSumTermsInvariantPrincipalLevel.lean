import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumSmallerLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormsSpannedByThetaSeriesOfClassSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalLevelLeLevelCharactersAgreeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

namespace GlobalTheory.PrincClassSum

theorem fin_symm {D : D7} (S : HSp D) (y : Bridge.Gf S) :
    finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) = y :=
  (GlobalTheory.ClassRegroup.finEquiv S).apply_symm_apply y

theorem left_inv {D : D7} {S T : HSp D} (B : Base S T) (hB : B.Good) (hS : S.SigOK) (ψ : Twist D Circle) (hψ : ψ.Good)
    (hQ : B.admitted ψ.Q) (ω : PairRep S T) (hω : B.IsWeil ψ.chi ω) {F : Bridge.Gf S → _} (hF : F ∈ B.formsC ψ)
    (g : GA D T) (γ : GQ S) (y : Bridge.Gf S) :
    series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (Bridge.ratF S γ * y) : GfC S) : GA D S)
        (F (Bridge.ratF S γ * y)) g =
      series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g := by
  have e : finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm (Bridge.ratF S γ * y) : GfC S) : GA D S) =
      Bridge.ratF S γ * finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) *
        ((1 : (GlobalTheory.FlatVecSum.princ B).levJ ψ) : Bridge.Gf S) := by
    rw [fin_symm, fin_symm, OneMemClass.coe_one, mul_one]
  have hm := GlobalTheory.BaseClassSum.series_move (GlobalTheory.FlatVecSum.princ_good hB) hS hψ hQ hω (Subtype.property _) (Subtype.property _)
    γ 1 e (F (Bridge.ratF S γ * y))
  have hl := (B.mem_formsC.1 hF).2 γ y 1
  rw [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at hl
  have hinv : B.act ((γ⁻¹ : GQ S) : GA D S) (B.act (γ : GA D S) (F y)) = F y := by
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [map_one, Units.val_one, inv_one, one_smul] at hm
  rw [hl] at hm ⊢
  rw [show (GlobalTheory.FlatVecSum.princ B).act = B.act from rfl, hinv] at hm
  exact congrFun hm g

set_option maxHeartbeats 8000000 in
theorem right_inv {D : D7} {S T : HSp D} (B : Base S T) (hB : B.Good) (hS : S.SigOK) (ψ : Twist D Circle) (hψ : ψ.Good)
    (hQ : B.admitted ψ.Q) (ω : PairRep S T) (hω : B.IsWeil ψ.chi ω) {F : Bridge.Gf S → _} (hF : F ∈ B.formsC ψ)
    (g : GA D T) (k : Bridge.Gf S) (hk : k ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ) (y : Bridge.Gf S) :
    series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (y * k) : GfC S) : GA D S)
        (F (y * k)) g =
      series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g := by
  obtain ⟨hle, hlam⟩ := GlobalTheory.T.principalLevel_le_level_characters_agree B hB ψ hQ
  have e : finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm (y * k) : GfC S) : GA D S) =
      Bridge.ratF S 1 * finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) *
        ((⟨k, hk⟩ : (GlobalTheory.FlatVecSum.princ B).levJ ψ) : Bridge.Gf S) := by
    rw [fin_symm, fin_symm, (Bridge.ratF S).map_one, one_mul]
  have hm := GlobalTheory.BaseClassSum.series_move (GlobalTheory.FlatVecSum.princ_good hB) hS hψ hQ hω (Subtype.property _) (Subtype.property _)
    1 ⟨k, hk⟩ e (F (y * k))
  have hl := (B.mem_formsC.1 hF).2 1 y ⟨k, hle hk⟩
  rw [(Bridge.ratF S).map_one, one_mul, OneMemClass.coe_one, map_one, Module.End.one_apply] at hl
  rw [show (GlobalTheory.FlatVecSum.princ B).act = B.act from rfl, inv_one, OneMemClass.coe_one, map_one,
    Module.End.one_apply, hlam k hk] at hm
  rw [hl] at hm ⊢
  rw [LinearMap.map_smul, LinearMap.map_smul, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at hm
  rw [LinearMap.map_smul]
  exact congrFun hm g

theorem terms_inv : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ F ∈ B.formsC ψ, ∀ g : GA D T,
      (∀ (γ : GQ S) (y : Bridge.Gf S),
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (Bridge.ratF S γ * y) : GfC S) : GA D S)
          (F (Bridge.ratF S γ * y)) g =
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g) ∧
      ∀ k ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ, ∀ y : Bridge.Gf S,
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (y * k) : GfC S) : GA D S)
          (F (y * k)) g =
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g :=
  fun B hB hS ψ hψ hQ ω hω _ hF g =>
    ⟨fun γ y => left_inv B hB hS ψ hψ hQ ω hω hF g γ y, fun k hk y => right_inv B hB hS ψ hψ hQ ω hω hF g k hk y⟩

end GlobalTheory.PrincClassSum
