import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmR
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.CenTheta

theorem norm_localChar_val {K : Type} [Field K] [NumberField K] (c : HeckeCharacter K) (w : PlK K)
    (x : (Kv K w)ˣ) : ‖((localChar c w x : ℂˣ) : ℂ)‖ = 1 := by
  rw [GroundTheory.Automorphic.GodementSection.coe_localChar]
  exact Circle.norm_coe _

theorem norm_cAt_val {K : Type} [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl) (w : PlK K)
    [w.asIdeal.LiesOver v.asIdeal] (a : (Qv v)ˣ) : ‖((cAt c v w a : ℂˣ) : ℂ)‖ = 1 :=
  norm_localChar_val c w _

theorem norm_resF_val {K : Type} [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl) (w : PlK K)
    [w.asIdeal.LiesOver v.asIdeal] (a : (Qv v)ˣ) :
    ‖((GL2LocalData.resF (F := Qv v) (localChar c w) a : ℂˣ) : ℂ)‖ = 1 :=
  norm_localChar_val c w _

theorem norm_nsg {F E : Type} [Field F] [Field E] [Algebra F E] (a : F) : ‖GL2LocalData.nsg E a‖ = 1 := by
  unfold GL2LocalData.nsg
  split_ifs <;> simp

theorem norm_central_scalars_eq_one : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (m : LM c v), m.ok → ∀ (a : (Qv v)ˣ), ‖omW m a‖ = 1 ∧ ‖om0 m a‖ = 1 := by
  intro K _ _ _ c v m hm a
  cases m with
  | sp w₁ w₂ Φ =>
    constructor
    · simp only [omW, Units.val_mul, norm_mul, norm_cAt_val, mul_one]
    · simp only [om0, Units.val_mul, norm_mul, norm_cAt_val, mul_one]
  | ns w σ η Φ =>
    have hη : ‖((η a : ℂˣ) : ℂ)‖ = 1 := by
      rw [hm.2.2.1 a]; exact norm_nsg _
    constructor
    · simp only [omW, MonoidHom.mul_apply, Units.val_mul, norm_mul, norm_resF_val, hη, mul_one]
    · simp only [om0, MonoidHom.mul_apply, Units.val_mul, norm_mul, norm_resF_val, hη, mul_one]

end GlobalTheory.CompanionTheory.CenTheta
