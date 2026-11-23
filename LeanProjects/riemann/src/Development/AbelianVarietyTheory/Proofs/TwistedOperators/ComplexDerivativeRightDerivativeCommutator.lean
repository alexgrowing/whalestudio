import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RWordRTrAdelic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperations

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DerBracket

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem bracket_mem_lieAt {τ : D.what₂.Tau} {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ) : X * Y - Y * X ∈ lieAt V τ := by

  have hX0 : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
  have hY0 : Yᴴ * gramAt D V τ + gramAt D V τ * Y = 0 := hY
  have hX' : Xᴴ * gramAt D V τ = -(gramAt D V τ * X) := eq_neg_of_add_eq_zero_left hX0
  have hY' : Yᴴ * gramAt D V τ = -(gramAt D V τ * Y) := eq_neg_of_add_eq_zero_left hY0
  have e1 : Yᴴ * Xᴴ * gramAt D V τ = gramAt D V τ * Y * X := by
    rw [Matrix.mul_assoc Yᴴ Xᴴ, hX', Matrix.mul_neg, ← Matrix.mul_assoc Yᴴ, hY', Matrix.neg_mul, neg_neg]
  have e2 : Xᴴ * Yᴴ * gramAt D V τ = gramAt D V τ * X * Y := by
    rw [Matrix.mul_assoc Xᴴ Yᴴ, hY', Matrix.mul_neg, ← Matrix.mul_assoc Xᴴ, hX', Matrix.neg_mul, neg_neg]
  show (X * Y - Y * X)ᴴ * gramAt D V τ + gramAt D V τ * (X * Y - Y * X) = 0
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2]
  noncomm_ring

private theorem mem_smF_of_mem_smFun (R : GlobalTheory.SmoothForms.RealPoints θ V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) :
    φ ∈ GlobalTheory.SmoothForms.SmF θ V :=
  (GlobalTheory.SmoothForms.isSmoothInf_iff φ).1 ((GlobalTheory.SmoothForms.smooth_iff R φ).1 hφ)

private theorem rder_eq_opInf_atPlace (R : GlobalTheory.SmoothForms.RealPoints θ V) (τ : D.what₂.Tau) (X : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ)
    (ψ : GlobalTheory.SmoothForms.SmF θ V) :
    Rder θ V τ X.1 ψ.1 = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ X) ψ).1 := by
  rw [GlobalTheory.SmoothForms.opInf_coe]
  exact GlobalTheory.SmoothForms.Rder_eq R τ X ψ.1

theorem Rder_bracket (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ) :
    Rder θ V τ X (Rder θ V τ Y φ) = Rder θ V τ Y (Rder θ V τ X φ) + Rder θ V τ (X * Y - Y * X) φ := by

  have R : GlobalTheory.SmoothForms.RealPoints θ V := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have hXY := bracket_mem_lieAt hX hY
  set ψ : GlobalTheory.SmoothForms.SmF θ V := ⟨φ, mem_smF_of_mem_smFun R hφ⟩ with hψ
  set Xl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X, (GlobalTheory.SmoothForms.mem_lieAt_iff τ X).1 hX⟩ with hXl
  set Yl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨Y, (GlobalTheory.SmoothForms.mem_lieAt_iff τ Y).1 hY⟩ with hYl
  set Zl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X * Y - Y * X, (GlobalTheory.SmoothForms.mem_lieAt_iff τ _).1 hXY⟩ with hZl
  have e := GlobalTheory.SmoothForms.opAt_bracket R τ Xl Yl Zl rfl
  have a1 : Rder θ V τ Y φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ).1 := rder_eq_opInf_atPlace R τ Yl ψ
  have a2 : Rder θ V τ X φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ).1 := rder_eq_opInf_atPlace R τ Xl ψ
  have a3 : Rder θ V τ X (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ).1 =
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ)).1 := rder_eq_opInf_atPlace R τ Xl _
  have a4 : Rder θ V τ Y (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ).1 =
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ)).1 := rder_eq_opInf_atPlace R τ Yl _
  have a5 : Rder θ V τ (X * Y - Y * X) φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Zl) ψ).1 :=
    rder_eq_opInf_atPlace R τ Zl ψ
  rw [a1, a3, a2, a4, a5, e, LinearMap.sub_apply, Submodule.coe_sub]
  change _ = _ + ((GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ)).1 -
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ)).1)
  abel

theorem Rder_comm (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ τ' : D.what₂.Tau} (hτ : τ ≠ τ')
    {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ') :
    Rder θ V τ X (Rder θ V τ' Y φ) = Rder θ V τ' Y (Rder θ V τ X φ) := by

  have R : GlobalTheory.SmoothForms.RealPoints θ V := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  set ψ : GlobalTheory.SmoothForms.SmF θ V := ⟨φ, mem_smF_of_mem_smFun R hφ⟩ with hψ
  set Xl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X, (GlobalTheory.SmoothForms.mem_lieAt_iff τ X).1 hX⟩ with hXl
  set Yl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ' := ⟨Y, (GlobalTheory.SmoothForms.mem_lieAt_iff τ' Y).1 hY⟩ with hYl
  have hc := (GlobalTheory.SmoothForms.opAt_comm R hτ Xl Yl).eq
  have a1 : Rder θ V τ' Y φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ' Yl) ψ).1 := rder_eq_opInf_atPlace R τ' Yl ψ
  have a2 : Rder θ V τ X φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ).1 := rder_eq_opInf_atPlace R τ Xl ψ
  rw [a1, a2, rder_eq_opInf_atPlace R τ Xl, rder_eq_opInf_atPlace R τ' Yl]
  exact congrArg Subtype.val (LinearMap.congr_fun hc ψ)

private theorem commutator_add_I_smul' {n : ℕ} (A B X : Matrix (Fin n) (Fin n) ℂ) :
    (A + Complex.I • B) * X - X * (A + Complex.I • B) = (A * X - X * A) + Complex.I • (B * X - X * B) := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  abel

theorem RderC_Rder : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ τ' : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ), ∀ X ∈ lieAt V τ, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, (RderC θ V τ Z (Rder θ V τ X φ) = Rder θ V τ X (RderC θ V τ Z φ) + RderC θ V τ (Z * X - X * Z) φ) ∧ (τ' ≠ τ → RderC θ V τ' Z (Rder θ V τ X φ) = Rder θ V τ X (RderC θ V τ' Z φ)) := by
  intro D θ hθ V τ τ' Z X hX φ hφ
  constructor
  ·
    obtain ⟨hA, hB⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
    have hZ := GlobalTheory.SmoothAutCheck.parts_sum V τ Z
    set A := (1 / 2 : ℂ) • (Z + conjAt V τ Z) with hAdef
    set B := (1 / (2 * Complex.I)) • (Z - conjAt V τ Z) with hBdef
    have hc := commutator_add_I_smul' A B X
    rw [hZ] at hc
    have hAX := bracket_mem_lieAt hA hX
    have hBX := bracket_mem_lieAt hB hX
    have e1 : RderC θ V τ (Z * X - X * Z) φ =
        Rder θ V τ (A * X - X * A) φ + Complex.I • Rder θ V τ (B * X - X * B) φ := by
      rw [hc, GlobalTheory.Mem.RealTranslate.RderC_add hθ hφ, GlobalTheory.Mem.RealTranslate.RderC_smul hθ hφ,
        GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hAX, GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hBX]
    rw [e1]
    show Rder θ V τ A (Rder θ V τ X φ) + Complex.I • Rder θ V τ B (Rder θ V τ X φ) =
      Rder θ V τ X (Rder θ V τ A φ + Complex.I • Rder θ V τ B φ) + _
    rw [Rder_bracket hθ hφ hA hX, Rder_bracket hθ hφ hB hX,
      Rder_add (Rder_mem hφ hA) ((SmFun θ V).smul_mem _ (Rder_mem hφ hB)) hX, Rder_smul]
    rw [smul_add]
    abel
  ·
    intro hne
    obtain ⟨hA, hB⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ' Z
    show Rder θ V τ' ((1 / 2 : ℂ) • (Z + conjAt V τ' Z)) (Rder θ V τ X φ) +
        Complex.I • Rder θ V τ' ((1 / (2 * Complex.I)) • (Z - conjAt V τ' Z)) (Rder θ V τ X φ) =
      Rder θ V τ X (Rder θ V τ' ((1 / 2 : ℂ) • (Z + conjAt V τ' Z)) φ +
        Complex.I • Rder θ V τ' ((1 / (2 * Complex.I)) • (Z - conjAt V τ' Z)) φ)
    rw [Rder_add (Rder_mem hφ hA) ((SmFun θ V).smul_mem _ (Rder_mem hφ hB)) hX, Rder_smul,
      Rder_comm hθ hφ hne hA hX, Rder_comm hθ hφ hne hB hX]

end GlobalTheory.DerBracket

end
