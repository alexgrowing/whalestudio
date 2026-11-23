import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

namespace GlobalTheory.LocOm.LawMul

theorem om_smul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (c : ℂ) (Φ : Matrix b a k → ℂ) :
    om μ g h (c • Φ) = c • om μ g h Φ := by
  funext x
  simp only [om, Pi.smul_apply, smul_eq_mul]
  ring

theorem lawLoc_mul : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (S T : HSp D) (ω : Om S T) (μS μT : kˣ →* ℂˣ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)) (g g' : GA D S) (gk gk' : GL Y' k) (h h' : GA D T) (hk hk' : GL Y k), LawLoc ω μS μT Tm g gk h hk → LawLoc ω μS μT Tm g' gk' h' hk' → LawLoc ω μS μT Tm (g * g') (gk * gk') (h * h') (hk * hk') := by
  intro D k _ _ _ _ S T ω μS μT Y Y' _ _ _ _ Tm g g' gk gk' h h' hk hk' H H' Φ Φ' hΦ
  let Φ₁ : SB (Matrix Y Y' k) :=
    ⟨(((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk') : ℂˣ) : ℂ) • om μS⁻¹ gk' hk' Φ.1,
      Submodule.smul_mem _ _ (GlobalTheory.SplitWeil.Model.om_mem_SB _ _ _ Φ.2)⟩
  have h1 : ω (g', h') (Tm Φ) = Tm Φ₁ := H' Φ Φ₁ rfl
  have h2 : ω (g, h) (Tm Φ₁) = Tm Φ' := by
    refine H Φ₁ Φ' ?_
    rw [hΦ, GlobalTheory.SplitWeil.Model.om_mul, map_mul, map_mul, Units.val_mul, mul_smul]
    simp only [Φ₁, om_smul]
  rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, h1, h2]

end GlobalTheory.LocOm.LawMul
