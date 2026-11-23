import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Lin

open GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.Rodier.SmIntEl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem muD_add {W : Type} [AddCommGroup W] [Module ℂ W] (n : ℕ) {φ₁ φ₂ : (Fin n → k) → W}
    (l₁ : IsLocallyConstant φ₁) (c₁ : HasCompactSupport φ₁)
    (l₂ : IsLocallyConstant φ₂) (c₂ : HasCompactSupport φ₂) :
    @smInt _ _ (borel _) _ _ (muD k n) (φ₁ + φ₂) =
      @smInt _ _ (borel _) _ _ (muD k n) φ₁ + @smInt _ _ (borel _) _ _ (muD k n) φ₂ := by
  letI : MeasurableSpace (Fin n → k) := borel _
  haveI : BorelSpace (Fin n → k) := ⟨rfl⟩
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts (muD k n) := by
    unfold muD
    infer_instance
  exact smInt_add (muD k n) l₁ c₁ l₂ c₂

theorem muD_smul {W : Type} [AddCommGroup W] [Module ℂ W] (n : ℕ) (c : ℂ) {φ : (Fin n → k) → W}
    (l : IsLocallyConstant φ) (h : HasCompactSupport φ) :
    @smInt _ _ (borel _) _ _ (muD k n) (c • φ) = c • @smInt _ _ (borel _) _ _ (muD k n) φ := by
  letI : MeasurableSpace (Fin n → k) := borel _
  haveI : BorelSpace (Fin n → k) := ⟨rfl⟩
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts (muD k n) := by
    unfold muD
    infer_instance
  have e : (⇑(c • LinearMap.id : W →ₗ[ℂ] W) ∘ φ) = c • φ := rfl
  rw [← e, smInt_linear (muD k n) (c • LinearMap.id : W →ₗ[ℂ] W) l h]
  rfl

variable {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}

def tw (ψ : AddChar k Circle) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) : (Fin (t + 1) → k) → τ.V ⊗[ℂ] σ.V :=
  fun d => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)

theorem tw_add (ψ : AddChar k Circle) (f g : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    tw ψ (f + g) y = tw ψ f y + tw ψ g y :=
  funext fun _ => smul_add _ _ _

theorem tw_smul (ψ : AddChar k Circle) (c : ℂ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    tw ψ (c • f) y = c • tw ψ f y :=
  funext fun d => by
    show (_ : ℂ) • (c • evX f _) = c • ((_ : ℂ) • evX f _)
    exact smul_comm _ _ _

theorem tw_lc (ψ : AddChar k Circle) (hψ : Continuous ψ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    IsLocallyConstant (tw ψ f y) := by
  have h1 : IsLocallyConstant (fun d : Fin (t + 1) → k => ψ (d (Fin.last t))) :=
    (GlobalTheory.IrredSB.char_isLocallyConstant ψ hψ).comp_continuous (continuous_apply _)
  have h2 : IsLocallyConstant (fun d : Fin (t + 1) → k =>
      (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ)) :=
    h1.comp (fun z : Circle => (((Circle.toUnits z)⁻¹ : ℂˣ) : ℂ))
  exact IsLocallyConstant.comp₂ h2 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).1 (fun a b => a • b)

theorem tw_cs (ψ : AddChar k Circle) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    HasCompactSupport (tw ψ f y) := by
  refine (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).2.mono fun d hd h0 => hd ?_
  have h0' : evX f (dEmb k i t d * y) = 0 := h0
  show (_ : ℂ) • evX f (dEmb k i t d * y) = 0
  rw [h0', smul_zero]

theorem intO_add (f g : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intO (f + g) y = intO f y + intO g y :=
  muD_add (t + 1) (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).1 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).2
    (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ g y).1 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ g y).2

theorem intO_smul (c : ℂ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intO (c • f) y = c • intO f y :=
  muD_smul (t + 1) c (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).1 (GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y).2

theorem intC_add (ψ : AddChar k Circle) (hψ : Continuous ψ) (f g : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intC ψ (f + g) y = intC ψ f y + intC ψ g y :=
  (congrArg (@smInt _ _ (borel _) _ _ (muD k (t + 1))) (tw_add ψ f g y)).trans
    (muD_add (t + 1) (tw_lc ψ hψ f y) (tw_cs ψ f y) (tw_lc ψ hψ g y) (tw_cs ψ g y))

theorem intC_smul (ψ : AddChar k Circle) (hψ : Continuous ψ) (c : ℂ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intC ψ (c • f) y = c • intC ψ f y :=
  (congrArg (@smInt _ _ (borel _) _ _ (muD k (t + 1))) (tw_smul ψ c f y)).trans
    (muD_smul (t + 1) c (tw_lc ψ hψ f y) (tw_cs ψ f y))

theorem scaled_add {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (T : A →ₗ[ℂ] B) (u : ℂ)
    {a b c : A} (h : a = b + c) : u • T a = u • T b + u • T c := by
  rw [h, map_add, smul_add]

theorem scaled_smul {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (T : A →ₗ[ℂ] B) (u c : ℂ)
    {a b : A} (h : a = c • b) : u • T a = c • u • T b := by
  rw [h, map_smul, smul_comm]

theorem eC_eO_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f g : XS τ σ) (c : ℂ),
    eC ψ (f + g) = eC ψ f + eC ψ g ∧ eC ψ (c • f) = c • eC ψ f ∧ eO ψ (f + g) = eO ψ f + eO ψ g ∧ eO ψ (c • f) = c • eO ψ f := by
  intro k _ _ _ _ i t ψ hψ τ σ _ _ f g c
  refine ⟨funext fun m => ?_, funext fun m => ?_, funext fun m => ?_, funext fun m => ?_⟩
  · exact scaled_add (qC τ σ) _ (intC_add ψ hψ f g _)
  · exact scaled_smul (qC τ σ) _ c (intC_smul ψ hψ c f _)
  · exact scaled_add (qO τ σ ψ) _ (intO_add f g _)
  · exact scaled_smul (qO τ σ ψ) _ c (intO_smul c f _)

end GlobalTheory.CompanionTheory.BZPhiPG.Lin

end
