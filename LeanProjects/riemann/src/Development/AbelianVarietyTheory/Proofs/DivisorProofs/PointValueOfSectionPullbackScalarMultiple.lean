import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecScalVal

theorem val_of_secScal : ∀ (X₂ Y : Scheme.{0}) (L₂ : LB X₂) (f₂ : Y ⟶ X₂) (k : ℕ) (σ : SecM (𝟙 X₂) L₂ k) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))) (c : Γ(Y, ⊤)), GeneratorPullback.SecScal L₂ (fun _ : Fin 1 => f₂) (fun _ => (k : ℤ)) s (fun _ : Fin 1 => 𝟙 X₂) (fun _ => (k : ℤ)) σ f₂ c → ∀ (F : Type) [CommRing F] (ξ : Sp F ⟶ Y) (i : L₂.ι), ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ L₂.U i → valR (ξ ≫ f₂) _ (σ.f fun _ => i) = valR ξ ⊤ c * valR ξ _ (s.f fun _ => i) := by
  intro X₂ Y L₂ f₂ k σ s c hs F _ ξ i hi
  have hc := hs (fun _ => i) (fun _ => i) (fun a b _ => by rcases a <;> rcases b <;> rfl)
  have hW : ⊤ ≤ ξ ⁻¹ᵁ (LB.wchart L₂ (fun _ : Fin 1 => f₂) (fun _ => i) ⊓
      LB.wchart L₂ (fun _ : Fin 1 => f₂ ≫ 𝟙 X₂) (fun _ => i)) := by
    intro y _
    have hy := hi (Set.mem_univ y)
    refine ⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩
    · simpa using hy
    · simpa using hy
  have hv := congrArg (valR ξ _) hc
  rw [GlobalTheory.ZH.CrdCalc.valR_mul ξ _ hW] at hv
  erw [GlobalTheory.ZH.CrdCalc.valR_res ξ _ hW, GlobalTheory.ZH.CrdCalc.valR_res ξ _ hW,
    GlobalTheory.ZH.CrdCalc.valR_res ξ _ hW] at hv
  have hσ : ⊤ ≤ ξ ⁻¹ᵁ f₂ ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => 𝟙 X₂) (fun _ => i) :=
    hW.trans (ξ.preimage_mono (inf_le_right.trans
      (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)))
  have hσ' : ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => 𝟙 X₂) (fun _ => i) := hσ
  rw [GlobalTheory.ZH.CrdCalc.valR_eq ξ _ hσ] at hv
  exact (GlobalTheory.ZH.CrdCalc.valR_eq (ξ ≫ f₂) _ hσ' _).trans hv

end GlobalTheory.SecScalVal
