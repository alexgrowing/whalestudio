import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.VacAway

variable {D : D7}

def combL (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f g := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring

theorem comb_single_one (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (y : WO S T) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single y 1) f = heisO ψ S T y f := by
  unfold comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]

theorem vac_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q₀ : QStep S) (c₁ : WO S.B.V S.J.W →₀ ℂ) (c₂ : WO S.J.W S.B'.V →₀ ℂ), IsFinComb c₁ → IsFinComb c₂ → Q₀.Away c₁ → Q₀.Away c₂ → ∀ f₁ f₂, IsThetaFunO ψ _ _ f₁ → IsThetaFunO ψ _ _ f₂ → Q₀.Vac f₁ f₂ → Q₀.Vac (comb ψ _ _ c₁ f₁) (comb ψ _ _ c₂ f₂) := by
  intro D ψ hψ σ S Q₀ c₁ c₂ hc₁ hc₂ ha₁ ha₂ f₁ f₂ _ _ hv
  obtain ⟨hee, hec, -⟩ := Q₀.q.split
  have hce : cA D Q₀.q.e * Q₀.q.e = 0 := by rw [mul_comm, hec]
  have hcc : cA D Q₀.q.e * cA D Q₀.q.e = cA D Q₀.q.e := by rw [← map_mul, hee]
  have hreal : cA D (Q₀.q.e + cA D Q₀.q.e) = Q₀.q.e + cA D Q₀.q.e := by
    rw [map_add, Formalism.L2.Theta.cA_cA, add_comm]
  have hidem : (Q₀.q.e + cA D Q₀.q.e) * (Q₀.q.e + cA D Q₀.q.e) = Q₀.q.e + cA D Q₀.q.e := by
    rw [add_mul, mul_add, mul_add, hee, hec, hce, hcc, add_zero, zero_add]
  have horth : (Q₀.q.e + cA D Q₀.q.e) * (1 - (Q₀.q.e + cA D Q₀.q.e)) = 0 := by
    rw [mul_sub, mul_one, hidem, sub_self]
  have comm : ∀ {A B : HSp D} (c : WO A B →₀ ℂ), Q₀.Away c → ∀ (f : WO A B → ℂ) (y : WO A B),
      IsHalf (Q₀.q.e + cA D Q₀.q.e) y → comb ψ A B c (heisO ψ A B y f) = heisO ψ A B y (comb ψ A B c f) := by
    intro A B c ha f y hy
    have h := (GlobalTheory.HeisComb.main D ψ A B).2.1 (Finsupp.single y 1) c (fun x hx u hu => by
      have hxy : x = y := Finset.mem_singleton.1 (Finsupp.support_single_subset hx)
      subst hxy
      exact GlobalTheory.HeisComb.symplO_half A B _ _ x u hreal horth hy (ha u hu)) f
    rw [comb_single_one, comb_single_one] at h
    exact h.symm
  obtain ⟨⟨T₁, O₁, hT₁, hO₁, rfl⟩, ⟨T₂, O₂, hT₂, hO₂, rfl⟩⟩ := hv
  refine ⟨⟨combL ψ _ _ c₁ ∘ₗ T₁, O₁, ?_, hO₁, rfl⟩, ⟨combL ψ _ _ c₂ ∘ₗ T₂, O₂, ?_, hO₂, rfl⟩⟩
  · exact (GlobalTheory.LocModU.localModel_uniq_transport_exist D Q₀.k (ofSplit Q₀.q) _ _ _ _ Q₀.F.G₀ Q₀.F.G₁ ψ hψ).2.1 T₁ hT₁
      (combL ψ _ _ c₁) (fun f hf => (GlobalTheory.HeisComb.main D ψ _ _).2.2.1 c₁ f hf hc₁ hψ)
      (fun f _ y hy => comm c₁ ha₁ f y hy)
  · exact (GlobalTheory.LocModU.localModel_uniq_transport_exist D Q₀.k (ofSplit Q₀.q) _ _ _ _ Q₀.F.G₁ Q₀.F.G₂ ψ hψ).2.1 T₂ hT₂
      (combL ψ _ _ c₂) (fun f hf => (GlobalTheory.HeisComb.main D ψ _ _).2.2.1 c₂ f hf hc₂ hψ)
      (fun f _ y hy => comm c₂ ha₂ f y hy)

end GlobalTheory.VacAway

end
