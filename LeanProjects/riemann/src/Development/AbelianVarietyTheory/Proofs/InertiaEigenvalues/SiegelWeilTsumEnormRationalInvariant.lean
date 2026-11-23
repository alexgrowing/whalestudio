import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OmRatInvApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActEquivSymmApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.SWAbsInv

open GlobalTheory.RallisCusp

variable {D : D7}

def lagSwap (W : HSp D) (Y : Lag W) : Lag W :=
  ⟨Y.1.map (LinearEquiv.prodComm D.host.E (Fin W.rank → D.host.E) (Fin W.rank → D.host.E)).toLinearMap, by rw [LinearEquiv.finrank_map_eq]; exact Y.2.1, by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    exact (Y.2.2 y hy y' hy').symm⟩

theorem lagSwap_lagSwap (W : HSp D) (Y : Lag W) : lagSwap W (lagSwap W Y) = Y := by
  apply Subtype.ext
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact hz
  · intro hy
    exact ⟨y.swap, ⟨y, hy, rfl⟩, rfl⟩

theorem isLagFrame_lagSwap (W : HSp D) (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E ×
    Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : IsLagFrame W Y C) : IsLagFrame W (lagSwap W Y) (C.2, C.1) := by
  unfold IsLagFrame at h ⊢
  change _ = Submodule.map (LinearEquiv.prodComm D.host.E _ _).toLinearMap Y.1
  rw [← h, Submodule.map_span, ← Set.range_comp]
  congr 2

theorem lagTerm_swap {V W : HSp D} (μ : Measure (WO V W)) (𝓕 : Set (WO V W))
    (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E) (f₁ f₂ : WO V W → ℂ) :
    lagTerm μ 𝓕 (C.2, C.1) f₂ f₁ = star (lagTerm μ 𝓕 C f₁ f₂) := by
  unfold lagTerm
  rw [Complex.star_def, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp [mul_comm]

section

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {νV : Measure (GA D V)}
    {𝓗 : Set (GA D V)} {νW : Measure (GA D W)} {𝓖 : Set (GA D W)} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}
    {fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}

theorem tsum_comm (hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) {f₁ f₂ : WO V W → ℂ} (h₁ : IsThetaFunO ψ V W f₁)
    (h₂ : IsThetaFunO ψ V W f₂) :
    ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) f₂ f₁‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) f₁ f₂‖ₑ := by
  let e : Lag W ≃ Lag W := ⟨lagSwap W, lagSwap W, lagSwap_lagSwap W, lagSwap_lagSwap W⟩
  rw [← e.tsum_eq]
  refine tsum_congr fun Y => ?_
  have h := (Move.termMove D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₂ f₁ h₂ h₁).1 (lagSwap W Y) _
    (isLagFrame_lagSwap W Y (fr Y) (hS.frame Y))
  change ‖lagTerm μ 𝓕 (fr (lagSwap W Y)) f₂ f₁‖ₑ = _
  rw [← h, lagTerm_swap, ← ofReal_norm_eq_enorm, norm_star, ofReal_norm_eq_enorm]

theorem tsum_left (hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) {f₁ f₂ : WO V W → ℂ} (h₁ : IsThetaFunO ψ V W f₁)
    (h₂ : IsThetaFunO ψ V W f₂) {γ : GA D W} (hγ : γ ∈ GQ W) :
    ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ) f₁) f₂‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) f₁ f₂‖ₑ := by
  let g : GQ W := ⟨γ, hγ⟩
  let e : Lag W ≃ Lag W := ⟨lagAct W g, lagAct W g⁻¹,
    fun Y => by rw [← lagAct_mul, inv_mul_cancel, lagAct_one],
    fun Y => by rw [← lagAct_mul, mul_inv_cancel, lagAct_one]⟩
  rw [← e.tsum_eq]
  refine tsum_congr fun Y => ?_
  have h := (Move.termMove D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS _ f₂ (hS.weil.om_pres (1, γ) f₁ h₁) h₂).1
    (lagAct W g Y) _ (isLagFrame_lagAct W g Y (fr Y) (hS.frame Y))
  have h' := ((Move.termMove D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ f₂ h₁ h₂).2 γ hγ (gqMat W g)
    (gqMat_map W g).symm).1 (fr Y)
  change ‖lagTerm μ 𝓕 (fr (lagAct W g Y)) (om (1, γ) f₁) f₂‖ₑ = _
  rw [← h, h']

end

theorem tsum_enorm_lagTerm_rat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (F₁ F₂ : WO V W → ℂ), IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₂ → ∀ γ₁ ∈ GQ W, ∀ γ₂ ∈ GQ W, ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ₁) F₁) (om (1, γ₂) F₂)‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) F₁ F₂‖ₑ := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS F₁ F₂ h₁ h₂ γ₁ hγ₁ γ₂ hγ₂
  have p₂ := hS.weil.om_pres (1, γ₂) F₂ h₂
  rw [tsum_left hS h₁ p₂ hγ₁, tsum_comm hS p₂ h₁, tsum_left hS h₂ h₁ hγ₂, tsum_comm hS h₁ h₂]

end GlobalTheory.SWAbsInv

end
