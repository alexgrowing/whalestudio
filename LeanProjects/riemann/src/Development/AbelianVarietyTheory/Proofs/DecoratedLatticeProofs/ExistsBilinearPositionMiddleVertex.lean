import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearIsQuotIntTIntStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsQuotientInvariantIntegralExchangeToPositionOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingAffPtUncurry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralLinear
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

noncomputable section
namespace GlobalTheory.PosOne.MidVertex

theorem exists_bilPos_mid : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ) (_ : c + 1 = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ₁ μ₂ : kˣ →* ℂˣ) (_ : IsOpen (μ₁.ker : Set kˣ)) (_ : IsOpen (μ₂.ker : Set kˣ)) (m₁ : Measure (GL n₁ k)) [m₁.IsHaarMeasure] (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) [G₁.IsHaarMeasure] (m₂ : Measure (GL n₂ k)) [m₂.IsHaarMeasure] (G₂ : Measure (GL (n₂ ⊕ Fin c) k)) [G₂.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : TriPos ψ μ₁ μ₂ ρ σ T) (F : A) (ρ₁ : Representation ℂ (GL (n₁ ⊕ Fin (c + 1)) k) (SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k))) (_ : IsSrc μ₂ ρ₁), ∃ b : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ, BilPos ψ μ₁ ρ ρ₁ b ∧ (∀ Ψ (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)), IsQuotInt ν m₂ G₂ ρ (tInt ψ ν μ₂ ρ σ (T Ψ) F Φ₂.1) (b Ψ Φ₂)) ∧ ∀ Ψ (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)), IsQuotInt ν m₂ G₂ 1 (tIntOne ψ ν μ₂ ρ σ (T Ψ) F Φ₂.1) (toOne ν ρ₁ ρ (b Ψ) Φ₂) := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hc ψ hψc hψ1 ν hsd μ₁ μ₂ hk₁ hk₂ m₁ _ G₁ _ m₂ _ G₂ _ A _ _ σ hσ T hT F ρ₁ hsrc
  haveI : ν.IsAddHaarMeasure := hsd.1
  have h1 : 1 ≤ ρ := by omega
  have h2 : ρ ≤ c := by omega
  have hR := fun Ψ => GlobalTheory.T.exists_linear_isQuotInt_tInt_alt k n₂ n₁ c ρ h1 h2 ψ hψc hψ1 ν μ₂ hk₂ m₂ G₂ A σ hσ (T Ψ) (hT.1 Ψ) F ρ₁ hsrc
  choose R hQ hN using hR
  have uniq : ∀ (f : GL (n₂ ⊕ Fin c) k → ℂ) (z z' : ℂ), IsQuotInt ν m₂ G₂ ρ f z → IsQuotInt ν m₂ G₂ ρ f z' → z = z' :=
    fun f z z' => (GlobalTheory.QuotInt.quotInt_unique_exists k n₂ c ρ h1 h2 ν m₂ G₂ f).1 z z'
  have lin := fun f f' a z z' => GlobalTheory.RootEx.QuotLinear.isQuotInt_linear k n₂ c ρ h1 h2 ν m₂ G₂ f f' a z z'
  have key : ∀ (a : ℂ) Ψ Ψ' Φ, R (a • Ψ + Ψ') Φ = a * R Ψ Φ + R Ψ' Φ := by
    intro a Ψ Ψ' Φ
    have h := lin _ _ a _ _ (hQ Ψ Φ) (hQ Ψ' Φ)
    have hf : (fun h => a * tInt ψ ν μ₂ ρ σ (T Ψ) F Φ.1 h + tInt ψ ν μ₂ ρ σ (T Ψ') F Φ.1 h) =
        tInt ψ ν μ₂ ρ σ (T (a • Ψ + Ψ')) F Φ.1 := by
      funext h
      simp only [tInt, app, map_add, map_smul]
      split_ifs <;> simp
    rw [hf] at h
    exact uniq _ _ _ (hQ _ Φ) h
  have hz : ∀ Φ, R 0 Φ = 0 := by
    intro Φ
    have := key 1 0 0 Φ
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination -this
  let b : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ :=
    { toFun := R
      map_add' := fun Ψ Ψ' => by
        ext Φ
        have := key 1 Ψ Ψ' Φ
        simpa using this
      map_smul' := fun a Ψ => by
        ext Φ
        have := key a Ψ 0 Φ
        simp only [add_zero] at this
        simp [this, hz] }
  refine ⟨b, ⟨fun Ψ => hN Ψ, ?_⟩, fun Ψ Φ₂ => hQ Ψ Φ₂, fun Ψ Φ₂ =>
    GlobalTheory.T.isQuotientInvariantIntegral_exchange_toPositionOne k n₂ n₁ c ρ h1 h2 ψ hψc hψ1 ν hsd μ₂ hk₂ m₂ G₂ A σ hσ (T Ψ) (hT.1 Ψ) F ρ₁ hsrc (R Ψ) (hQ Ψ) Φ₂⟩
  intro g Ψ Ψ₁ v hΨ
  show R Ψ₁ (ρ₁ (embX (c + 1) g) v) = _ * R Ψ v
  set s : ℂ := ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 2) / 2 - ρ) : ℝ) : ℂ) with hs
  have hexp : ((((c + 1 : ℕ) : ℝ) + 1) / 2 - (ρ : ℝ)) = ((c : ℝ) + 2) / 2 - ρ := by push_cast; ring
  rw [hexp]
  have hfun : tInt ψ ν μ₂ ρ σ (T Ψ₁) F (ρ₁ (embX (c + 1) g) v).1 =
      fun h => (s - 1) * tInt ψ ν μ₂ ρ σ (T Ψ) F v.1 h + tInt ψ ν μ₂ ρ σ (T Ψ) F v.1 h := by
    funext h
    have hv : ((ρ₁ (embX (c + 1) g) v : SB _) : Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k → ℂ) =
        om μ₂ (embX (c + 1) g) 1 v.1 := hsrc _ _
    have hcomm : om μ₂ 1 h (om μ₂ (embX (c + 1) g) 1 v.1) = om μ₂ (embX (c + 1) g) 1 (om μ₂ 1 h v.1) := by
      rw [← om_mul, ← om_mul, one_mul, mul_one, mul_one, one_mul]
    have hΦ' : om μ₂ 1 h v.1 ∈ SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) := om_mem_SB μ₂ 1 h v.2
    have hX := (GlobalTheory.RootEx.opE_SB_and_linear k n₂ n₁ c ρ ψ hψc ν).1 _ hΦ'
    have hE' := (GlobalTheory.RootEx.opE_om_embX k n₂ n₁ c ρ h1 h2 ψ ν μ₂ (om μ₂ 1 h v.1)).2 g
    have hX' : om μ₂ g 1 (opE ψ ν ρ (om μ₂ 1 h v.1)) ∈ SB (Matrix n₂ n₁ k) := om_mem_SB μ₂ g 1 hX
    have hinv := hT.2 g Ψ Ψ₁ ⟨_, hX⟩ ⟨_, hX'⟩ hΨ rfl
    simp only [tInt]
    rw [hv, hcomm, hE']
    have e1 : ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 2) / 2 - ρ) : ℝ) : ℂ) •
        om μ₂ g 1 (opE ψ ν ρ (om μ₂ 1 h v.1)) = ((s • (⟨_, hX'⟩ : SB (Matrix n₂ n₁ k)) : SB _) : Matrix n₂ n₁ k → ℂ) := by
      rfl
    have e2 : app (T Ψ) (opE ψ ν ρ (om μ₂ 1 h v.1)) = T Ψ ⟨_, hX⟩ := GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe _ ⟨_, hX⟩
    rw [e1, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe, e2, map_smul, hinv]
    simp only [LinearMap.smul_apply, smul_eq_mul]
    ring
  have h := lin _ _ (s - 1) _ _ (hQ Ψ v) (hQ Ψ v)
  rw [← hfun] at h
  rw [uniq _ _ _ (hQ Ψ₁ _) h]
  ring

end GlobalTheory.PosOne.MidVertex
