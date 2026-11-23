import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ToOneSucc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExDownExUpAndExUpExDown
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearIsQuotIntTIntStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantIntegralSuccPositionEqExchangeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilSourceActionAndSmoothStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

noncomputable section
namespace GlobalTheory.PosOneIntegral

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def omRight (μ : kˣ →* ℂˣ) : Representation ℂ (GL n k) (SB (Matrix n n' k)) where
  toFun g :=
    { toFun := fun Ψ => ⟨om μ (1 : GL n' k) g Ψ.1, om_mem_SB μ 1 g Ψ.2⟩
      map_add' := fun Φ Ψ => by
        apply Subtype.ext
        funext x
        simp only [om, Submodule.coe_add, Pi.add_apply]
        ring
      map_smul' := fun z Φ => by
        apply Subtype.ext
        funext x
        simp only [om, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  map_one' := by
    apply LinearMap.ext
    intro Ψ
    apply Subtype.ext
    exact om_one μ Ψ.1
  map_mul' g h := by
    apply LinearMap.ext
    intro Ψ
    apply Subtype.ext
    show om μ (1 : GL n' k) (g * h) Ψ.1 = om μ 1 g (om μ 1 h Ψ.1)
    rw [← om_mul μ 1 1 g h Ψ.1, mul_one]

@[simp] theorem omRight_apply (μ : kˣ →* ℂˣ) (g : GL n k) (Ψ : SB (Matrix n n' k)) :
    ((omRight (n' := n') μ g Ψ : SB (Matrix n n' k)) : Matrix n n' k → ℂ) = om μ 1 g Ψ.1 := rfl

variable {c : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]

theorem bilPos_iff_isPos (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (p : ℕ)
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) :
    BilPos ψ μ p σ B ↔ IsPos ψ p (omRight μ) σ B := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun g Ψ v => h2 g Ψ _ v rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun g Ψ Ψ₁ v hΨ => ?_⟩
    have : Ψ₁ = omRight μ g Ψ := Subtype.ext hΨ
    rw [this]
    exact h2 g Ψ v

end GlobalTheory.PosOneIntegral
end

open GlobalTheory.PosOneIntegral in
theorem GlobalTheory.PosOneIntegral.positionOne_invariantIntegral_exchange_step (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k) (hν : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (hμ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (hσ : IsSmoothRep σ) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (hρ' : IsSrc μ ρ') :
    ∀ q : ℕ, q + 1 ≤ c → ∀ (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), BilPos ψ μ (q + 1) σ B →
      ∀ (Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ),
      (∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG (q + 1) (tInt ψ ν μ (q + 1) σ B F Φ.1) (Rr Φ)) →
      ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
        IsQuotInt ν μX μG 1 (tIntOne ψ ν μ (q + 1) σ B F Φ.1) (toOne ν ρ' (q + 1) Rr Φ) := by
  haveI : ν.IsAddHaarMeasure := hν.1
  intro q
  induction q with
  | zero =>
    intro _ B _ Rr hRr Φ
    exact hRr Φ
  | succ q ih =>
    intro hqc B hB Rr hRr Φ
    have hq1 : 1 ≤ q + 1 := Nat.succ_le_succ (Nat.zero_le q)
    have hqlt : q + 1 < c := by omega

    obtain ⟨B₀, hB₀e, hB₀⟩ := ((GlobalTheory.RootEx.Exchange.exchange_isPos k n c (q + 1) hq1 hqlt ψ hψc hψ1 ν A σ hσ).2.2
      (SB (Matrix n n' k)) (omRight μ) B).2 ((bilPos_iff_isPos ψ μ _ σ B).1 hB)
    have hB₀' : BilPos ψ μ (q + 1) σ B₀ := (bilPos_iff_isPos ψ μ _ σ B₀).2 hB₀
    have hB₀f : ∀ Ψ, (⇑(B₀ Ψ) : A → ℂ) = exDown ν (q + 1) σ (⇑(B Ψ)) := fun Ψ => funext (hB₀e Ψ)

    have hsm' : IsSmoothRep ρ' := (GlobalTheory.T.exists_weilSourceAction_and_smooth k (n' ⊕ Fin (c + 1)) (n ⊕ Fin c) μ hμ).2 ρ' hρ'
    obtain ⟨Rr₀, hRr₀, hRr₀N⟩ := GlobalTheory.T.exists_linear_isQuotInt_tInt_alt k n n' c (q + 1) hq1 hqlt.le ψ hψc hψ1 ν μ hμ μX μG A σ hσ B₀ hB₀' F ρ' hρ'
    have hIH := ih hqlt.le B₀ hB₀' Rr₀ hRr₀ Φ

    have hBup : ∀ Ψ v, B Ψ v = exUp ν (q + 1) σ (B₀ Ψ) v := by
      intro Ψ v
      rw [hB₀f Ψ]
      exact ((GlobalTheory.RootEx.exDown_exUp_and_exUp_exDown k n c (q + 1) hq1 hqlt ψ hψc hψ1 ν hν A σ hσ (B Ψ) v).2
        (hB.1 Ψ)).symm

    have hRrup : ∀ Φ', Rr Φ' = exUp ν (q + 1) ρ' Rr₀ Φ' := by
      intro Φ'
      have hst := GlobalTheory.T.invariantIntegral_succ_position_eq_exchange k n n' c (q + 1) hq1 hqlt ψ hψc hψ1 ν hν μ hμ μX μG A σ hσ B₀ B hB₀' hBup F ρ' hρ' Rr₀ hRr₀ Φ'
      exact (GlobalTheory.QuotInt.quotInt_unique_exists k n c (q + 1 + 1) (by omega) hqc ν μX μG _).1 _ _ (hRr Φ') hst
    have hdown : exDown ν (q + 1) ρ' (⇑Rr) = ⇑Rr₀ := by
      funext v
      have hRrf : (⇑Rr : _ → ℂ) = exUp ν (q + 1) ρ' ⇑Rr₀ := funext hRrup
      rw [hRrf]
      exact (GlobalTheory.RootEx.exDown_exUp_and_exUp_exDown k n' (c + 1) (q + 1) hq1 (by omega) ψ hψc hψ1 ν hν _ ρ' hsm' Rr₀ v).1 hRr₀N
    have hval : toOne ν ρ' (q + 1 + 1) Rr Φ = toOne ν ρ' (q + 1) Rr₀ Φ := by
      rw [toOne_succ, hdown]
    have hfun : tIntOne ψ ν μ (q + 1 + 1) σ B F Φ.1 = tIntOne ψ ν μ (q + 1) σ B₀ F Φ.1 := by
      funext h
      simp only [tIntOne]
      rw [toOne_succ]
      congr 1
      funext v
      by_cases hm : opE ψ ν 1 (om μ 1 h Φ.1) ∈ SB (Matrix n n' k)
      · simp only [app, hm, dite_true]
        exact congrFun (hB₀f _).symm v
      · simp [app, hm, exDown]
    rw [hfun, hval]
    exact hIH

theorem GlobalTheory.PosOneIntegral.isQuotInt_toOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ P σ B) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ) (_ : ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG P (tInt ψ ν μ P σ B F Φ.1) (Rr Φ)) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), IsQuotInt ν μX μG 1 (tIntOne ψ ν μ P σ B F Φ.1) (toOne ν ρ' P Rr Φ) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c P hP1 hPc ψ hψc hψ1 ν hν μ hμ μX _ μG _ A _ _ σ hσ B hB F ρ' hρ' Rr hRr Φ
  obtain ⟨q, rfl⟩ : ∃ q, P = q + 1 := ⟨P - 1, by omega⟩
  exact GlobalTheory.PosOneIntegral.positionOne_invariantIntegral_exchange_step k n n' c ψ hψc hψ1 ν hν μ hμ μX μG A σ hσ F ρ' hρ' q hPc B hB Rr hRr Φ
