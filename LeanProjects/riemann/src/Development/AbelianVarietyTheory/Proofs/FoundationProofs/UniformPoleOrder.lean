import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDeltaQExpansionIntegrality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem uniform_pole_order : ∀ (E : Subring ℂ) (M : ℕ) (f : ℍ → ℂ), 0 < M →
    (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, f (γ • τ) = f τ) →
    (∀ γ : SL(2, ℤ), ∃ w : ℕ, QAll (· ∈ E) M fun τ => DD τ ^ w * f (γ • τ)) → ∃ w : ℕ, Lv E M w f := by
  intro E M f hM hinv hw
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  choose w hw using hw
  let red : SL(2, ℤ) →* SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))
  let lift : SL(2, ZMod M) → SL(2, ℤ) := fun g => if h : ∃ γ, red γ = g then h.choose else 1
  let W : ℕ := Finset.univ.sup fun g => w (lift g)
  refine ⟨W, hinv, fun γ => ?_⟩
  have hex : ∃ γ', red γ' = red γ := ⟨γ, rfl⟩
  have hl : lift (red γ) = hex.choose := dif_pos hex
  set γ' := lift (red γ) with hγ'
  have hred : red γ' = red γ := by rw [hl]; exact hex.choose_spec
  have hmem : γ * γ'⁻¹ ∈ CongruenceSubgroup.Gamma M := by
    rw [CongruenceSubgroup.Gamma_mem']
    show red (γ * γ'⁻¹) = 1
    rw [map_mul, map_inv, hred, mul_inv_cancel]
  have hf : ∀ τ : ℍ, f (γ • τ) = f (γ' • τ) := fun τ => by
    have := hinv _ hmem (γ' • τ)
    rw [← this, ← mul_smul, inv_mul_cancel_right]
  have hle : w γ' ≤ W := Finset.le_sup (f := fun g => w (lift g)) (Finset.mem_univ (red γ))
  have hD : QAll (· ∈ E) M fun τ => DD τ ^ (W - w γ') :=
    QAllSubring.pow _ (eis_qAll M hM DD (Or.inr (Or.inr rfl)) E)
  have := QAllSubring.mul hD (hw γ')
  convert this using 2 with τ
  rw [hf τ, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

end GlobalTheory.FN
