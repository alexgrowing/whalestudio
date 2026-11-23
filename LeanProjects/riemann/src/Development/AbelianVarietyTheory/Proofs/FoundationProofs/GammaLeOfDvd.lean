import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QAllQConjOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDeltaQExpansionIntegrality
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem gamma_le_of_dvd {N N' : ℕ} (hd : N ∣ N') :
    CongruenceSubgroup.Gamma N' ≤ CongruenceSubgroup.Gamma N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  have key : ∀ x : ℤ, (x : ZMod N) = ZMod.castHom hd (ZMod N) (x : ZMod N') := fun x => by
    rw [map_intCast]
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key, h1, map_one]
  · rw [key, h2, map_zero]
  · rw [key, h3, map_zero]
  · rw [key, h4, map_one]

theorem lv_mono : ∀ (E : Subring ℂ) (N N' w w' : ℕ) (f : ℍ → ℂ), 0 < N' → N ∣ N' → w ≤ w' →
    Lv E N w f → Lv E N' w' f := by
  intro E N N' w w' f hN' hd hw hf
  refine ⟨fun γ hγ τ => hf.1 γ (gamma_le_of_dvd hd hγ) τ, fun γ => ?_⟩
  have h1 : QAll (· ∈ E) N' fun τ => DD τ ^ w * f (γ • τ) :=
    QAll.of_dvd hN' hd E.zero_mem (hf.2 γ)
  have h2 : QAll (· ∈ E) N' fun τ => DD τ ^ (w' - w) :=
    QAllSubring.pow (w' - w) (eis_qAll N' hN' DD (Or.inr (Or.inr rfl)) E)
  have h3 := QAllSubring.mul h2 h1
  refine (congrArg (QAll (· ∈ E) N') (funext fun τ => ?_)).mp h3
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hw]

end GlobalTheory.FN
