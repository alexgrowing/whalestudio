import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZpowCrysDRJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

namespace CrystallineMultiplicity
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.CompanionTheory.CharInv

theorem isCrys_and_multV_inv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ) (a : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ), IsCrys (P.PD K) (charRep μ) → (∀ τ b, multV (P.PD K) (charRep μ) τ b = if b = a τ then 1 else 0) → IsCrys (P.PD K) (charRep μ⁻¹) ∧ ∀ τ b, multV (P.PD K) (charRep μ⁻¹) τ b = if b = -a τ then 1 else 0 := by
  intro l _ P AI T K LL μ a hμ hm
  obtain ⟨h1, -, h2⟩ := GlobalTheory.CycPow.cyc_zpow_crys_dR_jump l P AI T K LL 0
  rw [zpow_zero] at h1
  simp only [zpow_zero] at h2
  have hρ : ∀ g x, charRep (1 : ↥(GK K) →* (↥LL.1)ˣ) g x = (μ g : ↥LL.1) • charRep μ⁻¹ g x :=
    fun g x => by simp [charRep]
  refine ⟨(GlobalTheory.TopSteps.CrysRules.isCrys_iff T K LL _ _ μ hρ hμ).2 h1, fun τ c => ?_⟩
  have hs := GlobalTheory.TopSteps.CrysRules.multV_shift T K LL _ _ μ hρ hμ τ (a τ)
    (fun b => by rw [hm, Multiset.count_singleton]; split_ifs <;> rfl) c
  rw [← hs, h2]
  exact if_congr (by omega) rfl rfl

end GlobalTheory.CompanionTheory.CharInv

end

end CrystallineMultiplicity
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
theorem _root_.GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ) (a : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ), IsCrys (P.PD K) (charRep μ) → (∀ τ b, multV (P.PD K) (charRep μ) τ b = if b = a τ then 1 else 0) → IsCrys (P.PD K) (charRep μ⁻¹) ∧ ∀ τ b, multV (P.PD K) (charRep μ⁻¹) τ b = if b = -a τ then 1 else 0 := by
  first | exact @CrystallineMultiplicity.GlobalTheory.CompanionTheory.CharInv.isCrys_and_multV_inv | exact CrystallineMultiplicity.GlobalTheory.CompanionTheory.CharInv.isCrys_and_multV_inv | (intros; apply CrystallineMultiplicity.GlobalTheory.CompanionTheory.CharInv.isCrys_and_multV_inv <;> assumption)

end
