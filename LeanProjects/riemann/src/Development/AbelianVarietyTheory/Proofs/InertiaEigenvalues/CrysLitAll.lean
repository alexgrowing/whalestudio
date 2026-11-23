import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpIffMultNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparison
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineTwistCrystallineCharacterJumpsShift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInvAndHodgeTateJumpsNeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OfShortExact

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Module

namespace GlobalTheory.CrysFormalism

theorem crysLit_all : ∀ D : D7, Formalism.MainNotions.tableLineDegreeTwo.adm22 D := by
  intro D l _ K LL _
  have T := D.locT l
  refine ⟨?_, ?_, ?_⟩
  · intro μ a _ hμ hm
    refine ⟨GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg l (D.loc l) (D.locA l) T K LL μ a hμ hm, ?_⟩
    intro V _ _ _ _ _ _ _ ρ ρ' _ hρ hρ'
    have htw : IsTwistRep μ ρ ρ' := ⟨LinearEquiv.refl _ _, fun g x => by simp [hρ']⟩
    obtain ⟨hc, hmult⟩ := GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l (D.loc l) (D.locA l) T K LL
      V ρ V ρ' μ htw hμ hρ
    refine ⟨hc, fun τ b => ?_⟩
    have hj : IsJumpV ((D.loc l).PD K) (charRep μ) τ (a τ) := by
      rw [(GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l (D.loc l) (D.locA l) T K LL _ (charRep μ) τ (a τ)).2.2, hm]
      simp
    have := hmult τ (b - a τ) (a τ) hj
    rwa [sub_add_cancel] at this
  · intro V₀ V₁ V₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ₀ ρ₁ ρ₂ ι π _ _ _ hι hπ hinj hsurj hex h1
    have h0 := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) T K LL V₀ ρ₀ V₁ ρ₁ ι hι).1 hinj h1
    have h2 := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) T K LL V₁ ρ₁ V₂ ρ₂ π hπ).2 hsurj h1).1
    have hdr := GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) T K LL V₁ ρ₁ h1
    refine ⟨h0, h2, fun τ a => ?_⟩
    exact ((GlobalTheory.Per.ExactMult.exact_hodge_add l (D.loc l) (D.locA l) T K LL V₀ ρ₀ V₁ ρ₁ V₂ ρ₂ ι π
      hι hπ hinj hsurj hex hdr.1).2.2 τ a).2.1
  · intro V _ _ _ _ _ _ _ ρ _ τ
    obtain ⟨h1, _⟩ := GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) T K LL V ρ
    exact ⟨(h1 τ).1, (h1 τ).2.1⟩

end GlobalTheory.CrysFormalism
