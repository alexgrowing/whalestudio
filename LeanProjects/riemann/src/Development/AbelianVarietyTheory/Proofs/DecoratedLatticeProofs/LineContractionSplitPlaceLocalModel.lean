import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousKappa
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontriviaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineContractionHeisenbergInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineRowTranslationHeisenbergSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineColumnTranslationHeisenbergStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineContractionThetaFunctionIsLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionIsLocalModelSecondVariableStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ContrLocProof
open GlobalTheory.ContractionLocal

theorem contrLoc : ∀ (D : D7), GlobalTheory.LocFlat.ContrFactor → ContrLoc D := by
  have hH := GlobalTheory.T.besselLineContraction_heisenberg_invariant
  have hC := GlobalTheory.T.lineRow_translation_heisenberg_splitPlace
  have hD := GlobalTheory.T.splitPlace_lineColumn_translation_heisenberg
  have hL := GlobalTheory.T.besselLine_contraction_thetaFunction_isLocalModel
  have hR := GlobalTheory.T.thetaContraction_isLocalModel_secondVariable
  intro D hCF k _ _ _ _ _ _ p ν hν ψ hψ ψk hk ρ σ B B' l S vL s hs n n' n'' _ _ _ _ _ _ FA F₀ FS FA' F₀' hF hF' T₁ T₂ hT₁ hT₂
  obtain ⟨-, hψk, -, -, -⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hψ
  obtain ⟨hψkc, hψk1⟩ := hψk ψk hk
  let Bm := contrBil hψ l S vL T₁ T₂ hT₁.theta hT₂.theta
  have inv1 : ∀ (u₀ : n → k) Ψ₁ Ψ₁' Ψ₂ Ψ₂',
      (∀ x, Ψ₁'.1 x = (ψk (-(u₀ ⬝ᵥ fun r => x r (Sum.inr ()))) : ℂ) * Ψ₁.1 x) →
      (∀ x, Ψ₂'.1 x = Ψ₂.1 (x + fromRows 0 (Matrix.of fun _ => u₀))) → Bm Ψ₁' Ψ₂' = Bm Ψ₁ Ψ₂ := by
    intro u₀ Ψ₁ Ψ₁' Ψ₂ Ψ₂' h1 h2
    obtain ⟨x, hx1, hx2, hx3⟩ := hC D k p ψ hψ ψk hk ρ σ B B' l S s hs n n' n'' FA F₀ FS FA' F₀' hF hF' u₀
    have e1 : T₁ Ψ₁' = heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) (T₁ Ψ₁) :=
      hT₁.modul _ hx2 Ψ₁ Ψ₁' fun t => by rw [h1, hx3]
    have e2 : T₂ Ψ₂' = heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) (T₂ Ψ₂) := by
      rw [← hx1]; exact hT₂.trans _ Ψ₂ Ψ₂' h2
    simp only [Bm, contrBil_apply, e1, e2]
    exact hH D ψ hψ ρ σ B B' l S vL _ _ (hT₁.theta Ψ₁) (hT₂.theta Ψ₂) x
  have inv2 : ∀ (y₀ : n → k) Ψ₁ Ψ₁' Ψ₂ Ψ₂',
      (∀ x, Ψ₁'.1 x = Ψ₁.1 (x + fromCols 0 (Matrix.of fun r _ => y₀ r))) →
      (∀ x, Ψ₂'.1 x = (ψk (-(x (Sum.inr ()) ⬝ᵥ y₀)) : ℂ) * Ψ₂.1 x) → Bm Ψ₁' Ψ₂' = Bm Ψ₁ Ψ₂ := by
    intro y₀ Ψ₁ Ψ₁' Ψ₂ Ψ₂' h1 h2
    obtain ⟨x, hx1, hx2, hx3⟩ := hD D k p ψ hψ ψk hk ρ σ B B' l S s hs n n' n'' FA F₀ FS FA' F₀' hF hF' y₀
    have e1 : T₁ Ψ₁' = heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) (T₁ Ψ₁) := by
      rw [← hx1]; exact hT₁.trans _ Ψ₁ Ψ₁' h1
    have e2 : T₂ Ψ₂' = heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) (T₂ Ψ₂) :=
      hT₂.modul _ hx2 Ψ₂ Ψ₂' fun t => by rw [h2, hx3]
    simp only [Bm, contrBil_apply, e1, e2]
    exact hH D ψ hψ ρ σ B B' l S vL _ _ (hT₁.theta Ψ₁) (hT₂.theta Ψ₂) x
  obtain ⟨Λ, hΛ⟩ := hCF k ψk ν hψkc hψk1 hν n n' n'' (WO B.A S → WO S B'.A → ℂ) Bm inv1 inv2
  obtain ⟨φ₀, φ₀', hφ⟩ := exists_normPair ψk ν hψkc hν n
  have hval : ∀ Ξ₁ Ξ₂ (Ξ : SB (Matrix n n' k × Matrix n'' n k)), (∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2) →
      Λ Ξ = Bm (colTens φ₀ Ξ₁) (rowTens φ₀' Ξ₂) := by
    intro Ξ₁ Ξ₂ Ξ hq
    obtain ⟨Ξ', hΞ'1, hΞ'2⟩ := hΛ (colTens φ₀ Ξ₁) (rowTens φ₀' Ξ₂)
    have : Ξ' = Ξ := Subtype.ext (funext fun q => by rw [hΞ'1, contr_tens, hφ, mul_one, hq])
    rw [← this, hΞ'2]
  refine ⟨Λ, ⟨fun Ξ₂ v => ?_, fun Ξ₁ u => ?_⟩, hΛ⟩
  · let T : SB (Matrix n n' k) →ₗ[ℂ] (WO B.A S → ℂ) :=
      { toFun := fun Ξ₁ u => Bm (colTens φ₀ Ξ₁) (rowTens φ₀' Ξ₂) u v
        map_add' := fun a b => by funext u; simp only [map_add, LinearMap.add_apply, Pi.add_apply]
        map_smul' := fun c a => by funext u; simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply] }
    refine ⟨T, hL D k p ψ hψ ρ σ B B' l S vL s hs n n' FA F₀ FS hF T₁ hT₁ φ₀ _ (hT₂.theta _) v T fun Ξ₁ u => rfl,
      fun Ξ₁ Ξ hq u => ?_⟩
    rw [hval Ξ₁ Ξ₂ Ξ hq]; rfl
  · let T : SB (Matrix n'' n k) →ₗ[ℂ] (WO S B'.A → ℂ) :=
      { toFun := fun Ξ₂ v => Bm (colTens φ₀ Ξ₁) (rowTens φ₀' Ξ₂) u v
        map_add' := fun a b => by funext v; simp only [map_add, Pi.add_apply]
        map_smul' := fun c a => by funext v; simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }
    refine ⟨T, hR D k p ψ hψ ρ σ B B' l S vL (s * p.xi) ?_ n n'' FS FA' F₀' hF' T₂ hT₂ φ₀' _ (hT₁.theta _) u T
      fun Ξ₂ v => rfl, fun Ξ₂ Ξ hq v => ?_⟩
    · obtain ⟨-, -, hxi, -, -⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hψ
      exact mul_ne_zero hs hxi
    rw [hval Ξ₁ Ξ₂ Ξ hq]; rfl
end GlobalTheory.ContrLocProof

end
