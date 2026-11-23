import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDetProdConstAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericSubquotientPrincipalSeries

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.DetProd

noncomputable section

namespace GlobalTheory.ThK.DetProd

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_twoDet (x x' : ℕ) {χ₁ χ₂ : kˣ →* ℂˣ} (h₁ : IsSmoothChar χ₁) (h₂ : IsSmoothChar χ₂) :
    IsSmoothChar (twoDet x x' χ₁ χ₂) :=
  (h₁.detChar.comp _ (continuous_apply (0 : Fin 2))).mul (h₂.detChar.comp _ (continuous_apply (1 : Fin 2)))

theorem twoDet_mulSingle (x x' : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (a : Fin 2) (u : GL (Fin (![x, x'] a)) k)
    (hu : u ∈ unipB k (Fin (![x, x'] a))) : twoDet x x' χ₁ χ₂ (Pi.mulSingle a u) = 1 := by
  have hdet : ∀ b, Matrix.GeneralLinearGroup.det
      ((Pi.mulSingle a u : ∀ b, GL (Fin (![x, x'] b)) k) b) = 1 := fun b => by
    by_cases hb : b = a
    · subst hb
      rw [Pi.mulSingle_eq_same]
      exact det_eq_one_of_mem_unipRad k hu
    · rw [Pi.mulSingle_eq_of_ne hb, map_one]
  change χ₁ (Matrix.GeneralLinearGroup.det ((Pi.mulSingle a u : ∀ b, GL (Fin (![x, x'] b)) k) 0)) *
    χ₂ (Matrix.GeneralLinearGroup.det ((Pi.mulSingle a u : ∀ b, GL (Fin (![x, x'] b)) k) 1)) = 1
  rw [hdet, hdet, map_one, map_one, one_mul]

theorem IsDetProdConst.le_one_of_isGeneric (H : GlobalTheory.Published.GenericityGL) {ψ : AddChar k Circle} (hc : Continuous ψ)
    (h1 : ψ ≠ 1) {n x x' : ℕ} {χ₁ χ₂ : kˣ →* ℂˣ} (h₁ : IsSmoothChar χ₁) (h₂ : IsSmoothChar χ₂) {V : Type}
    [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V} (h : IsDetProdConst x x' χ₁ χ₂ π)
    (hg : GlobalTheory.Whittaker.IsGeneric ψ π) : x ≤ 1 ∧ x' ≤ 1 := by
  obtain ⟨e, hs⟩ := h
  have hb := fun a => H.block_le_one hc h1 e ((isSmooth_ofChar_iff _).2 (isSmoothChar_twoDet x x' h₁ h₂)) hs hg a
    (fun u hu v => by rw [ofChar_apply, twoDet_mulSingle x x' χ₁ χ₂ a u hu]; simp)
  exact ⟨hb 0, hb 1⟩

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_isGeneric_of_isLocComp {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}
    {τ : GlobalTheory.CuspRep.CuspSub E n} {w : HeightOneSpectrum (𝓞 E)}
    {ρ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (w.adicCompletion E))} (h : τ.IsLocComp w ρ) :
    ∃ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ ∧ ψ ≠ 1 ∧ GlobalTheory.Whittaker.IsGeneric ψ ρ.ρ := by
  obtain ⟨f, hf0, hf⟩ := h
  let S : Subrepresentation (τ.locRep w) := ⟨LinearMap.range f, by
    rintro g _ ⟨v, rfl⟩
    exact ⟨ρ.ρ g v, hf g v⟩⟩
  have hS : S.toSubmodule ≠ ⊥ := fun h => hf0 (LinearMap.range_eq_bot.1 h)
  obtain ⟨ψ, hc, h1, hg⟩ := GlobalTheory.CuspDetBlocks.exists_isGeneric_subrep τ w S hS
  exact ⟨ψ, hc, h1, hg.of_surjective (σ := S.toRepresentation) ⟨f.rangeRestrict, fun g => LinearMap.ext fun v => by exact Subtype.ext (hf g v)⟩
    (LinearMap.surjective_rangeRestrict _)⟩

theorem blocks_le_one_of_isLocComp : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (τ : GlobalTheory.CuspRep.CuspSub E n)
    (w : HeightOneSpectrum (𝓞 E)) (ρ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (w.adicCompletion E))) (x x' : ℕ)
    (χ₁ χ₂ : (w.adicCompletion E)ˣ →* ℂˣ), GlobalTheory.Published.GenericityGL → 1 ≤ n → τ.IsLocComp w ρ → IsUnramAt w χ₁ →
    IsUnramAt w χ₂ → IsDetProdConstAt w x x' χ₁ χ₂ ρ.ρ → x ≤ 1 ∧ x' ≤ 1 := by
  intro E _ _ _ n τ w ρ x x' χ₁ χ₂ H _ hρ h₁ h₂ hc
  obtain ⟨ψ, hψ, h1, hg⟩ := exists_isGeneric_of_isLocComp hρ
  exact IsDetProdConst.le_one_of_isGeneric H hψ h1 (isSmoothChar_of_isUnram h₁) (isSmoothChar_of_isUnram h₂) hc hg

end GlobalTheory.ThK.DetProd

end
