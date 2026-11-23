import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDetProdConstAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSignatureSum
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.DetProd

open scoped TensorProduct

namespace GlobalTheory.GoodPlaceUnr

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem valuation_eq_one_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x = 1 ↔ Valued.v x = 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one

end

theorem isUnramAt_of_unrAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ : (AF F ⊗[F] E)ˣ →* Circle} {w : HeightOneSpectrum (𝓞 E)} (h : GlobalTheory.LFun.UnrAt χ w) :
    IsUnramAt w (GlobalTheory.LFun.locChar χ w) := by
  intro x hx
  exact h x ((valuation_eq_one_iff w (x : w.adicCompletion E)).1 hx)

theorem unram_of_good : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ w : HeightOneSpectrum (𝓞 E), X.Good (w.under (𝓞 F)) →
      GlobalTheory.ThK.DetProd.IsUnramAt w (GlobalTheory.LFun.locChar X.α w) ∧ GlobalTheory.ThK.DetProd.IsUnramAt w (GlobalTheory.LFun.locChar X.β w) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT w hw
  have hn : w ∉ GlobalTheory.LFun.above E (X.T : Set (Pl F)) := fun h => hw.1 (Finset.mem_coe.1 h)
  exact ⟨isUnramAt_of_unrAt (hT.chars.unrα w hn), isUnramAt_of_unrAt (hT.chars.unrβ w hn)⟩

end GlobalTheory.GoodPlaceUnr
