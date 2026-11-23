import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlmostNormFinDiag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexTwoOfFiniteReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEverywhereNormDivOfEtaProdEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSquareMulInfinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBasisOfIsQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenCardOfNotLone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlmostNormEtaProdEqNegOne

open NumberField IsDedekindDomain

namespace GlobalTheory.QuadSymbol

theorem eta_eq_of_div_mem {K L : Type} [Field K] [Field L] [Algebra K L] {A : Type} [CommRing A]
    [Algebra K A] {a b : Aˣ} (h : a / b ∈ normGroup K L A) : eta K L A a = eta K L A b := by
  have hiff : a ∈ normGroup K L A ↔ b ∈ normGroup K L A := by
    have := (normGroup K L A).mul_mem_cancel_left (x := a / b) (y := b) h
    rwa [div_mul_cancel] at this
  by_cases hb : b ∈ normGroup K L A
  · rw [eta_eq_one_iff.2 hb, eta_eq_one_iff.2 (hiff.2 hb)]
  · rw [eta_eq_neg_one_iff.2 hb, eta_eq_neg_one_iff.2 (fun ha => hb (hiff.1 ha))]

theorem etaProd_eq_of_everywhereNorm_div {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    {x x' : FinFam K} {y y' : InfFam K} (h : EverywhereNorm K L (x / x') (y / y')) :
    etaProd K L x y = etaProd K L x' y' := by
  unfold etaProd
  congr 1
  · exact finprod_congr fun v => eta_eq_of_div_mem (h.1 v)
  · exact Finset.prod_congr rfl fun w _ => eta_eq_of_div_mem (h.2 w)

theorem exactSequence (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] : ExactSequence K L := by
  refine ⟨almostNorm_finDiag K L, fun t => (normTheorem K L t).symm, fun x y hx => ⟨?_, ?_⟩,
    exists_almostNorm_etaProd_eq_neg_one K L⟩
  · rintro ⟨t, ht⟩
    rw [etaProd_eq_of_everywhereNorm_div ht]
    exact (productFormula K L t).2
  · exact exists_everywhereNorm_div_of_etaProd_eq_one K L x y hx

end GlobalTheory.QuadSymbol

namespace GlobalTheory.Published

open GlobalTheory.QuadSymbol

theorem quadraticClassFieldTheory_holds : QuadraticClassFieldTheory :=
  ⟨fun K L _ _ _ _ _ _ =>
    ⟨localCharacters K L, normTheorem K L, exactSequence K L, productFormula K L⟩,
   fun F E K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => baseChange F E K L h⟩

end GlobalTheory.Published
