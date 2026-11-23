import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationAddOfIrreducibleProductStatement

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

section Sums

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem segSum_append_lpSum (rc : IrrGL (w.adicCompletion E) → WD h) (l l' : List (Segment (w.adicCompletion E))) :
    segSum rc (l ++ l') = (segSum rc l).lpSum (segSum rc l') := by
  induction l with
  | nil => exact ((WD.lpSum_comm _ _).trans (WD.lpSum_zero _)).symm
  | cons a l ih =>
    have key : ∀ m : List (Segment (w.adicCompletion E)), segSum rc (a :: m) =
        (((rc a.first).lpTw (((a.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h a.len)).lpSum (segSum rc m) := fun _ => rfl
    rw [List.cons_append, key, key, ih, WD.lpSum_assoc]

end Sums

theorem lawsLit_prod : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (r t : ℕ) (σ : IrrRep (GL (Fin r) (w.adicCompletion E))) (τ : IrrRep (GL (Fin t) (w.adicCompletion E))) (π : IrrRep (GL (Fin (r + t)) (w.adicCompletion E))), Nonempty (π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) → rc (cls π) = (rc (cls σ)).lpSum (rc (cls τ)) := by
  intro hX hM hS E Ω _ _ _ _ _ A w h a ha e rc H r t σ τ π hπ
  have : CharZero (w.adicCompletion E) := algebraRat.charZero _
  obtain ⟨𝔪, h𝔪⟩ := hX _ (cls σ)
  obtain ⟨𝔫, h𝔫⟩ := hX _ (cls τ)
  have hp := GlobalTheory.T.isLanglandsClassification_add_of_irreducible_product hM hS _ r t σ τ π 𝔪 𝔫 (h𝔪.of_equiv (equivRep σ).symm) (h𝔫.of_equiv (equivRep τ).symm) hπ
  rw [H.langlands 𝔪.toList (cls σ) (by rwa [Multiset.coe_toList]),
    H.langlands 𝔫.toList (cls τ) (by rwa [Multiset.coe_toList]),
    H.langlands (𝔪.toList ++ 𝔫.toList) (cls π) (by
      rw [← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList]
      exact hp.of_equiv (equivRep π)), segSum_append_lpSum]

end GlobalTheory.LocLanglands

end
