import Mathlib
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NoMonodromyOfMemWeilDeligneListSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaAndZelevinskyPolynomialRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BernsteinZelevinskyFinitenessHolds

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GenericLDatum

theorem exists_unlinked_isL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (x : IrrGL k), IsGeneric x.rep →
    ∃ (c : ℕ) (Δ : Fin c → Segment k), (∀ i j, i ≠ j → ¬ (Δ i).Linked (Δ j)) ∧
      IsL ((List.ofFn Δ : List (Segment k)) : Multiset (Segment k)) x.rep := by
  intro k _ _ _ _ _ x hg
  obtain ⟨c, Δ, y, hd, hun, hL, ⟨e⟩⟩ :=
    GlobalTheory.genericUnlinkedGL_outright k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr hg
  refine ⟨c, Δ, hun, c, y, hd, ⟨Δ, ⟨?_, ?_⟩, hL⟩, (isCosocle_self x.2.rep.irr).of_equiv (.refl _) e⟩
  · exact Fin.univ_val_map Δ
  · intro i j hij hP
    exact hun i j (ne_of_lt hij) hP.1

end GlobalTheory.GenericLDatum
