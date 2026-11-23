import Development.WeilBound.CoreStatements.VolumeEquality.PrimeIdealOfFromSpec

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem regular_function_chart_adjoin : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ (c : κ) (p : Cpt ξ), InChart ξ x c p → ∀ a : Ω, a ∈ regAt ξ p ↔ ∃ s ∈ Algebra.adjoin o (Set.range fun j => x j / x c), unitAt ξ p s ∧ s * a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
  intro X Ω _ ξ o _ _ κ x h c p hp a
  obtain ⟨U, hU, hg, hm, -, hr⟩ := BBase.chart h c hp.1
  have hq : p.1 ∈ U := (hm _).2 ⟨p.2, hp⟩
  constructor
  · intro ha
    obtain ⟨s, t, ht, e⟩ := BBase.exists_frac hU p hq hg ha
    exact ⟨_, (hr _).1 ⟨t, rfl⟩, (BBase.unitAt_ev_iff h.gen hU p hq hg t).2 ht, (hr _).1 ⟨s, e.symm⟩⟩
  · rintro ⟨s, -, ⟨h0, -, hi⟩, hsa⟩
    obtain ⟨t, ht⟩ := (hr _).2 hsa
    have e : a = s⁻¹ * (s * a) := by rw [inv_mul_cancel_left₀ h0]
    rw [e, ← ht]
    exact mul_mem hi (BBase.ev_mem p U hq hg t)

end SheetDecomposition
