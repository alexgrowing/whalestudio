import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.SConjSpaceC

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.CBC

theorem conjIso_of (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) (smo : StrongMultOneReal) (h7 : SSmo) (h8 : SConjSpaceC) (h9 : SConjSpaceR)
    (h10 : SConjSatC) (h11 : SConjSatR) {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    {n : ℕ} (hn : 1 ≤ n) (P : Cusp M n) (σ : M ≃ₐ[K] M)
    (H : ∀ g : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 M), Function.Injective g →
      (∀ w, (g w).under (𝓞 K) = w.under (𝓞 K)) → (∀ w, normV (g w) = normV w) →
      ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∃ B, P.sat w B ∧ P.sat (g w) B) :
    P.ConjIso σ.toRingEquiv := by
  intro s hs
  have key : ∃ P' : Cusp M n,
      P'.space = (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' P.space ∧
      ∃ g : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 M), Function.Injective g ∧ (∀ w, (g w).under (𝓞 K) = w.under (𝓞 K)) ∧
        (∀ w, normV (g w) = normV w) ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ B, P.sat (g w) B → P'.sat w B := by
    cases P with
    | cx P =>
      obtain ⟨P', hP'⟩ := h8 M σ.toRingEquiv s hs n P
      exact ⟨.cx P', hP', h10 K M σ s hs n P P' hP'⟩
    | re P =>
      obtain ⟨P', hP'⟩ := h9 M σ.toRingEquiv s hs n P
      exact ⟨.re P', hP', h11 K M σ s hs n P P' hP'⟩
  obtain ⟨P', hsp, g, hinj, hund, hnorm, hsat⟩ := key
  refine ⟨P', hsp, h7 hN smo M n hn P' P ?_⟩
  filter_upwards [hsat, H g hinj hund hnorm] with w hB ⟨B, hB1, hB2⟩
  exact ⟨B, hB _ hB2, hB1⟩

theorem top (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) (smo : StrongMultOneReal) (h1 : SCuspOf) (h2 : SIsCusp) (h3 : SIsoSat) (h4 : STwSat)
    (h5 : SSatEx) (h6 : SSatUniq) (h7 : SSmo) (h8 : SConjSpaceC) (h9 : SConjSpaceR) (h10 : SConjSatC) (h11 : SConjSatR)
    (h12 : SNormPow) : LitCBC → CyclicBaseChange := by
  intro L K M _ _ _ _ _ _ hp hK hM n hn
  obtain ⟨L1, L2, L3⟩ := L K M hp hK hM n hn
  refine ⟨?_, ?_, ?_⟩
  · intro sat inf hc
    obtain ⟨π, rfl, rfl⟩ := h1 K n sat inf hc
    rcases L1 π with ⟨η, hη, hi⟩ | ⟨P, hw, hinf⟩
    · refine Or.inl ⟨η, hη, ?_⟩
      filter_upwards [h4 K n π η, h5 K n π] with v ⟨hu, ht⟩ ⟨B, hB⟩
      exact ⟨hu, B, hB, h6 K n π v _ _ (h3 K n _ _ hi v _ (ht B hB)) hB⟩
    · exact Or.inr ⟨P.sat, P.inf, h2 M n P, hw, hinf⟩
  · intro sat' inf' hc' hinv
    obtain ⟨P, rfl, rfl⟩ := h1 M n sat' inf' hc'
    refine (fun ⟨π, hw, hinf⟩ => ⟨π.sat, π.inf, h2 K n π, hw, hinf⟩) (L2 P fun σ => ?_)
    refine conjIso_of hN smo h7 h8 h9 h10 h11 hn P σ fun g _ hund _ => ?_
    filter_upwards [hinv] with w hall
    exact hall (g w) (hund w)
  · intro sat inf sat' inf' hc hc' hw
    obtain ⟨π, rfl, rfl⟩ := h1 K n sat inf hc
    obtain ⟨P, rfl, rfl⟩ := h1 M n sat' inf' hc'
    have hconj : ∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv := fun σ => by
      refine conjIso_of hN smo h7 h8 h9 h10 h11 hn P σ fun g hinj hund hnorm => ?_
      filter_upwards [hw, hinj.tendsto_cofinite.eventually hw] with w h1' h2'
      obtain ⟨f, hf⟩ := h12 K M w
      obtain ⟨B, hB, hPB⟩ := h1' f hf
      obtain ⟨B', hB', hPB'⟩ := h2' f (by rw [hnorm w, hund w]; exact hf)
      rw [hund w] at hB'
      obtain rfl := h6 K n π _ _ _ hB hB'
      exact ⟨_, hPB, hPB'⟩
    obtain ⟨La, Lb⟩ := L3 π P hconj hw
    refine ⟨fun η hη ht => La η hη (h7 hN smo K n hn _ _ ?_), fun sat₁ inf₁ hc₁ hw₁ => ?_⟩
    · filter_upwards [ht, h4 K n π η] with v ⟨_, B, hB, he⟩ ⟨_, htw⟩
      exact ⟨B, he ▸ htw B hB, hB⟩
    · obtain ⟨π₁, rfl, rfl⟩ := h1 K n sat₁ inf₁ hc₁
      obtain ⟨η, hη, hi⟩ := Lb π₁ hw₁
      refine ⟨η, hη, ?_⟩
      filter_upwards [h4 K n π η, h5 K n π] with v ⟨hu, ht⟩ ⟨B, hB⟩
      exact ⟨hu, B, hB, h3 K n _ _ hi v _ (ht B hB)⟩

end UpperTheory.CBC
