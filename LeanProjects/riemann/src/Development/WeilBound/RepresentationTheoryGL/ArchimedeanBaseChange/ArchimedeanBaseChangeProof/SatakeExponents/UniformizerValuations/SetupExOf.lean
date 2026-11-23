import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEx

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5

namespace PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev Prod' {ι : Type} (H : ι → Type) [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
    [∀ s, CompleteSpace (H s)] (d : ℕ) : Type :=
  (∀ s, H s →L[ℂ] H s) × (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))

structure RunData (π : Submodule ℂ (UA E n → ℂ)) (S T : Finset (HeightOneSpectrum (𝓞 E)))
    (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
    (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)) where
  ι : Type
  [ft : Fintype ι]
  [ne : Nonempty ι]
  H : ι → Type
  [ng : ∀ s, NormedAddCommGroup (H s)]
  [ip : ∀ s, InnerProductSpace ℂ (H s)]
  [cs : ∀ s, CompleteSpace (H s)]
  d : ℕ
  Γ : Type
  gen : Γ → Prod' H d
  comm : ∀ x y, Commute (gen x) (gen y)
  commStar : ∀ x y, Commute (gen x) (star (gen y))
  β : ∀ s, H s →L[ℂ] H s
  βcomm : ∀ s x, Commute (β s) ((gen x).1 s) ∧ Commute (β s) (star ((gen x).1 s))
  m : ℕ
  u : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)
  ucomm : ∀ x, Commute u (gen x).2 ∧ Commute u (star (gen x).2)
  v : EuclideanSpace ℂ (Fin d)
  v_ne : v ≠ 0
  uv : u v = v
  eigv : ∀ x, ∃ c : ℂ, (gen x).2 v = c • v ∧ (star (gen x).2) v = (starRingEnd ℂ c) • v
  a₀ : Γ
  a₀v : ∃ c : ℂ, c ≠ 0 ∧ (gen a₀).2 v = c • v
  bound : ∀ a ∈ StarAlgebra.adjoin ℂ (Set.range gen), (∃ b ∈ StarAlgebra.adjoin ℂ (Set.range gen), a = b * gen a₀) →
    ∃ (C : ℝ) (N j : ℕ), ∀ᶠ k : ℕ in Filter.atTop,
    ‖LinearMap.trace ℂ _ (((u * a.2) ^ k : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :
      EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d))‖ ≤
      C * (1 + k) ^ N * Finset.univ.sup' Finset.univ_nonempty (fun s => ‖(β s ^ m * a.1 s) ^ (k - j)‖)
  read : ∀ (s : ι) (χ : StarAlgebra.adjoin ℂ
      (Set.range (fun a : StarAlgebra.adjoin ℂ (Set.range gen) => (a : Prod' H d).1 s) ∪ {star (β s ^ m) * β s ^ m})
        →⋆ₐ[ℂ] ℂ),
    (∀ x, ‖χ x‖ ≤ ‖(x : H s →L[ℂ] H s)‖) →
    (∀ a : StarAlgebra.adjoin ℂ (Set.range gen), a.1.2 v ≠ 0 → ∃ c : ℂ, a.1.2 v = c • v ∧
      χ ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ = c) →
    χ ⟨star (β s ^ m) * β s ^ m, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ ≠ 0 → ∃ D : Pre E n, TOut π S T K W D

def SetupAlg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (S T : Finset (HeightOneSpectrum (𝓞 E))) (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
  (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)), RunData π S T K W → Nonempty (Setup π S T K W)

def DataEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), S.card ≤ 1 →
    ∃ (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
      (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)), IsLevel K ∧ (∀ N, FiniteDimensional ℂ (W N)) ∧
      ∀ T : Finset (HeightOneSpectrum (𝓞 E)), Nonempty (RunData π S T K W)

theorem setupEx_of (h1 : SetupAlg) (h2 : DataEx) : SetupEx := by
  intro E _ _ _ hE n hn π hπ S hS
  obtain ⟨K, W, hK, hW, hT⟩ := h2 E hE n hn π hπ S hS
  exact ⟨K, W, hK, hW, fun T => let ⟨X⟩ := hT T; h1 E n π S T K W X⟩

end PositivityTheory.Rg.BcB.F

end
