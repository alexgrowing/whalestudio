import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.DataExOf

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5

namespace PositivityTheory.Rg.BcB.F.R3

variable {ι : Type} {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type}

theorem chi_pin (gen : Γ → Prod' H d) (a₀ : Γ) (v : EuclideanSpace ℂ (Fin d)) (hv : v ≠ 0) (ha₀ : (gen a₀).2 v = v)
    (s : ι) (X : H s →L[ℂ] H s)
    (χ : StarAlgebra.adjoin ℂ (Set.range (fun a : StarAlgebra.adjoin ℂ (Set.range gen) => (a : Prod' H d).1 s) ∪ {X})
      →⋆ₐ[ℂ] ℂ)
    (heig : ∀ a : StarAlgebra.adjoin ℂ (Set.range gen), a.1.2 v ≠ 0 → ∃ c : ℂ, a.1.2 v = c • v ∧
      χ ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ = c)
    (a : StarAlgebra.adjoin ℂ (Set.range gen)) (c : ℂ) (hc : a.1.2 v = c • v) :
    χ ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ = c := by
  have hinj : ∀ {c₁ c₂ : ℂ}, c₁ • v = c₂ • v → c₁ = c₂ := fun h => smul_left_injective ℂ hv h
  let A₀ : StarAlgebra.adjoin ℂ (Set.range gen) := ⟨gen a₀, StarAlgebra.subset_adjoin ℂ _ ⟨a₀, rfl⟩⟩
  have hA₀ : A₀.1.2 v = v := ha₀
  obtain ⟨c₀, hc₀, hχ₀⟩ := heig A₀ (by rw [hA₀]; exact hv)
  have hc₀1 : c₀ = 1 := hinj (by rw [← hc₀, hA₀, one_smul])
  by_cases hc0 : c = 0
  · subst hc0
    have hsum : (a + A₀).1.2 v = v := by
      show a.1.2 v + A₀.1.2 v = v
      rw [hc, hA₀, zero_smul, zero_add]
    obtain ⟨c₁, hc₁, hχ₁⟩ := heig (a + A₀) (by rw [hsum]; exact hv)
    have hc₁1 : c₁ = 1 := hinj (by rw [← hc₁, hsum, one_smul])
    have hsplit : χ ⟨(a + A₀).1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a + A₀, rfl⟩)⟩ =
        χ ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ +
          χ ⟨A₀.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨A₀, rfl⟩)⟩ := by
      rw [← map_add]; exact congrArg χ (Subtype.ext rfl)
    rw [hsplit, hχ₀, hc₀1, hc₁1] at hχ₁
    linear_combination hχ₁
  · obtain ⟨c', hc', hχ'⟩ := heig a (by rw [hc]; exact smul_ne_zero hc0 hv)
    rw [hχ']; exact hinj (hc'.symm.trans hc)

end PositivityTheory.Rg.BcB.F.R3

end
