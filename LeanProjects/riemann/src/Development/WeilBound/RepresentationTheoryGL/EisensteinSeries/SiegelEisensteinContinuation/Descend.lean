import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

noncomputable section

namespace PositivityTheory.RgEis

def Twist : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (Γ K S P P' : Subgroup G) (c c₀ : G → ℂ) (η η' β ξ : G → ℝ) (N : ℝ), IsCompact (K : Set G) → IsCh Γ ⊤ c₀ →
    IsPar Γ K S c → IsPar Γ K P c → IsPar Γ K P' c →
    ((AllRep K fun ρ => HasWall Γ K P P' c η η' β ρ) → AllRep K fun ρ => HasWall Γ K P P' (c * c₀) η η' β ρ) ∧
    ((AllRep K fun ρ => HasFirst Γ K S P P' c η η' β ρ) → AllRep K fun ρ => HasFirst Γ K S P P' (c * c₀) η η' β ρ) ∧
    ((AllRep K fun ρ => HasLast Γ K S P P' c η η' β ξ N ρ) → AllRep K fun ρ => HasLast Γ K S P P' (c * c₀) η η' β ξ N ρ)

def Scale : Prop := ForRep fun {G} _ _ {_W} _ _ K ρ => ∀ (Γ P P' : Subgroup G) (c : G → ℂ) (η η' β l : G → ℝ) (s : ℝ), 0 < s →
  IsHt Γ K ⊤ l → HasWall Γ K P P' c η η' β ρ →
  HasWall Γ K P P' c (fun g => s * (η g + l g)) (fun g => s * (η' g - l g)) β ρ

def Descend : Prop := ForRep fun {G} _ _ {_W} _ _ K ρ => ∀ (G₁ : Type) [Group G₁] [TopologicalSpace G₁]
  [IsTopologicalGroup G₁] [T2Space G₁] [LocallyCompactSpace G₁] (j : G₁ →* G) (Γ P : Subgroup G) (Γ₁ K₁ : Subgroup G₁)
  (c : G → ℂ) (η η' β : G → ℝ) (s : P → G₁), Continuous j → IsCompact (K₁ : Set G₁) → K₁.map j = K → Γ₁.map j = Γ →
  Continuous s → (∀ p, j (s p) = p) → IsPar Γ K P c → IsHt Γ K P η → IsHt Γ K P η' → IsHt Γ K P β →
  (AllRep K₁ fun ρ₁ => HasWall Γ₁ K₁ (P.comap j) (P.comap j) (c ∘ j) (η ∘ j) (η' ∘ j) (β ∘ j) ρ₁) →
  HasWall Γ K P P c η η' β ρ

end PositivityTheory.RgEis
