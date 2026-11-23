import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend

noncomputable section

namespace PositivityTheory.RgEis

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

def HasWallD (Γ K P P' : Subgroup G) (c : G → ℂ) (η η' β : G → ℝ) (ρ : K →* (W →L[ℂ] W)) (D : ℂ → ℂ) : Prop :=
  ∃ R Op H, Wall Γ K P P' c η η' β ρ (secSp K P c ρ) R D Op H

def HasWallU (Γ K P P' : Subgroup G) (c : G → ℂ) (η η' β : G → ℝ) (ρ : K →* (W →L[ℂ] W)) (D : ℂ → ℂ) : Prop :=
  ∃ M : ℂ → ℂ, StripEntire M ∧ (∀ z, M z ≠ 0) ∧ HasWallD Γ K P P' c η η' β ρ fun z => M z * D z

def Triv (K₀ : Subgroup G) {K : Subgroup G} (ρ : K →* (W →L[ℂ] W)) : Prop := ∀ k : K, (k : G) ∈ K₀ → ρ k = 1

def AllRepT (K K₀ : Subgroup G) (Q : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W], (K →* (W →L[ℂ] W)) → Prop) :
    Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (ρ : K →* (W →L[ℂ] W)), Continuous ρ →
    Triv K₀ ρ → Q ρ

def TwistD : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (Γ K K₀ P P' : Subgroup G) (c c₀ : G → ℂ) (η η' β : G → ℝ) (D : ℂ → ℂ), IsCompact (K : Set G) → IsCh Γ ⊤ c₀ →
    (∀ k ∈ K, k ∈ K₀ → c₀ k = 1) → IsPar Γ K P c → IsPar Γ K P' c →
    AllRepT K K₀ (fun ρ => HasWallU Γ K P P' c η η' β ρ D) → AllRepT K K₀ (fun ρ => HasWallU Γ K P P' (c * c₀) η η' β ρ D)

def ScaleD : Prop := ForRep fun {G} _ _ {_W} _ _ K ρ => ∀ (Γ P P' : Subgroup G) (c : G → ℂ) (η η' β l : G → ℝ) (s : ℝ)
  (D : ℂ → ℂ), 0 < s → IsHt Γ K ⊤ l → HasWallU Γ K P P' c η η' β ρ D →
  HasWallU Γ K P P' c (fun g => s * (η g + l g)) (fun g => s * (η' g - l g)) β ρ (fun z => D (s * z))

def TransferD : Prop := ForRep fun {G} _ _ {W} _ _ K ρ => ∀ (G' : Type) [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G'] [T2Space G'] [LocallyCompactSpace G'] (Γ Q P₁ P₂ K₀ : Subgroup G) (Γ' K' P₁' P₂' K₀' : Subgroup G')
  (π : Q →* G') (ι : G' →* Q) (c₀ c : G → ℂ) (c' : G' → ℂ) (η₁ η₂ β : G → ℝ) (η₁' η₂' β' : G' → ℝ) (D : ℂ → ℂ),
  IsCompact (K' : Set G') → IsLevi Γ K Q Γ' K' π ι c₀ → IsPull Q P₁ P₁' π c₀ c c' → IsPull Q P₂ P₂' π c₀ c c' →
  IsPar Γ' K' P₁' c' → IsPar Γ' K' P₂' c' → IsHt Γ' K' P₁' η₁' → IsHt Γ' K' P₂' η₂' → IsHt Γ' K' P₂' β' →
  PullHt K Q π η₁ η₁' → PullHt K Q π η₂ η₂' → PullHt K Q π β β' → (∀ m ∈ K', m ∈ K₀' → (ι m : G) ∈ K₀) → Triv K₀ ρ →
  AllRepT K' K₀' (fun ρ' => HasWallU Γ' K' P₁' P₂' c' η₁' η₂' β' ρ' D) → HasWallU (Γ ⊓ Q) K P₁ P₂ c η₁ η₂ β ρ D

def GalleryD : Prop := ForRep fun {G} _ _ {_W} _ _ K ρ => FirstCountableTopology G →
  ∀ (Γ S A B Q₁ Q₂ : Subgroup G) (c : G → ℂ) (h a b : G → ℝ) (N : ℝ) (Dc Da Db : ℂ → ℂ), A ≤ S → B ≤ S → A ≤ Q₁ →
  B ≤ Q₂ → IsPar Γ K S c → IsPar Γ K A c → IsPar Γ K B c → IsHt Γ K S h → IsHt Γ K Q₁ a → IsHt Γ K Q₂ (fun g => h g + b g) →
  (∃ R : ℝ, (∀ y : ℝ, R < y → Conv Γ S fun g => y * h g) ∧
    (∀ z y : ℝ, R < z → R < y → Conv Γ A fun g => z * a g + y * h g) ∧
    ∀ r y : ℝ, R < r → R < y → Conv Γ B fun g => r * (h g + b g) + y * h g) →
  HasFirst (Γ ⊓ S) K S A B c a b (fun g => h g + N * b g) ρ →
  HasWallU (Γ ⊓ Q₂) K B B c (fun g => -b g) (fun g => -b g) (fun g => -b g) ρ Dc →
  HasWallU (Γ ⊓ S) K B A c b a (fun g => N * a g - h g) ρ Da →
  HasWallU (Γ ⊓ Q₁) K A A c (fun g => h g - a g) (fun g => h g - a g) (fun g => (N - 1) * (h g - a g)) ρ Db →
  HasLast (Γ ⊓ S) K S A B c a b (fun g => h g + N * b g) h N ρ →
  HasWallU Γ K S S c h h (fun g => N * h g) ρ
    (fun y => Dc (y + 1 - N) * Da (2 * y + 1 - N) * Db y)

end PositivityTheory.RgEis
