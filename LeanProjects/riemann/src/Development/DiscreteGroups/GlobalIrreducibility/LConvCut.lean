import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.LConv

def IsWhitTest {k : Type} [Field k] [TopologicalSpace k] {m : ℕ} (ψ : AddChar k Circle) (f : GL (Fin m) k → ℂ) :
    Prop :=
  (∀ u ∈ unipB k (Fin m), ∀ g, f (u * g) = (ψ (superDiag u) : ℂ) * f g) ∧ IsLocallyConstant f ∧
    ∃ C : Set (GL (Fin m) k), IsCompact C ∧ ∀ g, f g ≠ 0 → ∃ u ∈ unipB k (Fin m), ∃ c ∈ C, g = u * c

def IsInvForm {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : Prop :=
  (∀ x y, (starRingEnd ℂ) (B x y) = B y x) ∧ (∀ x, 0 ≤ (B x x).re) ∧ ∀ g x y, B (ρ g x) (ρ g y) = B x y

def IsExtremeForm {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : Prop :=
  IsInvForm ρ B ∧ ∀ B' : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, IsInvForm ρ B' → IsInvForm ρ (B - B') →
    ∃ c : ℂ, ∀ x y, B' x y = c * B x y

def UnitAdm (G : Type) [Group G] (K : Subgroup G) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : G →* (H →L[ℂ] H)),
    (∀ g x, ‖π g x‖ = ‖x‖) → (∀ T : H →L[ℂ] H, (∀ g, T * π g = π g * T) → ∃ c : ℂ, T = c • (1 : H →L[ℂ] H)) →
    ∃ s : Finset H, ∀ x : H, (∀ κ ∈ K, π κ x = x) → x ∈ Submodule.span ℂ (s : Set H)

def UnifAdm (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (N : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → ρ.IsIrreducible →
    FiniteDimensional ℂ (fixed ρ K) ∧ Module.finrank ℂ (fixed ρ K) ≤ N

def CuspGen : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), Nontrivial V → IsCuspidal π → IsGeneric ψ π

def KirBump : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin (m + 1)) k) V), IsSmooth ρ → ∀ v₀ : V, ∃ v : V,
      ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l →
        l v = l v₀ ∧ (l v₀ = 0 → ∀ g : GL (Fin m) k, l (ρ (corner g) v) = 0)

def BigCell : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (m : ℕ), 0 < m → ∀ (π₁ π₂ : IrrRep (GL (Fin (m + 1)) k))
    (l₁ : Module.Dual ℂ π₁.V) (l₂ : Module.Dual ℂ π₂.V), IsFunctional ψ π₁.ρ l₁ → IsFunctional ψ π₂.ρ l₂ →
    (∀ (v₁ : π₁.V) (v₂ : π₂.V), (∀ g : GL (Fin m) k, l₁ (π₁.ρ (corner g) v₁) = l₂ (π₂.ρ (corner g) v₂)) →
      l₁ (π₁.ρ (longElt (m + 1) k) v₁) = l₂ (π₂.ρ (longElt (m + 1) k) v₂)) →
    (∃ (v₁ : π₁.V) (v₂ : π₂.V), (∀ g : GL (Fin m) k, l₁ (π₁.ρ (corner g) v₁) = l₂ (π₂.ρ (corner g) v₂)) ∧
      l₁ v₁ ≠ 0) →
    Nonempty (π₁.ρ.Equiv π₂.ρ)

def WhitSep : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (m : ℕ),
    ∃ I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ, IsInvIntegral I ∧
      ∀ ψ : AddChar k Circle, Continuous ψ → ∀ f : GL (Fin m) k → ℂ, IsWhitTest ψ f →
        (∀ (τ : IrrRep (GL (Fin m) k)) (l : Module.Dual ℂ τ.V), IsFunctional ψ⁻¹ τ.ρ l →
          ∀ v : τ.V, I (fun g => f g * l (τ.ρ g v)) = 0) → f = 0

def ExtremeExists : Prop :=
  ∀ (G M : Type) [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M),
    (∃ s : Set M, s.Countable ∧ Submodule.span ℂ s = ⊤) →
    ∀ B₀ : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, IsInvForm ρ B₀ → ∀ f : M, B₀ f f ≠ 0 →
      ∃ B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, IsExtremeForm ρ B ∧ B f f ≠ 0

def ExtremeIrred : Prop :=
  ∀ (G M : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ G M), IsSmooth ρ →
    (∀ x : M, ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ ∀ κ ∈ K, ρ κ x = x) →
    (∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → UnitAdm G K) →
    ∀ B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, IsExtremeForm ρ B →
      ∀ Z : Submodule ℂ M, (∀ g, ∀ z ∈ Z, ρ g z ∈ Z) →
        (∀ z ∈ Z, B z z = 0) ∨ ∀ x : M, ∃ z ∈ Z, B (x - z) (x - z) = 0

def UnitAdmGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ)
    (K : Subgroup (GL (Fin m) k)), IsOpen (K : Set (GL (Fin m) k)) → IsCompact (K : Set (GL (Fin m) k)) →
    UnitAdm (GL (Fin m) k) K

def SepOfExtreme : Prop := ExtremeExists → ExtremeIrred → UnitAdmGL → WhitSep

def CommBound : Prop :=
  ∀ l t : ℕ, ∃ c : ℕ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : Fin l → Module.End ℂ V), (∀ i j, a i * a j = a j * a i) →
    t * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ Module.finrank ℂ V ^ 2 + c * Module.finrank ℂ V

def UnifAdmGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ)
    (K : Subgroup (GL (Fin m) k)), IsOpen (K : Set (GL (Fin m) k)) → ∃ N : ℕ, UnifAdm (GL (Fin m) k) K N

def UnifOfComm : Prop := CommBound → UnifAdmGL

def AltIdentity : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    IsCompact (K : Set G) → Countable (G ⧸ K) → ∀ N : ℕ, UnifAdm G K N →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : G →* (H →L[ℂ] H)),
      (∀ g x, ‖π g x‖ = ‖x‖) → ∀ e : H →L[ℂ] H, IsSelfAdjoint e → (∀ x, ∀ κ ∈ K, π κ (e x) = e x) →
      (∀ x, (∀ κ ∈ K, π κ x = x) → e x = x) → ∀ d : ℕ, N ^ 2 < d → ∀ g : Fin d → G,
        ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun i => e * π (g (σ i)) * e).prod = 0

def FiniteOfAlt : Prop :=
  ∀ (G : Type) [Group G] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G →* (H →L[ℂ] H)), (∀ g x, ‖π g x‖ = ‖x‖) →
    (∀ T : H →L[ℂ] H, (∀ g, T * π g = π g * T) → ∃ c : ℂ, T = c • (1 : H →L[ℂ] H)) →
    ∀ e : H →L[ℂ] H, e * e = e → ∀ d : ℕ, (∀ g : Fin d → G,
      ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun i => e * π (g (σ i)) * e).prod = 0) →
    ∃ s : Finset H, ∀ x : H, e x ∈ Submodule.span ℂ (s : Set H)

def UnitOfUnif : Prop := AltIdentity → FiniteOfAlt → UnifAdmGL → UnitAdmGL

def Glue : Prop := CuspGen → KirBump → BigCell → WhitSep → GlobalTheory.Published.LocalConverseGL

theorem localConverseGL_of_leaves (h1 : CuspGen) (h2 : KirBump) (h3 : BigCell) (h4 : ExtremeExists)
    (h5 : ExtremeIrred) (h6 : SepOfExtreme) (h7 : CommBound) (h8 : UnifOfComm) (h9 : AltIdentity)
    (h10 : FiniteOfAlt) (h11 : UnitOfUnif) (h12 : Glue) : GlobalTheory.Published.LocalConverseGL :=
  h12 h1 h2 h3 (h6 h4 h5 (h11 h9 h10 (h8 h7)))

end DiscreteGroups.sglob.LConv

end
