import Mathlib
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.MapStdPoly

noncomputable section

open CompanionTheory.D.gk.admitted (stdPoly)
open scoped InnerProductSpace

namespace CompanionTheory.Rg.Fl

section Group

variable {G : Type} [Group G]

def IsHeckePair (K : Subgroup G) : Prop := ∀ g : G, (MulAction.orbit K (g : G ⧸ K)).Finite

def IsCartan (K : Subgroup G) (d l : ℕ) : Prop :=
  ∃ (c : Fin d → G) (t : Fin l → G), (∀ i k, k ∈ K ↔ c i * k * (c i)⁻¹ ∈ K) ∧ (∀ i j, Commute (t i) (t j)) ∧
    (∀ g, ∃ i j, ∃ s ∈ Submonoid.closure (Set.range t), ∃ k ∈ K, ∃ k' ∈ K, g = k * c i * s * c j * k') ∧
    ∀ s ∈ Submonoid.closure (Set.range t), ∀ s' ∈ Submonoid.closure (Set.range t), ∀ k ∈ K,
      ∃ a ∈ K, ∃ b ∈ K, s * k * s' = a * (s * s') * b

def IsSep (K : Subgroup G) : Prop :=
  ∀ S : Finset (G ⧸ K), ∃ Γ : Subgroup G, Finite (MulAction.orbitRel.Quotient Γ (G ⧸ K)) ∧
    (∀ x : G ⧸ K, Finite (MulAction.stabilizer Γ x)) ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ γ : Γ, γ • x = y → x = y

def lam (K : Subgroup G) (g : G) : Module.End ℂ ((G ⧸ K) →₀ ℂ) := Finsupp.lmapDomain ℂ ℂ fun x => g • x

def Hk (K : Subgroup G) : Subalgebra ℂ (Module.End ℂ ((G ⧸ K) →₀ ℂ)) := Subalgebra.centralizer ℂ (Set.range (lam K))

end Group

def IsBern (A : Type) [Ring A] [Algebra ℂ A] (d l : ℕ) : Prop :=
  ∃ (x y : Fin d → A) (a : Fin l → A), (∀ i j, Commute (a i) (a j)) ∧
    Submodule.span ℂ {z | ∃ i j, ∃ c ∈ Algebra.adjoin ℂ (Set.range a), z = x i * c * y j} = ⊤

def StarClosed {A V : Type} [Ring A] [Algebra ℂ A] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : A →ₐ[ℂ] Module.End ℂ V) : Prop := ∀ h, ∃ h', ∀ u w, ⟪ρ h u, w⟫_ℂ = ⟪u, ρ h' w⟫_ℂ

section Hilbert

variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsAvg (σ : G →* (H →L[ℂ] H)) (K : Subgroup G) (E : H →L[ℂ] H) : Prop :=
  (∀ v, ∀ k ∈ K, σ k (E v) = E v) ∧ (∀ v, (∀ k ∈ K, σ k v = v) → E v = v) ∧ ∀ v, ∀ k ∈ K, E (σ k v) = E v

def IsPIProj (σ : G →* (H →L[ℂ] H)) (E : H →L[ℂ] H) : Prop :=
  E ≠ 0 ∧ E * E = E ∧ (∀ u w, ⟪E u, w⟫_ℂ = ⟪u, E w⟫_ℂ) ∧ (∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → T * E = E * T) ∧
    ∃ M : ℕ, ∀ g : Fin M → G, stdPoly E (fun i => σ (g i)) = 0

end Hilbert

def HasPI {G : Type} [Group G] (K : Subgroup G) (M : ℕ) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ E, IsAvg σ K E → ∀ g : Fin M → G, stdPoly E (fun i => σ (g i)) = 0

def StComm : Prop :=
  ∀ l N : ℕ, ∃ C : ℕ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : Fin l → Module.End ℂ V),
    (∀ i j, Commute (a i) (a j)) →
      N * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ Module.finrank ℂ V ^ 2 + C * Module.finrank ℂ V

def StSimple : Prop :=
  ∀ d l : ℕ, ∃ C : ℕ, ∀ (A : Type) [Ring A] [Algebra ℂ A], IsBern A d l →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V),
      (∀ W : Submodule ℂ V, (∀ h, ∀ w ∈ W, ρ h w ∈ W) → W = ⊥ ∨ W = ⊤) → Module.finrank ℂ V ≤ C

def StStar : Prop :=
  ∀ (C : ℕ) (A : Type) [Ring A] [Algebra ℂ A],
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V),
      (∀ W : Submodule ℂ V, (∀ h, ∀ w ∈ W, ρ h w ∈ W) → W = ⊥ ∨ W = ⊤) → Module.finrank ℂ V ≤ C) →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V),
      StarClosed ρ → ∀ b : Fin (C ^ 2 + 1) → A, ρ (stdPoly 1 b) = 0

def StHecke : Prop :=
  ∀ (G : Type) [Group G] (K : Subgroup G) (d l : ℕ), IsHeckePair K → IsCartan K d l → IsBern (Hk K) d l

def StMod : Prop :=
  ∀ (G : Type) [Group G] (K : Subgroup G), IsHeckePair K → IsSep K → ∀ h : Hk K,
    ∃ (N : ℕ) (ρ : Hk K →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin N))), StarClosed ρ ∧ (ρ h = 0 → h = 0)

def StTransfer : Prop :=
  ∀ (G : Type) [Group G] (K : Subgroup G) (M : ℕ), IsHeckePair K → (∀ b : Fin M → Hk K, stdPoly 1 b = 0) → HasPI K M

def StProj : Prop :=
  ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ K : Subgroup G, ∃ E, IsAvg σ K E ∧ (∀ u w, ⟪E u, w⟫_ℂ = ⟪u, E w⟫_ℂ) ∧
      ∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → T * E = E * T

def StPair : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) →
    IsCompact (K : Set G) → IsHeckePair K

def StFixVec : Prop :=
  ∀ (G H : Type) [Group G] [TopologicalSpace G] [NonarchimedeanGroup G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] (σ : G →* (H →L[ℂ] H)), (∀ g v, ‖σ g v‖ = ‖v‖) → (∀ v, Continuous fun g => σ g v) →
    ∃ (U : Subgroup G) (v : H), IsOpen (U : Set G) ∧ v ≠ 0 ∧ ∀ k ∈ U, σ k v = v

def HasCartan (G : Type) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ K ≤ U, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ ∃ d l, IsCartan K d l

def UG {L : Type} [CommRing L] {n : ℕ} (s : L →+* L) (J : Matrix (Fin n) (Fin n) L) : Subgroup (GL (Fin n) L) where
  carrier := {g | (g.1.map s).transpose * J * g.1 = J}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul] at *
    calc _ = (b.1.map s).transpose * ((a.1.map s).transpose * J * a.1) * b.1 := by simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h1 : ((a⁻¹).1.map s).transpose * (a.1.map s).transpose = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul]; simp
    calc _ = ((a⁻¹).1.map s).transpose * ((a.1.map s).transpose * J * a.1) * (a⁻¹).1 := by rw [ha]
      _ = (((a⁻¹).1.map s).transpose * (a.1.map s).transpose) * J * (a.1 * (a⁻¹).1) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [h1]; simp

def StCartanU : Prop :=
  ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] [CharZero L] (s : L →+* L),
    (∀ x, s (s x) = x) → (∀ x, ‖s x‖ = ‖x‖) → (∃ x, s x ≠ x) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) L),
      (J.map s).transpose = J → J.det ≠ 0 → HasCartan (UG s J)

def StCartanGL : Prop :=
  ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] (n : ℕ), HasCartan (GL (Fin n) L)

def StMove : Prop :=
  ∀ (G G' : Type) [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (_ : G ≃ₜ* G'), HasCartan G' → HasCartan G

theorem hasPI_of (h2 : StSimple) (h3 : StStar) (h4 : StHecke) (h5 : StMod) (h7 : StTransfer)
    {G : Type} [Group G] {K : Subgroup G} {d l : ℕ} (hp : IsHeckePair K) (hc : IsCartan K d l) (hs : IsSep K) :
    ∃ M, HasPI K M := by
  obtain ⟨C, hC⟩ := h2 d l
  refine ⟨C ^ 2 + 1, h7 G K _ hp fun b => ?_⟩
  obtain ⟨N, ρ, hρ, h0⟩ := h5 G K hp hs (stdPoly 1 b)
  exact h0 (h3 C _ (hC _ (h4 G K d l hp hc)) _ ρ hρ b)

end CompanionTheory.Rg.Fl

end
