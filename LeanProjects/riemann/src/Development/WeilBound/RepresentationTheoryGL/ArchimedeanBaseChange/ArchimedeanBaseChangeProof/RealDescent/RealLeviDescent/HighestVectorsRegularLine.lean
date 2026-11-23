import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod

noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC.Real

def TrPass : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
    ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U]
      [InnerProductSpace ℂ U] [CompleteSpace U] (π : G n →* (U →L[ℂ] U)) (A : U →L[ℂ] U), IsUnitaryRep π →
      IsTopIrreducible π → IsThetaOp n π A → A * A = 1 → HasInf π (infOf lam) →
      ∀ k val (T' : ℝ), IsMult μ E k val T' →
        HasTrace (repOp π μ (phiOf E T k) ∘L A) (val (infOf lam) * trInv π E A T)

def Bridge : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    (π : G n →* (U →L[ℂ] U)) (A : U →L[ℂ] U), IsUnitaryRep π → IsTopIrreducible π → IsThetaOp n π A → A * A = 1 →
    HasInf π (infOf lam) → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V), (∀ k, T * E.ρ k = E.ρ k * T) →
      ∃ (V : Submodule ℂ U) (E1 E2 : Fin n → Fin n → Module.End ℂ V)
        (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A' : V →ₗ[ℂ] V),
        IsCoreMod (infOf lam) E1 E2 σ A' ∧ FiniteDimensional ℂ (invA σ E) ∧ (invSp π E ≠ ⊥ → invA σ E ≠ ⊥) ∧
          trInv π E A T = trOn (invA σ E) (flipA E A' T)

def Core : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), StrictAnti lam → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
      (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V), IsCoreMod (infOf lam) E1 E2 σ A →
      FiniteDimensional ℂ (invA σ E) → invA σ E ≠ ⊥ →
        ∃ s : ℂ, (s = 1 ∨ s = -1) ∧ trOn (invA σ E) (flipA E A T) = s * 2 ^ n

def CountK : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), StrictAnti lam → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
      (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V), IsCoreMod (infOf lam) E1 E2 σ A →
      FiniteDimensional ℂ (invA σ E) →
        (∀ x ∈ hwSp E1 E2 (m0 lam), A x ∈ hwSp E1 E2 (m0 lam)) ∧ FiniteDimensional ℂ (hwSp E1 E2 (m0 lam)) ∧
          (invA σ E ≠ ⊥ → hwSp E1 E2 (m0 lam) ≠ ⊥) ∧
          trOn (invA σ E) (flipA E A T) = 2 ^ n * trOn (hwSp E1 E2 (m0 lam)) A

def HighestVectorsRegularLine : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), StrictAnti lam → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V),
    IsCoreMod (infOf lam) E1 E2 σ A → ∀ v w : V, v ∈ hwSp E1 E2 (m0 lam) → w ∈ hwSp E1 E2 (m0 lam) → v ≠ 0 →
      ∃ c : ℂ, w = c • v

def SignOne : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (A : V →ₗ[ℂ] V), A * A = 1 → (∀ x ∈ S, A x ∈ S) →
    Module.finrank ℂ S = 1 → ∃ s : ℂ, (s = 1 ∨ s = -1) ∧ trOn S A = s

def CoreG : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
      (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V), IsCoreMod (infOf lam) E1 E2 σ A →
      FiniteDimensional ℂ (invA σ E) → invA σ E ≠ ⊥ →
        ∃ s : ℂ, (s = 1 ∨ s = -1) ∧ trOn (invA σ E) (flipA E A T) = s * 2 ^ n

def CountG : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
      (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V), IsCoreMod (infOf lam) E1 E2 σ A →
      FiniteDimensional ℂ (invA σ E) →
        (∀ μ ∈ harmSet lam, (∀ x ∈ hwSp E1 E2 μ, A x ∈ hwSp E1 E2 μ) ∧ FiniteDimensional ℂ (hwSp E1 E2 μ)) ∧
          (invA σ E ≠ ⊥ → ∃ μ ∈ harmSet lam, hwSp E1 E2 μ ≠ ⊥) ∧
          trOn (invA σ E) (flipA E A T) = 2 ^ n * ∑ μ ∈ harmSet lam, trOn (hwSp E1 E2 μ) A

def MultG : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V),
    IsCoreMod (infOf lam) E1 E2 σ A → ∃ μ₀ ∈ harmSet lam, (∀ μ ∈ harmSet lam, μ ≠ μ₀ → hwSp E1 E2 μ = ⊥) ∧
      ∀ v w : V, v ∈ hwSp E1 E2 μ₀ → w ∈ hwSp E1 E2 μ₀ → v ≠ 0 → ∃ c : ℂ, w = c • v

theorem coreG_of (hK : CountG) (hM : MultG) (hS : SignOne) : CoreG := by
  intro n lam hlam E T hT V _ _ E1 E2 σ A hA hfin hne
  obtain ⟨h1, h2, h3⟩ := hK n lam hlam E T hT V E1 E2 σ A hA hfin
  obtain ⟨μ₀, hμ₀, hzero, hone⟩ := hM n lam hlam V E1 E2 σ A hA
  have hbot : hwSp E1 E2 μ₀ ≠ ⊥ := by
    obtain ⟨μ, hμ, hμne⟩ := h2 hne
    by_cases heq : μ = μ₀
    · exact heq ▸ hμne
    · exact absurd (hzero μ hμ heq) hμne
  have htr0 : ∀ μ ∈ harmSet lam, μ ≠ μ₀ → trOn (hwSp E1 E2 μ) A = 0 := by
    intro μ hμ hμne
    rw [hzero μ hμ hμne]
    unfold trOn
    split_ifs with h
    · have hz : A.restrict h = 0 := LinearMap.ext fun x => Subsingleton.elim _ _
      rw [hz, map_zero]
    · rfl
  have hsum : ∑ μ ∈ harmSet lam, trOn (hwSp E1 E2 μ) A = trOn (hwSp E1 E2 μ₀) A :=
    Finset.sum_eq_single_of_mem μ₀ hμ₀ htr0
  obtain ⟨hinv, hfd⟩ := h1 μ₀ hμ₀
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hle : Module.finrank ℂ (hwSp E1 E2 μ₀) ≤ 1 := by
    apply finrank_le_one (⟨v, hv⟩ : hwSp E1 E2 μ₀)
    intro w
    obtain ⟨c, hc⟩ := hone v w hv w.2 hv0
    exact ⟨c, Subtype.ext (by simp [hc])⟩
  have hpos : 0 < Module.finrank ℂ (hwSp E1 E2 μ₀) := by
    have : Nontrivial (hwSp E1 E2 μ₀) :=
      ⟨⟨⟨v, hv⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
    exact Module.finrank_pos
  obtain ⟨s, hs, hts⟩ := hS V (hwSp E1 E2 μ₀) A hA.Asq hinv (by omega)
  refine ⟨s, hs, ?_⟩
  rw [h3, hsum, hts, mul_comm]

end PositivityTheory.RgBcC.RealD
