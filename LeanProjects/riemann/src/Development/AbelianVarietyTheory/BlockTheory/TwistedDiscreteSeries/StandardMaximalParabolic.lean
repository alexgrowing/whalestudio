import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

section Groups

variable (R : Type) [CommRing R] {a b r : ℕ}

def stdMaxParab (h : a + b = r) : Subgroup (GL (Fin r) R) := parab R (two (stdSum h))

def stdMaxRad (h : a + b = r) : Subgroup (GL (Fin r) R) := unipRad R (two (stdSum h))

variable {R}

def conjBy {G : Type} [Group G] (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

def IsParabRad (P N : Subgroup (GL (Fin r) R)) : Prop :=
  ∃ (s : ℕ) (d : Fin s → ℕ) (h : ∑ i, d i = r) (g : GL (Fin r) R),
    P = conjBy g (parab R (stdBlocks d h)) ∧ N = conjBy g (unipRad R (stdBlocks d h))

def NoFixed {Q W : Type} [Group Q] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ Q W) (H : Subgroup Q) : Prop :=
  ∀ w : W, (∀ u ∈ H, τ u w = w) → w = 0

end Groups

def idemGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r : ℕ}
    [MeasurableSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (GL (Fin r) 𝓀[k]) W) : GL (Fin r) k → ℂ :=
  GlobalTheory.Orb.typeIdem μ (GlobalTheory.LocGL.redK k (Fin r)) τ

def TypeConstTermVanish : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r a b : ℕ) (h : a + b = r), 0 < a → 0 < b →
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ (GL (Fin r) 𝓀[k]) W),
    τ.IsIrreducible → NoFixed τ (stdMaxRad 𝓀[k] h) →
  ∀ [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k)) [μ.IsHaarMeasure],
  ∀ φ ∈ SB (GL (Fin r) k), ∀ f : GL (Fin r) k → ℂ,
    (f = GlobalTheory.AutomorphicL2Unitary.conv μ (idemGL k μ τ) φ ∨ f = GlobalTheory.AutomorphicL2Unitary.conv μ φ (idemGL k μ τ)) →
  ∀ P N : Subgroup (GL (Fin r) k), IsParabRad P N → (∃ g₀, P ≤ conjBy g₀ (stdMaxParab k h)) →
  ∀ (ν : Measure N) [ν.IsHaarMeasure] (x y : GL (Fin r) k),
    Integrable (fun u : N => f (x * u * y)) ν ∧ ∫ u : N, f (x * u * y) ∂ν = 0

theorem mem_conjBy {G : Type} [Group G] {g x : G} {H : Subgroup G} : x ∈ conjBy g H ↔ g⁻¹ * x * g ∈ H :=
  ⟨by rintro ⟨u, hu, rfl⟩; simpa [mul_assoc] using hu, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩

theorem mem_stdMaxParab {R : Type} [CommRing R] {a b r : ℕ} (h : a + b = r) {g : GL (Fin r) R} :
    g ∈ stdMaxParab R h ↔ ∀ i j : Fin r, (j : ℕ) < a → a ≤ (i : ℕ) → (g : Matrix (Fin r) (Fin r) R) i j = 0 := by
  rw [stdMaxParab, mem_parab_two]
  refine ⟨fun H i j hj hi => ?_, fun H j i => H _ _ (by simp) (by simp)⟩
  have := H ⟨i - a, by omega⟩ ⟨j, hj⟩
  have e1 : stdSum h (Sum.inr ⟨i - a, by omega⟩) = i := Fin.ext (by simp; omega)
  have e2 : stdSum h (Sum.inl ⟨j, hj⟩) = j := Fin.ext (by simp)
  rwa [e1, e2] at this

example {R : Type} [CommRing R] {a b r : ℕ} (h : a + b = r) :
    ∃ P N : Subgroup (GL (Fin r) R), IsParabRad P N ∧ ∃ g₀, P ≤ conjBy g₀ (stdMaxParab R h) := by
  have h' : ∑ i, ![a, b] i = r := by simpa using h
  refine ⟨_, _, ⟨2, ![a, b], h', 1, rfl, rfl⟩, 1, fun g hg => ?_⟩
  rw [mem_conjBy] at hg ⊢
  rw [stdMaxParab, mem_parab_two]
  intro j i
  have := mem_parab_iff.1 hg 1 0 j i (by decide)
  have e1 : stdBlocks ![a, b] h' ⟨1, j⟩ = stdSum h (Sum.inr j) :=
    Fin.ext (((stdBlocks_val ![a, b] h' 1 j).trans (congrArg (· + (j : ℕ)) (Fin.sum_univ_one _))).trans
      (stdSum_inr h j).symm)
  have e2 : stdBlocks ![a, b] h' ⟨0, i⟩ = stdSum h (Sum.inl i) :=
    Fin.ext (((stdBlocks_val ![a, b] h' 0 i).trans (zero_add _)).trans (stdSum_inl h i).symm)
  exact e1 ▸ e2 ▸ this

example {Q : Type} [Group Q] (H : Subgroup Q) : ¬ NoFixed (Representation.trivial ℂ Q ℂ) H :=
  fun h => one_ne_zero (h 1 fun _ _ => rfl)

end GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic
