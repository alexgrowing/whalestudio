import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicHermitianFormGaloisMemOfMemCompletion
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClassesSelfDualOfSelfDual

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.ClassFin

theorem exists_reps {X ι : Type} (P : X → Prop) (c : X → ι → Prop) (R : X → X → Prop) (I : Set ι)
    (hI : I.Finite) (h1 : ∀ x, P x → ∃ i ∈ I, c x i)
    (h2 : ∀ x y i, P x → P y → c x i → c y i → R x y) :
    ∃ T : Set X, T.Finite ∧ (∀ y ∈ T, P y) ∧ ∀ x, P x → ∃ y ∈ T, R x y := by
  classical
  have : ∀ i : ι, ∃ T : Set X, T.Finite ∧ (∀ y ∈ T, P y) ∧ ∀ x, P x → c x i → ∃ y ∈ T, R x y := by
    intro i
    by_cases h : ∃ y, P y ∧ c y i
    · obtain ⟨y, hy, hc⟩ := h
      exact ⟨{y}, Set.finite_singleton _, by simpa using hy,
        fun x hx hxc => ⟨y, rfl, h2 x y i hx hy hxc hc⟩⟩
    · exact ⟨∅, Set.finite_empty, by simp, fun x hx hxc => (h ⟨x, hx, hxc⟩).elim⟩
  choose T hT1 hT2 hT3 using this
  refine ⟨⋃ i ∈ I, T i, hI.biUnion fun i _ => hT1 i, ?_, ?_⟩
  · intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨i, -, hy⟩ := hy
    exact hT2 i y hy
  · intro x hx
    obtain ⟨i, hi, hc⟩ := h1 x hx
    obtain ⟨y, hy, hR⟩ := hT3 i x hx hc
    exact ⟨y, Set.mem_biUnion hi hy, hR⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem fm_mul (γ δ : Matrix (Fin n) (Fin n) E) : fm F (γ * δ) = fm F γ * fm F δ := by
  ext i j : 1
  simp [fm, Matrix.mul_apply, TensorProduct.tmul_sum]

theorem fm_one : fm F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  ext i j : 1
  by_cases h : i = j
  · subst h; simp [fm, Algebra.TensorProduct.one_def]
  · simp [fm, h]

theorem mem_one_iff {E : Type} [Field E] [NumberField E] (x : E) :
    x ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ↔ IsIntegral ℤ x := by
  rw [FractionalIdeal.mem_one_iff]
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

end GlobalTheory.UnRep.ClassFin
