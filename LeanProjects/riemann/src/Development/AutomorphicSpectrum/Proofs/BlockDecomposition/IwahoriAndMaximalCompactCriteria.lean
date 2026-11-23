import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwEntries

variable {E : Type} [Field E] [NumberField E]

theorem rel_le_one_iff (w : Pl E) (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one

theorem rel_lt_one_iff (w : Pl E) (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x < 1 ↔ Valued.v x < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).lt_one_iff_lt_one

theorem mem_KGL_iff (w : Pl E) (n : ℕ) (g : GLw n w) :
    g ∈ GlobalTheory.LFun.KGL w n ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
  have key : ∀ x : GLw n w, x ∈ GlobalTheory.LFun.KGL w n → ∀ i j, Valued.v (x.val i j) ≤ 1 := by
    rintro x ⟨u, rfl⟩ i j
    exact (u.val i j).2
  constructor
  · exact fun h => ⟨key g h, key _ (inv_mem h)⟩
  · rintro ⟨h1, h2⟩
    have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨(g⁻¹ : GLw n w).1 i j, h2 i j⟩,
      hi ?_, hi ?_⟩, Units.ext rfl⟩
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul

theorem mem_KO_iff (w : Pl E) (n : ℕ) (g : GLw n w) :
    g ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) ↔
      (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
  have key : ∀ x : GLw n w, x ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) →
      ∀ i j, Valued.v (x.val i j) ≤ 1 := by
    rintro x ⟨u, rfl⟩ i j
    exact (rel_le_one_iff w _).1 (u.val i j).2
  constructor
  · exact fun h => ⟨key g h, key _ (inv_mem h)⟩
  · rintro ⟨h1, h2⟩
    let O := ValuativeRel.valuation (w.adicCompletion E) |>.integer
    have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨Matrix.of fun i j => ⟨_, (rel_le_one_iff w _).2 (h1 i j)⟩,
      Matrix.of fun i j => ⟨(g⁻¹ : GLw n w).1 i j, (rel_le_one_iff w _).2 (h2 i j)⟩, hi ?_, hi ?_⟩,
      Units.ext rfl⟩
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul

theorem iwGL_KGL_entries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (g : GLw n w), (g ∈ iwGL n w ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ (∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) ∧ ∀ i j, j < i → Valued.v (g.val i j) < 1) ∧ (g ∈ GlobalTheory.LFun.KGL w n ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) := by
  intro E _ _ _ w n g
  refine ⟨?_, mem_KGL_iff w n g⟩
  show g ∈ GlobalTheory.SmGL.iwahori (w.adicCompletion E) (Fin n) ↔ _
  rw [GlobalTheory.SmGL.mem_iwahori, mem_KO_iff, and_assoc]
  exact and_congr_right' (and_congr_right' (forall₃_congr fun i j _ => rel_lt_one_iff w _))

end GlobalTheory.CompanionTheory.IwEntries
