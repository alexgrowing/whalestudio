import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingsAgreeOnSubfieldNeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointSeparateStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

theorem exists_mul_eq_of_generic_unique_complexPoint : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (σ : K →+* ℂ) (A B : Subalgebra K Ω), A.FG → B.FG → B ≤ A → (∀ b ∈ B, b ≠ 0 → ∃ x : A →+* ℂ, (∀ k : K, x (algebraMap K A k) = σ k) ∧ (∀ hb : b ∈ A, x ⟨b, hb⟩ ≠ 0) ∧ ∀ y : A →+* ℂ, (∀ k : K, y (algebraMap K A k) = σ k) → (∀ a : A, (a : Ω) ∈ B → y a = x a) → y = x) → ∀ a ∈ A, ∃ p ∈ B, ∃ q ∈ B, q ≠ 0 ∧ a * q = p := by
  intro K Ω _ _ _ σ A B hA hB hBA H a haA
  by_contra hne
  haveI : CharZero K := ⟨fun m n h => Nat.cast_injective (R := ℂ) (by simpa using congrArg σ h)⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  let L := IntermediateField.adjoin K (B : Set Ω)
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have haL : a ∉ Set.range (algebraMap L Ω) := by
    rintro ⟨l, hl⟩
    have hmem : a ∈ L := hl ▸ l.2
    obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.1 hmem
    rw [Algebra.adjoin_eq] at hr hs
    apply hne
    by_cases hs0 : s = 0
    · exact ⟨0, B.zero_mem, 1, B.one_mem, one_ne_zero, by simp [hs0]⟩
    · exact ⟨r, hr, s, hs, hs0, div_mul_cancel₀ r hs0⟩
  obtain ⟨F, _, i₁, i₂, hi, hne2⟩ := GlobalTheory.T.exists_ringHom_pair_eq_on_subfield_ne_of_not_mem_range L Ω a haL
  letI : Algebra B A := (Subalgebra.inclusion hBA).toRingHom.toAlgebra
  haveI : IsScalarTower K B A := IsScalarTower.of_algebraMap_eq fun k => rfl
  haveI : Algebra.FiniteType K A := (Subalgebra.fg_iff_finiteType A).1 hA
  haveI : Algebra.FiniteType K B := (Subalgebra.fg_iff_finiteType B).1 hB
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  haveI : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType K B A
  let j₁ : A →+* F := i₁.comp A.val.toRingHom
  let j₂ : A →+* F := i₂.comp A.val.toRingHom
  have hBL : ∀ b : B, (b : Ω) = algebraMap L Ω ⟨b, IntermediateField.subset_adjoin K _ b.2⟩ := fun b => rfl
  have hj : j₁.comp (algebraMap B A) = j₂.comp (algebraMap B A) := by
    ext b
    change i₁ (b : Ω) = i₂ (b : Ω)
    rw [hBL b]
    exact congrArg (fun f : L →+* F => f _) hi
  have hinj : Function.Injective (j₁.comp (algebraMap B A)) := by
    intro b c h
    exact Subtype.ext (i₁.injective h)
  obtain ⟨q, hq, Hq⟩ := GlobalTheory.T.exists_ne_zero_forall_complexPoint_separate' B A F j₁ j₂ hj hinj ⟨a, haA⟩ hne2
  obtain ⟨x, hxσ, hxq, hxu⟩ := H q q.2 (fun h => hq (Subtype.ext h))
  let φ : B →+* ℂ := x.comp (algebraMap B A)
  have hφq : φ q ≠ 0 := hxq (hBA q.2)
  obtain ⟨y₁, y₂, h₁, h₂, hy⟩ := Hq φ hφq
  have key : ∀ y : A →+* ℂ, y.comp (algebraMap B A) = φ → y = x := by
    intro y hy
    refine hxu y (fun k => ?_) (fun a' ha' => ?_)
    · have e1 : algebraMap K A k = algebraMap B A (algebraMap K B k) := rfl
      rw [e1, ← hxσ k, e1]
      exact congrArg (fun f : B →+* ℂ => f (algebraMap K B k)) hy
    · have e1 : a' = algebraMap B A ⟨a', ha'⟩ := rfl
      rw [e1]
      exact congrArg (fun f : B →+* ℂ => f ⟨a', ha'⟩) hy
  exact hy (by rw [key y₁ h₁, key y₂ h₂])

end GlobalTheory.DegVal
