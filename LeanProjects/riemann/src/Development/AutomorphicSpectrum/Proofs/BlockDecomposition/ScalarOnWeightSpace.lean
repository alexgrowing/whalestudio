import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SumOfLevelSizesEqStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardBlocksLevelSumStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FreeAlgebraActionOnSubquotientStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisSide

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PairMult.Asm

open Formalism.REAL (GlRel qdet)
open GlobalTheory.CompanionTheory.PairMult
open GlobalTheory.CompanionTheory.RgCOBlock (sz shift fb)
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ}

theorem mem_down {S : Finset (Fin n)} (hS : ∀ a b, b ≤ a → a ∈ S → b ∈ S) (a : Fin n) :
    a ∈ S ↔ (a : ℕ) < S.card :=
  _root_.UpperTheory.Reformulated.B.DYlb8.main hS a

theorem twice_sum_Ico (m d : ℕ) :
    2 * ∑ k ∈ Finset.Ico m (m + d), (k : ℝ) = 2 * (d : ℝ) * m + d * ((d : ℝ) - 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega), mul_add, ih]
    push_cast
    ring

theorem level_sum (lev : Fin n → ℕ) (hm : Monotone lev) (c : ℕ) :
    2 * ∑ a ∈ univ.filter (fun a => lev a = c), ((a : ℕ) : ℝ) =
      2 * ((univ.filter fun a => lev a = c).card : ℝ) * ((univ.filter fun a => lev a < c).card : ℝ) +
        ((univ.filter fun a => lev a = c).card : ℝ) * (((univ.filter fun a => lev a = c).card : ℝ) - 1) := by
  set d := (univ.filter fun a => lev a = c).card with hd
  set m := (univ.filter fun a => lev a < c).card with hmm
  have hlow : ∀ a, lev a < c ↔ (a : ℕ) < m := fun a => by
    have := mem_down (S := univ.filter fun a => lev a < c) (fun x y hyx hx => by
      rw [mem_filter] at hx ⊢
      exact ⟨mem_univ _, lt_of_le_of_lt (hm hyx) hx.2⟩) a
    simpa using this
  have hcard : (univ.filter fun a => lev a < c + 1).card = m + d := by
    rw [hmm, hd, ← Finset.card_union_of_disjoint]
    · congr 1
      ext a
      simp only [mem_filter, mem_univ, true_and, mem_union]
      omega
    · rw [Finset.disjoint_left]
      intro a h1 h2
      have := (mem_filter.1 h1).2
      have := (mem_filter.1 h2).2
      omega
  have hup : ∀ a, lev a < c + 1 ↔ (a : ℕ) < m + d := fun a => by
    have := mem_down (S := univ.filter fun a => lev a < c + 1) (fun x y hyx hx => by
      rw [mem_filter] at hx ⊢
      exact ⟨mem_univ _, lt_of_le_of_lt (hm hyx) hx.2⟩) a
    rw [hcard] at this
    simpa using this
  have hle : m + d ≤ n := by
    rw [← hcard]
    exact (card_le_univ _).trans_eq (Fintype.card_fin n)
  have hmap : (univ.filter fun a => lev a = c).map Fin.valEmbedding = Finset.Ico m (m + d) := by
    ext k
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have h1 := hlow a
      have h2 := hup a
      omega
    · rintro ⟨k1, k2⟩
      refine ⟨⟨k, by omega⟩, ?_, rfl⟩
      have h1 := hlow ⟨k, by omega⟩
      have h2 := hup ⟨k, by omega⟩
      simp only at h1 h2
      omega
  rw [← twice_sum_Ico, ← hmap, Finset.sum_map]
  rfl

section Alg

variable {W : Type} [AddCommGroup W] [Module ℂ W]

end Alg

section Spaces

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def cycQ (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (j : ℕ) : Submodule ℂ (Cq n V) where
  carrier := {x | SuppQ (inUL lev) x ∧ DegQ j x ∧ bdq E1 E2 x = 0}
  add_mem' := by
    rintro x y ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
    refine ⟨fun A hA i hi => ?_, fun A hA => ?_, by rw [map_add, h3, g3, add_zero]⟩
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g1 A hy i hi
      · exact h1 A hx i hi
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g2 A hy
      · exact h2 A hx
  zero_mem' := ⟨fun A hA => absurd rfl hA, fun A hA => absurd rfl hA, map_zero _⟩
  smul_mem' := by
    rintro c x ⟨h1, h2, h3⟩
    have hne : ∀ A, (c • x) A ≠ 0 → x A ≠ 0 := fun A hA hx => hA (by simp [hx])
    exact ⟨fun A hA => h1 A (hne A hA), fun A hA => h2 A (hne A hA), by rw [map_smul, h3, smul_zero]⟩

def bdyQ (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (j : ℕ) : Submodule ℂ (Cq n V) where
  carrier := {x | ∃ w : Cq n V, SuppQ (inUL lev) w ∧ DegQ (j + 1) w ∧ bdq E1 E2 w = x}
  add_mem' := by
    rintro _ _ ⟨x, h1, h2, rfl⟩ ⟨y, g1, g2, rfl⟩
    refine ⟨x + y, fun A hA i hi => ?_, fun A hA => ?_, map_add _ _ _⟩
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g1 A hy i hi
      · exact h1 A hx i hi
    · by_cases hx : x A = 0
      · have hy : y A ≠ 0 := fun hy => hA (by simp [hx, hy])
        exact g2 A hy
      · exact h2 A hx
  zero_mem' := ⟨0, fun A hA => absurd rfl hA, fun A hA => absurd rfl hA, map_zero _⟩
  smul_mem' := by
    rintro c _ ⟨x, h1, h2, rfl⟩
    have hne : ∀ A, (c • x) A ≠ 0 → x A ≠ 0 := fun A hA hx => hA (by simp [hx])
    exact ⟨c • x, fun A hA => h1 A (hne A hA), fun A hA => h2 A (hne A hA), map_smul _ _ _⟩

abbrev HQ (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (j : ℕ) : Type :=
  cycQ lev E1 E2 j ⧸ (bdyQ lev E1 E2 j).comap (cycQ lev E1 E2 j).subtype

abbrev levL (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (x : Bool × Fin n × Fin n) :
    Module.End ℂ (Cq n V) :=
  if lev x.2.1 = lev x.2.2 then (if x.1 then c1 E1 E2 x.2.1 x.2.2 else c2 E1 E2 x.2.1 x.2.2) else 0

abbrev fam {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] Module.End ℂ W) (s : Bool) (p q : Fin n) : Module.End ℂ W :=
  ρ (FreeAlgebra.ι ℂ (s, p, q))

end Spaces

end GlobalTheory.CompanionTheory.PairMult.Asm
