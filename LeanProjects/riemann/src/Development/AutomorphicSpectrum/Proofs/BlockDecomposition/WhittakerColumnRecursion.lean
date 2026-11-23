import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def colEntries {d j : ℕ} (hj : j < d) (u : GL (Fin d) K) : Fin j → K :=
  fun i => (u : Matrix (Fin d) (Fin d) K) ⟨i, i.2.trans hj⟩ ⟨j, hj⟩

theorem sum_dite_col {d j : ℕ} (hj : j < d) (r : Fin j → K) (M : Matrix (Fin d) (Fin d) K) :
    ∑ i : Fin d, ∑ l : Fin d, (if h : (l : ℕ) = j ∧ (i : ℕ) < j then r ⟨i, h.2⟩ else 0) * M i l =
      ∑ i : Fin j, r i * M ⟨i, i.2.trans hj⟩ ⟨j, hj⟩ := by
  have inner : ∀ i : Fin d, ∑ l : Fin d, (if h : (l : ℕ) = j ∧ (i : ℕ) < j then r ⟨i, h.2⟩ else 0) * M i l =
      if h : (i : ℕ) < j then r ⟨i, h⟩ * M i ⟨j, hj⟩ else 0 := by
    intro i
    rw [Finset.sum_eq_single ⟨j, hj⟩]
    · by_cases h : (i : ℕ) < j
      · rw [dif_pos ⟨rfl, h⟩, dif_pos h]
      · rw [dif_neg (fun h' => h h'.2), dif_neg h, zero_mul]
    · intro l _ hl
      have hl' : ¬ ((l : ℕ) = j ∧ (i : ℕ) < j) := fun h => hl (Fin.ext h.1)
      rw [dif_neg hl', zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp only [inner]
  rw [show (∑ i : Fin d, if h : (i : ℕ) < j then r ⟨i, h⟩ * M i ⟨j, hj⟩ else 0) =
      ∑ i ∈ (Finset.univ : Finset (Fin j)).map (Fin.castLEEmb hj.le),
        (if h : (i : ℕ) < j then r ⟨i, h⟩ * M i ⟨j, hj⟩ else 0) from ?_]
  · rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.castLEEmb_apply, Fin.val_castLE, dif_pos i.2]
    rfl
  · symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hij : ¬ (i : ℕ) < j := by
      intro h
      apply hi
      exact Finset.mem_map.mpr ⟨⟨i, h⟩, Finset.mem_univ _, Fin.ext rfl⟩
    rw [dif_neg hij]

theorem patChar_colGeR {d j : ℕ} (hj : j < d) (r : Fin j → K) (ψ₀ : AddChar K ℂ) (u : GL (Fin d) K) :
    patChar (colGeR K d j r) ψ₀ u =
      patChar (colGeE K d (j + 1)) ψ₀ u * ψ₀ (∑ i, r i * colEntries hj u i) := by
  unfold patChar
  rw [← AddChar.map_add_eq_mul]
  congr 1
  rw [show (∑ i, r i * colEntries hj u i) =
      ∑ i : Fin j, r i * (u : Matrix (Fin d) (Fin d) K) ⟨i, i.2.trans hj⟩ ⟨j, hj⟩ from rfl,
    ← sum_dite_col hj r (u : Matrix (Fin d) (Fin d) K), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  unfold colGeR
  ring

theorem mem_patSet_succ_iff {d j : ℕ} (hj : j < d) (u : GL (Fin d) K) :
    u ∈ patSet K (colGe d (j + 1)) ↔ u ∈ patSet K (colGe d j) ∧ colEntries hj u = 0 := by
  simp only [patSet, Set.mem_setOf_eq, colGe]
  constructor
  · intro h
    refine ⟨fun i l => ⟨(h i l).1, fun hne hn => (h i l).2 hne (fun hc => hn ⟨hc.1, by
      have h2 := hc.2; omega⟩)⟩, ?_⟩
    funext i
    have hi2 := i.2
    have hi : (⟨i, i.2.trans hj⟩ : Fin d) ≠ ⟨j, hj⟩ := by
      intro h'
      have h3 := congrArg Fin.val h'
      simp only [Fin.val_mk] at h3
      omega
    exact (h _ _).2 hi (fun hc => by
      have h2 := hc.2
      simp only [Fin.val_mk] at h2
      omega)
  · rintro ⟨h, hc⟩ i l
    refine ⟨(h i l).1, fun hne hn => ?_⟩
    by_cases hlj : (l : ℕ) = j ∧ i < l
    · have h3 : (i : ℕ) < l := hlj.2
      have hij : (i : ℕ) < j := by omega
      have h4 := congrFun hc ⟨i, hij⟩
      have hl : l = ⟨j, hj⟩ := Fin.ext hlj.1
      subst hl
      exact h4
    · apply (h i l).2 hne
      rintro ⟨h1, h2⟩
      apply hn
      refine ⟨h1, ?_⟩
      have h5 : (l : ℕ) ≠ j := fun h3 => hlj ⟨h3, h1⟩
      omega

theorem wh_colGe_succ_eq_sum (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ)
    (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ) (hj : j < d)
    (hc : (patSet K (colGe d j)).ncard = Fintype.card K ^ j * (patSet K (colGe d (j + 1))).ncard)
    (ho : ∀ x : Fin j → K, (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) =
      if x = 0 then (Fintype.card K : ℂ) ^ j else 0) :
    wh (colGe d (j + 1)) (colGeE K d (j + 1)) ψ₀ χ =
      ∑ r : Fin j → K, wh (colGe d j) (colGeR K d j r) ψ₀ χ := by
  classical
  have hq : (Fintype.card K : ℂ) ^ j ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hN : ((patSet K (colGe d j)).ncard : ℂ)⁻¹ * (Fintype.card K : ℂ) ^ j =
      ((patSet K (colGe d (j + 1))).ncard : ℂ)⁻¹ := by
    rw [hc, Nat.cast_mul, Nat.cast_pow, mul_inv, mul_comm (((Fintype.card K : ℂ) ^ j)⁻¹), mul_assoc,
      inv_mul_cancel₀ hq, mul_one]
  have hu : ∀ u : GL (Fin d) K, (∑ r : Fin j → K, if u ∈ patSet K (colGe d j) then
      (patChar (colGeR K d j r) ψ₀ u)⁻¹ * χ u else 0) =
      (Fintype.card K : ℂ) ^ j * (if u ∈ patSet K (colGe d (j + 1)) then
        (patChar (colGeE K d (j + 1)) ψ₀ u)⁻¹ * χ u else 0) := by
    intro u
    by_cases hP : u ∈ patSet K (colGe d j)
    · rw [Finset.sum_congr rfl (fun r _ => if_pos hP)]
      simp only [patChar_colGeR hj, mul_inv]
      rw [show (∑ r : Fin j → K, (patChar (colGeE K d (j + 1)) ψ₀ u)⁻¹ *
          (ψ₀ (∑ i, r i * colEntries hj u i))⁻¹ * χ u) =
          ((patChar (colGeE K d (j + 1)) ψ₀ u)⁻¹ * χ u) *
            ∑ r : Fin j → K, (ψ₀ (∑ i, r i * colEntries hj u i))⁻¹ by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring]
      rw [ho (colEntries hj u)]
      by_cases hx : colEntries hj u = 0
      · have hmem : u ∈ patSet K (colGe d (j + 1)) := (mem_patSet_succ_iff hj u).mpr ⟨hP, hx⟩
        rw [if_pos hx, if_pos hmem]
        ring
      · have hmem : u ∉ patSet K (colGe d (j + 1)) := fun h => hx ((mem_patSet_succ_iff hj u).mp h).2
        rw [if_neg hx, if_neg hmem]
        ring
    · have hmem : u ∉ patSet K (colGe d (j + 1)) := fun h => hP ((mem_patSet_succ_iff hj u).mp h).1
      rw [if_neg hmem, mul_zero]
      exact Finset.sum_eq_zero (fun r _ => if_neg hP)
  unfold wh
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [hu]
  rw [← Finset.mul_sum, ← mul_assoc, hN]

end GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier
