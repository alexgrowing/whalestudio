import Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementW
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.AntitoneOfMemGtBox

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

namespace WGT

open Formalism.InvariantFactorPaths.GelfandTsetlinBases (gtBox dGT stripsUp)

lemma extW_lt {n : ℕ} (la : Fin n → ℤ) {m : ℕ} (h : m < n) : extW la m = la ⟨m, h⟩ := by
  simp [extW, h]

lemma extW_val {n : ℕ} (la : Fin n → ℤ) (i : Fin n) : extW la i.val = la i := by
  simp [extW]

lemma dom_iff {n : ℕ} (μ : Fin n → ℤ) : Dom n (extW μ) ↔ Antitone μ := by
  constructor
  · intro h a b hab
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    simp only [Fin.mk_le_mk] at hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ k hak ih =>
      have h1 := h k hb
      rw [extW_lt μ hb, extW_lt μ (by omega)] at h1
      exact le_trans h1 (ih (by omega))
  · intro h m hm
    rw [extW_lt μ hm, extW_lt μ (by omega)]
    exact h (Fin.mk_le_mk.mpr (Nat.le_succ m))

lemma interl_iff {n : ℕ} (la : Fin n → ℤ) (μ : Fin (n + 1) → ℤ) :
    Interl n (extW la) (extW μ) ↔ la ∈ gtBox μ := by
  simp only [gtBox, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · intro h i
    have h1 := h i.val i.isLt
    rw [extW_val, extW_lt μ (by omega), extW_lt μ (by omega)] at h1
    exact ⟨h1.2, h1.1⟩
  · intro h l hl
    have h1 := h ⟨l, hl⟩
    rw [extW_lt la hl, extW_lt μ (by omega), extW_lt μ (by omega)]
    exact ⟨h1.2, h1.1⟩

lemma wsize_extW {n : ℕ} (μ : Fin n → ℤ) : wsize n (extW μ) = ∑ m, μ m := by
  rw [wsize, Finset.sum_range]
  simp [extW_val]

lemma hstrip_iff {n : ℕ} (μ ν : Fin n → ℤ) (B : ℕ) :
    (HStrip n (extW μ) (extW ν) ∧ wsize n (extW ν) - wsize n (extW μ) = B) ↔ ν ∈ stripsUp μ B := by
  have hm : ν ∈ stripsUp μ B ↔ (∀ i, ν i ∈ Finset.Icc (μ i) (μ i + B)) ∧
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip ν μ B := by
    classical
    unfold stripsUp
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
  rw [hm]
  simp only [Finset.mem_Icc, HStrip, Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip, wsize_extW]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hle : ∀ i, μ i ≤ ν i := fun i => by
      have := h1 i.val i.isLt
      rwa [extW_val, extW_val] at this
    have hadj : ∀ m m' : Fin n, m.val + 1 = m'.val → ν m' ≤ μ m := by
      intro m m' hmm
      have := h2 m.val (by omega)
      rw [extW_lt μ (by omega), extW_lt ν (by omega)] at this
      have e : (⟨m.val + 1, by omega⟩ : Fin n) = m' := Fin.ext hmm
      rw [e] at this
      exact this
    refine ⟨fun i => ⟨hle i, ?_⟩, hle, hadj, h3⟩
    have hsum : ν i - μ i ≤ ∑ m, ν m - ∑ m, μ m := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.single_le_sum (f := fun m => ν m - μ m) (fun m _ => by linarith [hle m]) (Finset.mem_univ i)
    linarith
  · rintro ⟨_, hle, hadj, h3⟩
    refine ⟨⟨fun m hm => ?_, fun m hm => ?_⟩, h3⟩
    · rw [extW_lt μ hm, extW_lt ν hm]
      exact hle _
    · rw [extW_lt μ (by omega), extW_lt ν (by omega)]
      exact hadj ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl

lemma antitone_of_mem_stripsUp {n : ℕ} {μ ν : Fin n → ℤ} {B : ℕ} (h : ν ∈ stripsUp μ B) : Antitone ν := by
  classical
  unfold stripsUp at h
  simp only [Finset.mem_filter] at h
  obtain ⟨_, hle, hadj, _⟩ := h
  apply (dom_iff ν).mp
  intro m hm
  rw [extW_lt ν hm, extW_lt ν (by omega)]
  exact le_trans (hadj ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl) (hle _)

lemma finsum_prop_eq_sum {α : Type*} (p : α → Prop) (s : Finset α) (f : α → ℝ) (h : ∀ a, p a ↔ a ∈ s) :
    ∑ᶠ (a : α) (_ : p a), f a = ∑ a ∈ s, f a := by
  simp_rw [h]
  exact finsum_mem_finset_eq_sum f s

end WGT

open WGT in
theorem weyl_dim_eq_gelfand_tsetlin : WeylGT := by
  intro hB n
  induction n with
  | zero =>
    intro μ _
    simp [weylDim, Formalism.InvariantFactorPaths.GelfandTsetlinBases.dGT]
  | succ n ih =>
    intro μ hμ
    rw [← hB n μ ((dom_iff μ).mpr hμ), finsum_prop_eq_sum _ (Formalism.InvariantFactorPaths.GelfandTsetlinBases.gtBox μ) _ (fun la => interl_iff la μ),
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.dGT_succ, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun la hla => ih la ?_)
    have hI := (interl_iff la μ).mpr hla
    apply (dom_iff la).mp
    intro m hm
    exact le_trans (hI (m + 1) hm).1 (hI m (by omega)).2

open WGT in
theorem pieri_of_branching : PieriOfBranch := by
  intro hB n μ B hn hdom
  have hW := weyl_dim_eq_gelfand_tsetlin hB
  have hμ := (dom_iff μ).mp hdom
  rw [finsum_prop_eq_sum _ (Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsUp μ B) _ (fun ν => hstrip_iff μ ν B),
    Finset.sum_congr rfl (fun ν hν => hW n ν (antitone_of_mem_stripsUp hν)), hW n μ hμ,
    ← Nat.cast_sum, Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.up n μ B hμ, Nat.cast_mul]
  have hc : (n + B - 1).choose B = (B + n - 1).choose (n - 1) := by
    rw [show B + n - 1 = n + B - 1 by omega]
    exact Nat.choose_symm_of_eq_add (by omega)
  rw [hc]

end Formalism.InvariantFactorPaths.BranchingDimensions
