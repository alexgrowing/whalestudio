import Mathlib
import Formalism.PeriodIntegrals.BesselPeriodGGP
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.DecreasingNodeGaps

namespace GlobalTheory.Proof.NodeGapNoncompact

open PI.BesselPeriodGGP GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps

theorem lam_eq (k r : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) :
    lam48 k r v b = param r k hk v b := by
  funext s
  unfold lam48
  by_cases h : s.val < k - 1
  · rw [dif_pos h]
    exact (param_cloud r k hk v b ⟨s.val, h⟩).symm
  · rw [dif_neg h]
    have hs : s = nodeIdx r k hk ⟨s.val - (k - 1), by have := s.isLt; omega⟩ := by
      apply Fin.ext
      simp only [nodeIdx]
      omega
    conv_rhs => rw [hs, param_node]

theorem sign_eq (k r : ℕ) (hk : 1 ≤ k) : eps48 k r = sign r k hk := by
  funext s
  unfold eps48
  by_cases h : s.val < k - 1
  · rw [if_pos h]
    exact (sign_cloud r k hk ⟨s.val, h⟩).symm
  · rw [if_neg h]
    have hs : s = nodeIdx r k hk ⟨s.val - (k - 1), by have := s.isLt; omega⟩ := by
      apply Fin.ext
      simp only [nodeIdx]
      omega
    conv_rhs => rw [hs, sign_node]
    simp only [Nat.even_iff]

theorem interlace_iff (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) :
    InterlacingCondition k r u v b ↔ Interlaces r k (param r k hk v b) u := by
  have hc : ∀ (i : ℕ) (hi : i < k - 1) (hi' : i < 2 * r + k + 1),
      param r k hk v b ⟨i, hi'⟩ = v ⟨i, hi⟩ := fun i hi _ => param_cloud r k hk v b ⟨i, hi⟩
  have hn : ∀ (hi' : k - 1 < 2 * r + k + 1),
      param r k hk v b ⟨k - 1, hi'⟩ = -b ⟨0, by omega⟩ :=
    fun _ => param_node r k hk v b ⟨0, by omega⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · by_cases h : i.val < k - 1
      · rw [hc i.val h]
        exact (h1 ⟨i.val, h⟩).1
      · obtain ⟨i, hi⟩ := i
        obtain rfl : i = k - 1 := by simp only at h; omega
        rw [hn]
        exact h2 hk
    · rw [hc i (by omega)]
      exact (h1 ⟨i, by omega⟩).2
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ⟨?_, ?_⟩, fun h => ?_⟩
    · have := h1 ⟨i.val, by have := i.isLt; omega⟩
      rwa [hc i.val i.isLt] at this
    · have := h2 i.val (by have := i.isLt; omega)
      rwa [hc i.val i.isLt] at this
    · have := h1 ⟨k - 1, by omega⟩
      rwa [hn] at this

theorem parity_iff (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) :
    HalfIntegralDifference k r u v b ↔ Parity r k (param r k hk v b) u := by
  unfold HalfIntegralDifference Parity
  rw [lam_eq k r hk]
  constructor
  · intro h s i
    obtain ⟨j, hj⟩ := h i s
    exact ⟨-j - 1, by push_cast; linarith⟩
  · intro h i s
    obtain ⟨j, hj⟩ := h s i
    exact ⟨-j - 1, by push_cast; linarith⟩

theorem gap_iff (h : ℝ) (r : ℕ) (b : Fin (2 * r + 2) → ℝ) :
    LowGapGe h r b ↔ NodeGapGe r b h := by
  constructor
  · intro H i hi
    have := H ⟨i, by omega⟩ hi
    simp only at this
    linarith
  · intro H j hj
    have := H j.val hj
    simp only [Fin.eta] at this
    linarith

theorem le_sub_of_nodeGapGe (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (h : ℝ) (hd : IsDecreasing r k hk v b) (hg : NodeGapGe r b h)
    (s t : Fin (2 * r + k + 1)) (hst : s < t) (hne : sign r k hk s ≠ sign r k hk t) :
    h ≤ param r k hk v b s - param r k hk v b t := by
  have hlt : s.val < t.val := hst
  have ht : k ≤ t.val := by
    by_contra hc
    apply hne
    rw [← sign_eq]
    unfold eps48
    have h1 : s.val < k - 1 := by omega
    rw [if_pos h1]
    by_cases h2 : t.val < k - 1
    · rw [if_pos h2]
    · rw [if_neg h2]
      have : t.val - (k - 1) = 0 := by omega
      simp [this]
  have htl := t.isLt
  have hi : t.val - k + 1 < 2 * r + 2 := by omega
  have h1 := hg (t.val - k) hi
  have e1 : t = nodeIdx r k hk ⟨t.val - k + 1, hi⟩ := by
    apply Fin.ext
    simp only [nodeIdx]
    omega
  have e2 : s ≤ nodeIdx r k hk ⟨t.val - k, by omega⟩ := by
    simp only [nodeIdx, Fin.le_def]
    omega
  have h2 := hd.antitone e2
  have h3 : param r k hk v b t = -b ⟨t.val - k + 1, hi⟩ := by
    conv_lhs => rw [e1, param_node]
  rw [param_node] at h2
  linarith

theorem gap_iff_noncompact (k r : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (h : ℝ) (hd : IsDecreasing r k hk v b) :
    LowGapGe h r b ↔ NoncompactGapGe r k hk (param r k hk v b) h := by
  rw [gap_iff]
  refine ⟨fun hg s t hne => ?_, nodeGapGe_of_noncompactGapGe r k hk v b h hd⟩
  rcases lt_trichotomy s t with hst | hst | hst
  · exact (le_sub_of_nodeGapGe r k hk v b h hd hg s t hst hne).trans (le_abs_self _)
  · exact absurd (congrArg _ hst) hne
  · rw [abs_sub_comm]
    exact (le_sub_of_nodeGapGe r k hk v b h hd hg t s hst hne.symm).trans (le_abs_self _)

theorem isHCParam_iff (k r : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) :
    Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) ↔
      IsDecreasing r k hk v b ∧ IsShiftedIntegral (param r k hk v b) := by
  unfold Formalism.QuantumDeterminants.IsHCParam IsDecreasing IsShiftedIntegral
  rw [lam_eq k r hk]
  refine and_congr Iff.rfl (forall_congr' fun s => exists_congr fun z => ?_)
  constructor <;> intro h <;> linarith

theorem gapAtLeast_iff (k r : ℕ) (hk : 1 ≤ k) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) :
    Formalism.QuantumDeterminants.GapAtLeast (eps48 k r) lam h ↔ NoncompactGapGe r k hk lam h := by
  rw [sign_eq k r hk]
  rfl

theorem typings_equiv (k r : ℕ) (hk : 1 ≤ k) :
    (∀ (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ), lam48 k r v b = param r k hk v b) ∧
    eps48 k r = sign r k hk ∧
    (∀ (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ),
      InterlacingCondition k r u v b ↔ Interlaces r k (param r k hk v b) u) ∧
    (∀ (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ),
      HalfIntegralDifference k r u v b ↔ Parity r k (param r k hk v b) u) ∧
    (∀ (h : ℝ) (b : Fin (2 * r + 2) → ℝ), LowGapGe h r b ↔ NodeGapGe r b h) :=
  ⟨lam_eq k r hk, sign_eq k r hk, interlace_iff k r hk, parity_iff k r hk,
    fun h b => gap_iff h r b⟩

end GlobalTheory.Proof.NodeGapNoncompact
