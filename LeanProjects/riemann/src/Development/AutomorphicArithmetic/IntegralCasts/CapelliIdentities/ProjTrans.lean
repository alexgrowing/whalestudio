import Mathlib

private def UpperTheory.Reformulated.B.Qi50.proj {P : ℕ → Type 1} (t : (j : ℕ) → P (j + 1) → P j)
    {i j : ℕ} (h : i ≤ j) : P j → P i :=
  Nat.leRec (motive := fun j _ => P j → P i) id (fun k _ f => f ∘ t k) h

private theorem UpperTheory.Reformulated.B.Qi50.proj_self {P : ℕ → Type 1} (t : (j : ℕ) → P (j + 1) → P j)
    {i : ℕ} (h : i ≤ i) (a : P i) : UpperTheory.Reformulated.B.Qi50.proj t h a = a := by
  unfold UpperTheory.Reformulated.B.Qi50.proj
  rw [Nat.leRec_self]
  rfl

private theorem UpperTheory.Reformulated.B.Qi50.proj_succ {P : ℕ → Type 1} (t : (j : ℕ) → P (j + 1) → P j)
    {i j : ℕ} (h : i ≤ j) (h' : i ≤ j + 1) (a : P (j + 1)) :
    UpperTheory.Reformulated.B.Qi50.proj t h' a = UpperTheory.Reformulated.B.Qi50.proj t h (t j a) := by
  unfold UpperTheory.Reformulated.B.Qi50.proj
  rw [Nat.leRec_succ _ _ h]
  rfl

private theorem UpperTheory.Reformulated.B.Qi50.proj_trans {P : ℕ → Type 1} (t : (j : ℕ) → P (j + 1) → P j)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (a : P k) :
    UpperTheory.Reformulated.B.Qi50.proj t hij (UpperTheory.Reformulated.B.Qi50.proj t hjk a)
      = UpperTheory.Reformulated.B.Qi50.proj t (hij.trans hjk) a := by
  induction k, hjk using Nat.le_induction with
  | base => rw [UpperTheory.Reformulated.B.Qi50.proj_self]
  | succ k hk ih =>
    rw [UpperTheory.Reformulated.B.Qi50.proj_succ t hk, UpperTheory.Reformulated.B.Qi50.proj_succ t (hij.trans hk), ih]

theorem UpperTheory.Reformulated.B.Qi50.seq_sec :
    ∀ (P : ℕ → Type 1),
    (∀ (j : ℕ), Finite (P j)) →
      (∀ (j : ℕ), Nonempty (P j)) →
        ∀ (t : (j : ℕ) → P (j + (1 : ℕ)) → P j), ∃ (s : (j : ℕ) → P j), ∀ (j : ℕ), t j (s (j + (1 : ℕ))) = s j := by
  intro P hfin hne t
  obtain ⟨s, hs⟩ := exists_seq_forall_proj_of_forall_finite (α := P)
    (fun h => UpperTheory.Reformulated.B.Qi50.proj t h)
    (fun _ a => UpperTheory.Reformulated.B.Qi50.proj_self t _ a)
    (fun _ _ _ hij hjk a => UpperTheory.Reformulated.B.Qi50.proj_trans t hij hjk a)
    (fun _ _ => Set.toFinite _)
  refine ⟨s, fun j => ?_⟩
  have h := hs (Nat.le_succ j)
  rwa [UpperTheory.Reformulated.B.Qi50.proj_succ t le_rfl, UpperTheory.Reformulated.B.Qi50.proj_self] at h
