import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne

open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.card_dvd_of_partition_equal_size :
    ∀ (ι Q : Type) [Finite ι] (T : Q → Set ι) (d : ℕ), (∀ q, (T q).ncard = d) → (∀ i, ∃! q, i ∈ T q) →
      Nat.card Q ∣ Nat.card ι := by
  intro ι Q _ T d hT hu
  classical
  choose f hf hf' using hu
  have hfib : ∀ q, T q = {i | f i = q} := by
    intro q
    ext i
    constructor
    · intro h
      exact (hf' i q h).symm
    · intro h
      rw [Set.mem_setOf_eq] at h
      rw [← h]
      exact hf i
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : IsEmpty ι := ⟨fun i => by
      have h := hT (f i)
      rw [Set.ncard_eq_zero (Set.toFinite _)] at h
      have hi : i ∈ T (f i) := hf i
      rw [h] at hi
      simp at hi⟩
    rw [Nat.card_of_isEmpty (α := ι)]
    exact dvd_zero _
  · have hne : ∀ q, (T q).Nonempty := fun q =>
      Set.nonempty_of_ncard_ne_zero (by rw [hT q]; omega)
    choose g hg using hne
    have ginj : Function.Injective g := by
      intro q q' h
      calc q = f (g q) := hf' _ _ (hg q)
        _ = f (g q') := by rw [h]
        _ = q' := (hf' _ _ (hg q')).symm
    haveI : Finite Q := Finite.of_injective g ginj
    letI : Fintype Q := Fintype.ofFinite Q
    have hc : ∀ q, Nat.card {x // f x = q} = d := fun q => by
      rw [← hT q, hfib q, ← Nat.card_coe_set_eq]
      rfl
    have key : Nat.card ι = Nat.card Q * d := by
      rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
      simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
    rw [key]
    exact dvd_mul_right _ _
