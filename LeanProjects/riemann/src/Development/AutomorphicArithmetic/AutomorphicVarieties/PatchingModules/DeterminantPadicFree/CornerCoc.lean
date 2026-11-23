import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem cut_conj {F : Type} [Field F] {n : ℕ} (p q : Fin n → Prop) [DecidablePred p] [DecidablePred q]
    [∀ i j, Decidable (p i ∧ q j)] (A Z B : Matrix (Fin n) (Fin n) F)
    (hA : ∀ i k, ¬ (p i ↔ p k) → A i k = 0) (hB : ∀ i k, ¬ (q i ↔ q k) → B i k = 0) :
    (Matrix.of fun i j => if p i ∧ q j then (A * Z * B) i j else 0) =
      A * (Matrix.of fun i j => if p i ∧ q j then Z i j else 0) * B := by
  ext i j
  have key : (if p i ∧ q j then (A * Z * B) i j else 0) =
      ∑ m, ∑ k, if p i ∧ q j then A i k * Z k m * B m j else 0 := by
    split_ifs
    · simp only [Matrix.mul_apply, Finset.sum_mul]
    · simp
  rw [Matrix.of_apply, key]
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.of_apply]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h1 : p i ↔ p k
  · by_cases h2 : q m ↔ q j
    · by_cases h : p i ∧ q j
      · rw [if_pos h, if_pos ⟨h1.1 h.1, h2.2 h.2⟩]
      · rw [if_neg h, if_neg (fun h' => h ⟨h1.2 h'.1, h2.1 h'.2⟩)]; simp
    · simp [hB m j h2]
  · simp [hA i k h1]

private theorem cV_conj {F : Type} [Field F] {n a : ℕ} {A B : Matrix (Fin n) (Fin n) F}
    (hA : A ∈ Ev F F n a) (hB : B ∈ Ev F F n a) (Z : Matrix (Fin n) (Fin n) F) :
    cV a (A * Z * B) = A * cV a Z * B ∧ cV' a (A * Z * B) = A * cV' a Z * B := by
  have hA' : ∀ i k : Fin n, ¬ ((i : ℕ) < a ↔ (k : ℕ) < a) → A i k = 0 := fun i k h => by
    simpa using (hA i k).2 h
  have hB' : ∀ i k : Fin n, ¬ ((i : ℕ) < a ↔ (k : ℕ) < a) → B i k = 0 := fun i k h => by
    simpa using (hB i k).2 h
  exact ⟨cut_conj (fun i => (i : ℕ) < a) (fun i => ¬ (i : ℕ) < a) A Z B hA'
      (fun i k h => hB' i k (fun e => h (not_congr e))),
    cut_conj (fun i => ¬ (i : ℕ) < a) (fun i => (i : ℕ) < a) A Z B
      (fun i k h => hA' i k (fun e => h (not_congr e))) hB'⟩

private theorem cV_lin {F : Type} [Field F] {n : ℕ} (a : ℕ) (c : F) (Y Z : Matrix (Fin n) (Fin n) F) :
    (cV a (Y + c • Z) = cV a Y + c • cV a Z ∧ cV' a (Y + c • Z) = cV' a Y + c • cV' a Z) ∧
    (cV a (c • Z - Y) = c • cV a Z - cV a Y ∧ cV' a (c • Z - Y) = c • cV' a Z - cV' a Y) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ext i j <;>
    simp only [cV, cV', Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply] <;>
    split_ifs <;> simp

theorem UpperTheory.V.Pa.Det.cornerCoc :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (S : Set G) (z : G → Matrix (Fin n) (Fin n) F), TwCoc χ D.r S z → (TwCoc χ D.r S fun g => cV D.a (z g)) ∧ (TwCoc χ D.r S fun g => cV' D.a (z g)) ∧ (∀ Y g, cV D.a (dTw χ D.r Y g) = dTw χ D.r (cV D.a Y) g ∧ cV' D.a (dTw χ D.r Y g) = dTw χ D.r (cV' D.a Y) g) ∧ ∀ Z : Matrix (Fin n) (Fin n) F, cV D.a Z ∈ Od F F n D.a ∧ cV' D.a Z ∈ Od F F n D.a ∧ (cV D.a Z)ᵀ = cV' D.a Zᵀ ∧ (Z ∈ Od F F n D.a → cV D.a Z + cV' D.a Z = Z) := by
  intro F G _ _ n D χ S z hz
  refine ⟨fun g hg h hh => ?_, fun g hg h hh => ?_, fun Y g => ⟨?_, ?_⟩, fun Z => ⟨?_, ?_, ?_, fun hZ => ?_⟩⟩
  · beta_reduce
    rw [hz g hg h hh, (cV_lin _ _ _ _).1.1, (cV_conj (D.ev _) (D.ev _) _).1]
  · beta_reduce
    rw [hz g hg h hh, (cV_lin _ _ _ _).1.2, (cV_conj (D.ev _) (D.ev _) _).2]
  · unfold dTw
    rw [(cV_lin _ _ _ _).2.1, (cV_conj (D.ev _) (D.ev _) _).1]
  · unfold dTw
    rw [(cV_lin _ _ _ _).2.2, (cV_conj (D.ev _) (D.ev _) _).2]
  · intro i j
    refine ⟨fun e => ?_, fun _ => Submodule.mem_top⟩
    rw [Submodule.mem_bot, cV, Matrix.of_apply, if_neg (fun h => h.2 (e.1 h.1))]
  · intro i j
    refine ⟨fun e => ?_, fun _ => Submodule.mem_top⟩
    rw [Submodule.mem_bot, cV', Matrix.of_apply, if_neg (fun h => h.1 (e.2 h.2))]
  · ext i j
    simp only [cV, cV', Matrix.of_apply, Matrix.transpose_apply, and_comm]
  · ext i j
    have h0 : ((i : ℕ) < D.a ↔ (j : ℕ) < D.a) → Z i j = 0 := fun e => by simpa using (hZ i j).1 e
    simp only [cV, cV', Matrix.of_apply, Matrix.add_apply]
    by_cases hi : (i : ℕ) < D.a <;> by_cases hj : (j : ℕ) < D.a
    · simp [hi, hj, h0 (iff_of_true hi hj)]
    · rw [if_pos ⟨hi, hj⟩, if_neg (fun h => h.1 hi), add_zero]
    · rw [if_neg (fun h => hi h.1), if_pos ⟨hi, hj⟩, zero_add]
    · rw [if_neg (fun h => hi h.1), if_neg (fun h => hj h.2), add_zero, h0 (iff_of_false hi hj)]
