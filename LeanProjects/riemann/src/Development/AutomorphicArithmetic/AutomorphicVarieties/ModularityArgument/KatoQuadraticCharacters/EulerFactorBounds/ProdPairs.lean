import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

private theorem tp_inj (p M : ℕ) [NeZero p] [NeZero M] (s t : ZMod p)
    (h : ((M * s.val : ℕ) : ZMod (p * M)) = ((M * t.val : ℕ) : ZMod (p * M))) : s = t := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hlt : ∀ u : ZMod p, M * u.val < p * M := fun u => by
    rw [mul_comm p M]
    exact (Nat.mul_lt_mul_left hM).2 (ZMod.val_lt u)
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hlt s), Nat.mod_eq_of_lt (hlt t)] at h
  exact ZMod.val_injective p (Nat.eq_of_mul_eq_mul_left hM h)

private theorem tp_surj (p M : ℕ) [NeZero p] [NeZero M] (w : ZMod (p * M))
    (h : ZMod.castHom (dvd_mul_left M p) (ZMod M) w = 0) : ∃ t : ZMod p, w = ((M * t.val : ℕ) : ZMod (p * M)) := by
  have hw : M ∣ w.val := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, CharP.cast_eq_zero_iff (ZMod M) M] at h
    exact h
  obtain ⟨k, hk⟩ := hw
  have hkp : k < p := by
    have hv := ZMod.val_lt w
    rw [hk, mul_comm p M] at hv
    exact Nat.lt_of_mul_lt_mul_left hv
  refine ⟨(k : ZMod p), ?_⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hkp, ← hk, ZMod.natCast_zmod_val]

private theorem dn_up (p M : ℕ) [NeZero p] [NeZero M] (x : Row M) (i : Fin 2) :
    ZMod.castHom (dvd_mul_left M p) (ZMod M) (up p M x i) = ((p : ZMod M) • x) i := by
  unfold up
  rw [map_natCast]
  simp

private theorem prod_fib {G : Type} [CommMonoid G] (p M : ℕ) [NeZero p] [NeZero M] [NeZero (p * M)] (x : Row M)
    (S : Finset (Row (p * M))) (hS : ∀ z, z ∈ S ↔ dn p M z = (p : ZMod M) • x) (f : Row (p * M) → G) :
    ∏ z ∈ S, f z = ∏ t : Fin 2 → ZMod p, f (up p M x + tp p M t) := by
  have htp : ∀ (t : Fin 2 → ZMod p) (i : Fin 2),
      ZMod.castHom (dvd_mul_left M p) (ZMod M) (tp p M t i) = 0 := by
    intro t i
    show ZMod.castHom (dvd_mul_left M p) (ZMod M) ((M * (t i).val : ℕ) : ZMod (p * M)) = 0
    rw [map_natCast, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  symm
  refine Finset.prod_bij (fun t _ => up p M x + tp p M t) ?_ ?_ ?_ ?_
  · intro t _
    rw [hS]
    funext i
    show ZMod.castHom (dvd_mul_left M p) (ZMod M) (up p M x i + tp p M t i) = ((p : ZMod M) • x) i
    rw [map_add, dn_up, htp, add_zero]
  · intro t _ t' _ h
    funext i
    have hi := add_left_cancel (congrFun h i)
    exact tp_inj p M (t i) (t' i) hi
  · intro z hz
    rw [hS] at hz
    have hex : ∀ i, ∃ s : ZMod p, z i - up p M x i = ((M * s.val : ℕ) : ZMod (p * M)) := by
      intro i
      apply tp_surj p M
      have hzi : ZMod.castHom (dvd_mul_left M p) (ZMod M) (z i) = ((p : ZMod M) • x) i := congrFun hz i
      rw [map_sub, dn_up, hzi, sub_self]
    choose t ht using hex
    refine ⟨t, Finset.mem_univ _, ?_⟩
    funext i
    show up p M x i + ((M * (t i).val : ℕ) : ZMod (p * M)) = z i
    rw [← ht i]
    abel
  · intro t _
    rfl

private theorem lin_ne (p N : ℕ) [Fact p.Prime] (o : Option (Fin p)) : lin p N o ≠ 0 := by
  intro h
  cases o with
  | none => simpa [lin] using congrFun h 1
  | some j => simpa [lin] using congrFun h 0

private theorem lin_eq (p N : ℕ) [Fact p.Prime] (hN : (N : ZMod p) ≠ 0) (o o' : Option (Fin p)) (i i' : ZMod p) (hi : i ≠ 0)
    (h : i • lin p N o = i' • lin p N o') : o = o' := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some j' =>
      exfalso
      simp [lin] at h0 h1
      apply hi
      rw [← h0] at h1
      simpa using h1
  | some j =>
    cases o' with
    | none =>
      exfalso
      simp [lin] at h0
      exact hi h0
    | some j' =>
      simp [lin] at h0 h1
      subst h0
      have h2 : ((N * (j : ℕ) : ℕ) : ZMod p) = ((N * (j' : ℕ) : ℕ) : ZMod p) := by
        push_cast at h1 ⊢
        exact mul_left_cancel₀ hi h1
      push_cast at h2
      have h3 : ((j : ℕ) : ZMod p) = ((j' : ℕ) : ZMod p) := mul_left_cancel₀ hN h2
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt j'.isLt] at h3
      rw [Fin.ext h3]

private theorem lin_dep (p N : ℕ) [Fact p.Prime] (o : Option (Fin p)) (w : Fin 2 → ZMod p)
    (h : lin p N o 0 * w 1 - lin p N o 1 * w 0 = 0) : ∃ j : ZMod p, w = j • lin p N o := by
  cases o with
  | none =>
    refine ⟨w 1, ?_⟩
    funext i
    fin_cases i
    · simpa [lin] using h
    · simp [lin]
  | some j =>
    refine ⟨w 0, ?_⟩
    funext i
    fin_cases i
    · simp [lin]
    · simp [lin] at h ⊢
      linear_combination h

private theorem lin_surj (p N : ℕ) [Fact p.Prime] (hN : (N : ZMod p) ≠ 0) (w : Fin 2 → ZMod p) :
    ∃ (o : Option (Fin p)) (j : ZMod p), w = j • lin p N o := by
  by_cases h0 : w 0 = 0
  · exact ⟨none, lin_dep p N none w (by simp [lin, h0])⟩
  · refine ⟨some ⟨(w 1 / w 0 / N).val, ZMod.val_lt _⟩, lin_dep p N _ w ?_⟩
    simp only [lin]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id]
    field_simp
    ring

private theorem prod_dep {G : Type} [CommMonoid G] (p N : ℕ) [Fact p.Prime] (hN : (N : ZMod p) ≠ 0)
    (F : (Fin 2 → ZMod p) → (Fin 2 → ZMod p) → G) :
    ∏ o : Option (Fin p), ∏ ij ∈ (Finset.univ : Finset (ZMod p × ZMod p)).erase 0, F (ij.1 • lin p N o) (ij.2 • lin p N o) =
      ∏ tt ∈ (Finset.univ.filter (fun tt : (Fin 2 → ZMod p) × (Fin 2 → ZMod p) =>
        ¬ (tt.1 0 * tt.2 1 - tt.1 1 * tt.2 0 ≠ 0))).erase 0, F tt.1 tt.2 := by
  rw [← Finset.prod_product' (s := Finset.univ) (t := (Finset.univ : Finset (ZMod p × ZMod p)).erase 0)
    (fun o ij => F (ij.1 • lin p N o) (ij.2 • lin p N o))]
  refine Finset.prod_bij (fun oij _ => (oij.2.1 • lin p N oij.1, oij.2.2 • lin p N oij.1)) ?_ ?_ ?_ ?_
  · rintro ⟨o, i, j⟩ h
    have hne : ((i, j) : ZMod p × ZMod p) ≠ 0 := Finset.ne_of_mem_erase (Finset.mem_product.1 h).2
    rw [Finset.mem_erase, Finset.mem_filter]
    refine ⟨?_, Finset.mem_univ _, ?_⟩
    · intro h0
      apply hne
      have h1 := congrArg Prod.fst h0
      have h2 := congrArg Prod.snd h0
      simp only [Prod.fst_zero, Prod.snd_zero, smul_eq_zero] at h1 h2
      have hl := lin_ne p N o
      rw [show i = 0 from h1.resolve_right hl, show j = 0 from h2.resolve_right hl]
      rfl
    · rw [not_not]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  · rintro ⟨o, i, j⟩ h ⟨o', i', j'⟩ h' heq
    have hne : ((i, j) : ZMod p × ZMod p) ≠ 0 := Finset.ne_of_mem_erase (Finset.mem_product.1 h).2
    have hi := congrArg Prod.fst heq
    have hj := congrArg Prod.snd heq
    simp only at hi hj
    have ho : o = o' := by
      by_cases hi0 : i = 0
      · have hj0 : j ≠ 0 := by
          intro hj0
          apply hne
          rw [hi0, hj0]
          rfl
        exact lin_eq p N hN o o' j j' hj0 hj
      · exact lin_eq p N hN o o' i i' hi0 hi
    subst ho
    have hl := lin_ne p N o
    have e1 : i = i' := smul_left_injective (ZMod p) hl hi
    have e2 : j = j' := smul_left_injective (ZMod p) hl hj
    rw [e1, e2]
  · rintro ⟨t, t'⟩ hmem
    rw [Finset.mem_erase, Finset.mem_filter, not_not] at hmem
    obtain ⟨hne, -, hdet⟩ := hmem
    simp only at hdet
    by_cases ht : t = 0
    · obtain ⟨o, j, hj⟩ := lin_surj p N hN t'
      have hj0 : j ≠ 0 := by
        intro hj0
        apply hne
        rw [ht, hj, hj0, zero_smul]
        rfl
      refine ⟨⟨o, 0, j⟩, ?_, ?_⟩
      · rw [Finset.mem_product, Finset.mem_erase]
        refine ⟨Finset.mem_univ _, ?_, Finset.mem_univ _⟩
        intro h0
        exact hj0 (congrArg Prod.snd h0)
      · simp only [zero_smul]
        rw [ht, hj]
    · obtain ⟨o, i, hi⟩ := lin_surj p N hN t
      have hi0 : i ≠ 0 := by
        intro hi0
        apply ht
        rw [hi, hi0, zero_smul]
      have hd : lin p N o 0 * t' 1 - lin p N o 1 * t' 0 = 0 := by
        have hd' : i * (lin p N o 0 * t' 1 - lin p N o 1 * t' 0) = 0 := by
          rw [hi] at hdet
          simp only [Pi.smul_apply, smul_eq_mul] at hdet
          linear_combination hdet
        exact (mul_eq_zero.1 hd').resolve_left hi0
      obtain ⟨j, hj⟩ := lin_dep p N o t' hd
      refine ⟨⟨o, i, j⟩, ?_, ?_⟩
      · rw [Finset.mem_product, Finset.mem_erase]
        refine ⟨Finset.mem_univ _, ?_, Finset.mem_univ _⟩
        intro h0
        exact hi0 (congrArg Prod.fst h0)
      · simp only
        rw [hi, hj]
  · intro _ _
    rfl

private theorem prod_pairs {G : Type} [CommMonoid G] (p N : ℕ) [Fact p.Prime] (hN : (N : ZMod p) ≠ 0)
    (F : (Fin 2 → ZMod p) → (Fin 2 → ZMod p) → G) :
    (∏ tt ∈ Finset.univ.filter (fun tt : (Fin 2 → ZMod p) × (Fin 2 → ZMod p) =>
        tt.1 0 * tt.2 1 - tt.1 1 * tt.2 0 ≠ 0), F tt.1 tt.2) *
      ∏ o : Option (Fin p), ∏ i : ZMod p, ∏ j : ZMod p, F (i • lin p N o) (j • lin p N o) =
      (∏ t, ∏ t', F t t') * F 0 0 ^ p := by
  have hinner : ∀ o : Option (Fin p), ∏ i : ZMod p, ∏ j : ZMod p, F (i • lin p N o) (j • lin p N o) =
      (∏ ij ∈ (Finset.univ : Finset (ZMod p × ZMod p)).erase 0, F (ij.1 • lin p N o) (ij.2 • lin p N o)) * F 0 0 := by
    intro o
    rw [← Fintype.prod_prod_type' (fun i j => F (i • lin p N o) (j • lin p N o))]
    rw [← Finset.mul_prod_erase Finset.univ (fun ij : ZMod p × ZMod p => F (ij.1 • lin p N o) (ij.2 • lin p N o))
      (Finset.mem_univ 0)]
    rw [mul_comm]
    congr 1
    simp
  have hmem : (0 : (Fin 2 → ZMod p) × (Fin 2 → ZMod p)) ∈ Finset.univ.filter
      (fun tt : (Fin 2 → ZMod p) × (Fin 2 → ZMod p) => ¬ (tt.1 0 * tt.2 1 - tt.1 1 * tt.2 0 ≠ 0)) := by
    simp
  have hfull : ∏ t, ∏ t', F t t' =
      (∏ tt ∈ Finset.univ.filter (fun tt : (Fin 2 → ZMod p) × (Fin 2 → ZMod p) =>
        tt.1 0 * tt.2 1 - tt.1 1 * tt.2 0 ≠ 0), F tt.1 tt.2) *
      (F 0 0 * ∏ tt ∈ (Finset.univ.filter (fun tt : (Fin 2 → ZMod p) × (Fin 2 → ZMod p) =>
        ¬ (tt.1 0 * tt.2 1 - tt.1 1 * tt.2 0 ≠ 0))).erase 0, F tt.1 tt.2) := by
    rw [← Fintype.prod_prod_type' F]
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun tt : (Fin 2 → ZMod p) × (Fin 2 → ZMod p) => tt.1 0 * tt.2 1 - tt.1 1 * tt.2 0 ≠ 0)]
    congr 1
    exact (Finset.mul_prod_erase _ (fun tt : (Fin 2 → ZMod p) × (Fin 2 → ZMod p) => F tt.1 tt.2) hmem).symm
  rw [Finset.prod_congr rfl (fun o _ => hinner o), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_option, Fintype.card_fin, prod_dep p N hN F, hfull, pow_succ]
  simp only [mul_assoc, mul_comm, mul_left_comm]

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sPairs :
    UpperTheory.V.Z.Kato.Nb.SPairs := by
  intro Ω _ _ ε X p N M₀ _ _ hcop a x y
  have hN : (N : ZMod p) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 (Nat.Coprime.coprime_dvd_right (dvd_mul_right N M₀) hcop) h
  have htp0 : tp p M₀ 0 = 0 := by
    funext i
    simp [tp]
  have key := prod_pairs p N hN (fun t t' => a (up p M₀ x + tp p M₀ t) (up p M₀ y + tp p M₀ t'))
  unfold pushB pushL pushD
  rw [key, htp0, add_zero, add_zero]
  congr 1
  rw [prod_fib p M₀ x (Finset.univ.filter fun x' => dn p M₀ x' = (p : ZMod M₀) • x) (by simp)
    (fun x' => ∏ y' ∈ Finset.univ.filter (fun y' => dn p M₀ y' = (p : ZMod M₀) • y), a x' y')]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  have hy := prod_fib p M₀ y (Finset.univ.filter fun y' => dn p M₀ y' = (p : ZMod M₀) • y)
    (fun z => by simp) (a (up p M₀ x + tp p M₀ t))
  exact hy.symm
