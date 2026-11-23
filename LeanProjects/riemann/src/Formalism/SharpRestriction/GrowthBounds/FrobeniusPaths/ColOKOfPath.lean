import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftedColumnCongruence

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section Strip

lemma colH_strip {n : ℕ} (nu mu' : Fin n → ℤ) (b : ℕ) (h : HStrip nu mu' b) (c : ℤ) :
    colH nu c ≤ colH mu' c ∧ colH mu' c ≤ colH nu c + 1 := by
  classical
  obtain ⟨h1, h2, _⟩ := h
  constructor
  · unfold colH
    refine Finset.card_le_card fun m hm => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    exact hm.trans (h1 m)
  · unfold colH
    set A := univ.filter fun m : Fin n => c ≤ mu' m with hA
    have e : A.card = (A.filter fun m => m.val = 0).card + (A.filter fun m => ¬ m.val = 0).card :=
      (Finset.card_filter_add_card_filter_not _).symm
    have e1 : (A.filter fun m => m.val = 0).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      exact Fin.ext (by omega)
    have e2 : (A.filter fun m => ¬ m.val = 0).card ≤ (univ.filter fun m : Fin n => c ≤ nu m).card := by
      refine Finset.card_le_card_of_injOn (fun m => ⟨m.val - 1, by have := m.isLt; omega⟩) ?_ ?_
      · intro m hm
        simp only [Finset.coe_filter, Finset.mem_filter, hA, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hm ⊢
        have hlt : (m.val - 1) + 1 < n := by have := m.isLt; omega
        have := h2 ⟨m.val - 1, by have := m.isLt; omega⟩ hlt
        have em : (⟨(m.val - 1) + 1, hlt⟩ : Fin n) = m := Fin.ext (by simp; omega)
        simp only [em] at this
        exact hm.1.trans this
      · intro a ha b hb hab
        simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_ofPred_eq] at ha hb
        simp only [Fin.mk.injEq] at hab
        exact Fin.ext (by omega)
    omega

end Strip

section Col

variable {N r K : ℕ}

structure ColOK (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) : Prop where
  rise : ∀ (j : ℕ) (h : j < N), colH (mu ⟨j, by omega⟩) c < colH (mu ⟨j + 1, by omega⟩) c →
    LL.vec ⟨j, h⟩ = true ∧ colH (mu ⟨j + 1, by omega⟩) c = colH (mu ⟨j, by omega⟩) c + 1
  fall : ∀ (j : ℕ) (h : j < N), colH (mu ⟨j + 1, by omega⟩) c < colH (mu ⟨j, by omega⟩) c →
    LL.vec ⟨j, h⟩ = false ∧ colH (mu ⟨j, by omega⟩) c = colH (mu ⟨j + 1, by omega⟩) c + 1
  start : 1 ≤ c → colH (mu ⟨0, by omega⟩) c = 0
  dual : ¬ 1 ≤ c → ∀ (j : ℕ) (h : j ≤ N), r < colH (mu ⟨j, by omega⟩) c

lemma colOK_of_path [NeZero r] (LL : LiftLetters (Fin N)) (B : Fin N → ℕ) (hK : N + r ≤ K)
    (P : PPath (r + K) N LL.toLetters B) (c : ℤ) : ColOK LL P.mu c := by
  have step : ∀ (j : ℕ) (h : j < N),
      (LL.vec ⟨j, h⟩ = true ∧ colH (P.mu ⟨j, by omega⟩) c ≤ colH (P.mu ⟨j + 1, by omega⟩) c ∧
        colH (P.mu ⟨j + 1, by omega⟩) c ≤ colH (P.mu ⟨j, by omega⟩) c + 1) ∨
      (LL.vec ⟨j, h⟩ = false ∧ colH (P.mu ⟨j + 1, by omega⟩) c ≤ colH (P.mu ⟨j, by omega⟩) c ∧
        colH (P.mu ⟨j, by omega⟩) c ≤ colH (P.mu ⟨j + 1, by omega⟩) c + 1) := by
    intro j h
    have hs := P.step ⟨j, h⟩
    by_cases hv : LL.vec ⟨j, h⟩ = true
    · rw [if_pos hv] at hs
      exact Or.inl ⟨hv, colH_strip _ _ _ hs c⟩
    · rw [if_neg hv] at hs
      exact Or.inr ⟨by simpa using hv, colH_strip _ _ _ hs c⟩
  have hz : P.mu ⟨0, by omega⟩ = 0 := P.zero
  refine ⟨fun j h hlt => ?_, fun j h hlt => ?_, fun hc => ?_, fun hc => ?_⟩
  · rcases step j h with ⟨hv, h1, h2⟩ | ⟨hv, h1, h2⟩
    · exact ⟨hv, by omega⟩
    · omega
  · rcases step j h with ⟨hv, h1, h2⟩ | ⟨hv, h1, h2⟩
    · omega
    · exact ⟨hv, by omega⟩
  · rw [hz]; unfold colH
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _; simp only [Pi.zero_apply]; omega
  · have h0 : colH (P.mu ⟨0, by omega⟩) c = r + K := by
      rw [hz]; unfold colH
      rw [Finset.filter_true_of_mem (fun m _ => by simp only [Pi.zero_apply]; omega)]
      simp
    have hind : ∀ (j : ℕ) (h : j ≤ N), r + K ≤ colH (P.mu ⟨j, by omega⟩) c + j := by
      intro j
      induction j with
      | zero => intro _; omega
      | succ j ih =>
        intro h
        have := ih (by omega)
        rcases step j h with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ <;> omega
    intro j h
    have := hind j h
    have := NeZero.pos r
    omega

lemma plane_card : (univ.filter fun a : Fin (r + K) => a.val < r).card = r := by
  classical
  rw [show (univ.filter fun a : Fin (r + K) => a.val < r) = (univ : Finset (Fin r)).image (Fin.castAdd K) from ?_,
    Finset.card_image_of_injective _ (Fin.castAdd_injective r K), Finset.card_fin]
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h; exact ⟨⟨a.val, h⟩, Fin.ext rfl⟩
  · rintro ⟨b, rfl⟩; exact b.isLt

lemma costly_iff (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (j : ℕ) (h : j < N) :
    IsCostly mu c ⟨j, h⟩ ↔
      (colH (mu ⟨j, by omega⟩) c < colH (mu ⟨j + 1, by omega⟩) c ∧ r ≤ colH (mu ⟨j, by omega⟩) c) ∨
      (colH (mu ⟨j + 1, by omega⟩) c < colH (mu ⟨j, by omega⟩) c ∧ colH (mu ⟨j, by omega⟩) c ≤ r) := Iff.rfl

lemma nomL_ne {R : Type} [CommRing R] (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ)
    (i : Fin N) (m : Fin (r + K)) (h : nomL R LL mu c i m ≠ 0) : condUS LL i m ↔ IsCostly mu c i := by
  classical
  by_contra hh
  exact h (by unfold nomL; rw [if_neg hh])

lemma wedgeR_ne {R : Type} [CommRing R] {k : ℕ} (x : Fin k → R) (Kv : Finset (Fin k) → R) (J : Finset (Fin k))
    (h : wedgeR x Kv J ≠ 0) : ∃ m ∈ J, x m ≠ 0 ∧ Kv (J.erase m) ≠ 0 := by
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨m, hm, fun e => hne (by rw [e]; simp), fun e => hne (by rw [e]; simp)⟩

lemma contrR_ne {R : Type} [CommRing R] {k : ℕ} (x : Fin k → R) (Kv : Finset (Fin k) → R) (J : Finset (Fin k))
    (h : contrR x Kv J ≠ 0) : ∃ m, m ∉ J ∧ x m ≠ 0 ∧ Kv (insert m J) ≠ 0 := by
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨m, by simpa using hm, fun e => hne (by rw [e]; simp), fun e => hne (by rw [e]; simp)⟩

lemma SgW_supp {R : Type} [CommRing R] (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ)
    (H : ColOK LL mu c) (j : ℕ) (hj : j ≤ N) :
    ∀ J, SgW R LL mu c j J ≠ 0 →
      (1 ≤ c → J.card = colH (mu ⟨j, by omega⟩) c ∧
        (r ≤ colH (mu ⟨j, by omega⟩) c → ∀ a : Fin (r + K), a.val < r → a ∈ J) ∧
        (colH (mu ⟨j, by omega⟩) c ≤ r → ∀ a ∈ J, a.val < r)) ∧
      (¬ 1 ≤ c → ∀ a ∈ J, r ≤ a.val) := by
  classical
  induction j with
  | zero =>
    intro J hJ
    have : J = ∅ := by
      by_contra hne; exact hJ (by simp only [SgW]; unfold extOne; rw [if_neg hne])
    subst this
    refine ⟨fun hc => ⟨by rw [H.start hc]; simp, fun hr a ha => ?_, by simp⟩, by simp⟩
    rw [H.start hc] at hr; omega
  | succ j ih =>
    intro J hJ
    have h : j < N := hj
    have ih' := ih (by omega)
    simp only [SgW, dif_pos h] at hJ
    unfold colStep at hJ
    have hci := costly_iff mu c j h
    split_ifs at hJ with h1 h2 h3 h4
    ·
      obtain ⟨hv, hN⟩ := H.rise j h h1
      obtain ⟨m, hm, hn, hK⟩ := wedgeR_ne _ _ _ hJ
      have hc := nomL_ne LL mu c _ m hn
      obtain ⟨hcard, hA, hB⟩ := (ih' _ hK).1 h2
      have hmr : r ≤ m.val ↔ r ≤ colH (mu ⟨j, by omega⟩) c := by
        rw [hci] at hc; unfold condUS at hc; simp only [hv, true_and] at hc
        constructor
        · intro hh; rcases hc.mp (Or.inl hh) with ⟨_, x⟩ | ⟨x, _⟩ <;> omega
        · intro hh; rcases hc.mpr (Or.inl ⟨h1, hh⟩) with x | ⟨x, _⟩
          · exact x
          · exact absurd x (by simp)
      have hcJ : J.card = colH (mu ⟨j + 1, by omega⟩) c := by
        rw [Finset.card_erase_of_mem hm] at hcard
        have := Finset.card_pos.mpr ⟨m, hm⟩; omega
      have hsub : colH (mu ⟨j, by omega⟩) c < r → ∀ a ∈ J, a.val < r := by
        intro hlt a ha
        by_cases ham : a = m
        · subst ham; by_contra hh; have := hmr.mp (by omega); omega
        · exact hB (by omega) a (Finset.mem_erase.mpr ⟨ham, ha⟩)
      refine ⟨fun _ => ⟨hcJ, fun hr a ha => ?_, fun hr => hsub (by omega)⟩, fun hc' => absurd h2 hc'⟩
      by_cases hr' : r ≤ colH (mu ⟨j, by omega⟩) c
      · exact Finset.mem_of_mem_erase (hA hr' a ha)
      · have hs := hsub (by omega)
        have : J = univ.filter fun a : Fin (r + K) => a.val < r := by
          refine Finset.eq_of_subset_of_card_le (fun a ha => by simpa using hs a ha) ?_
          rw [plane_card]; omega
        rw [this]; simpa using ha
    ·
      obtain ⟨hv, hN⟩ := H.rise j h h1
      obtain ⟨m, hm, hn, hK⟩ := contrR_ne _ _ _ hJ
      exact ⟨fun hc' => absurd hc' h2, fun _ a ha => (ih' _ hK).2 h2 a (Finset.mem_insert_of_mem ha)⟩
    ·
      obtain ⟨hv, hP⟩ := H.fall j h h3
      obtain ⟨m, hm, hn, hK⟩ := contrR_ne _ _ _ hJ
      have hc := nomL_ne LL mu c _ m hn
      obtain ⟨hcard, hA, hB⟩ := (ih' _ hK).1 h4
      have hmr : m.val < r ↔ colH (mu ⟨j, by omega⟩) c ≤ r := by
        rw [hci] at hc; unfold condUS at hc; simp only [hv, true_and] at hc
        constructor
        · intro hh; rcases hc.mp (Or.inr hh) with ⟨x, _⟩ | ⟨_, x⟩ <;> omega
        · intro hh; rcases hc.mpr (Or.inr ⟨h3, hh⟩) with ⟨x, _⟩ | x
          · exact absurd x (by simp)
          · exact x
      have hcJ : J.card = colH (mu ⟨j + 1, by omega⟩) c := by
        rw [Finset.card_insert_of_notMem hm] at hcard; omega
      have hsup : r < colH (mu ⟨j, by omega⟩) c → ∀ a : Fin (r + K), a.val < r → a ∈ J := by
        intro hlt a ha
        have := hA (by omega) a ha
        rcases Finset.mem_insert.mp this with e | e
        · subst e; have := hmr.mp ha; omega
        · exact e
      refine ⟨fun _ => ⟨hcJ, fun hr => hsup (by omega), fun hr a ha => ?_⟩, fun hc' => absurd h4 hc'⟩
      by_cases hr' : colH (mu ⟨j, by omega⟩) c ≤ r
      · exact hB hr' a (Finset.mem_insert_of_mem ha)
      · have hs := hsup (by omega)
        have : (univ.filter fun a : Fin (r + K) => a.val < r) = J := by
          refine Finset.eq_of_subset_of_card_le (fun a ha => hs a (by simpa using ha)) ?_
          rw [plane_card]; omega
        rw [← this] at ha; simpa using ha
    ·
      obtain ⟨hv, hP⟩ := H.fall j h h3
      obtain ⟨m, hm, hn, hK⟩ := wedgeR_ne _ _ _ hJ
      have hc := nomL_ne LL mu c _ m hn
      have hd := H.dual h4 j (by omega)
      refine ⟨fun hc' => absurd hc' h4, fun _ a ha => ?_⟩
      by_cases ham : a = m
      · subst ham
        by_contra hh
        rw [hci] at hc; unfold condUS at hc
        rcases hc.mp (Or.inr ⟨hv, by omega⟩) with ⟨x, _⟩ | ⟨_, x⟩ <;> omega
      · exact (ih' _ hK).2 h4 a (Finset.mem_erase.mpr ⟨ham, ha⟩)
    ·
      have e : colH (mu ⟨j + 1, by omega⟩) c = colH (mu ⟨j, by omega⟩) c := by omega
      rw [e]; exact ih' J hJ

lemma SgVanish_of (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ)
    (H : ColOK LL mu c) : SgVanish LL mu c := by
  intro j h hc m hm J
  rw [costly_iff] at hc
  unfold condUS at hm
  refine ⟨fun hw hmJ => ?_, fun hw hmJ => ?_⟩
  · by_contra hne
    have hs := SgW_supp LL mu c H j (by omega) _ hne
    rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨hv, _⟩ := H.rise j h h1
      have hmr : m.val < r := by by_contra hh; exact hm (Or.inl ⟨hv, by omega⟩)
      have hr : r ≤ colH (mu ⟨j, by omega⟩) c := by rcases hc with ⟨_, x⟩ | ⟨x, _⟩ <;> omega
      exact (Finset.notMem_erase m J) ((hs.1 h2).2.1 hr m hmr)
    · have := H.dual h2 j (by omega)
      rcases hc with ⟨x, _⟩ | ⟨_, x⟩ <;> omega
  · by_contra hne
    have hs := SgW_supp LL mu c H j (by omega) _ hne
    rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨hv, _⟩ := H.rise j h h1
      have hmr : m.val < r := by by_contra hh; exact hm (Or.inl ⟨hv, by omega⟩)
      have := hs.2 h2 m (Finset.mem_insert_self m J); omega
    · obtain ⟨hv, _⟩ := H.fall j h h1
      have hmr : ¬ m.val < r := fun hh => hm (Or.inr ⟨hv, hh⟩)
      have hr : colH (mu ⟨j, by omega⟩) c ≤ r := by rcases hc with ⟨x, _⟩ | ⟨_, x⟩ <;> omega
      exact hmr ((hs.1 h2).2.2 hr m (Finset.mem_insert_self m J))

end Col

end Formalism.MainNotions.LemmaBAlt
