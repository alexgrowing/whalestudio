import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ColOKOfPath

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section Nom

variable {r K : ℕ}

def NmH (c : ℤ) (h : ℕ) (J : Finset (Fin (r + K))) : Prop :=
  (1 ≤ c → J.card = h ∧ (r ≤ h → ∀ a : Fin (r + K), a.val < r → a ∈ J) ∧ (h ≤ r → ∀ a ∈ J, a.val < r)) ∧
  (¬ 1 ≤ c → ∀ a ∈ J, r ≤ a.val)

lemma NmH_wedge_pos {c : ℤ} (hc : 1 ≤ c) {hP hN : ℕ} (hN' : hN = hP + 1) {J : Finset (Fin (r + K))} {m : Fin (r + K)}
    (hm : m ∈ J) (hmr : r ≤ m.val ↔ r ≤ hP) (H : NmH c hP (J.erase m)) : NmH c hN J := by
  classical
  obtain ⟨hcard, hA, hB⟩ := H.1 hc
  have hcJ : J.card = hN := by
    rw [Finset.card_erase_of_mem hm] at hcard
    have := Finset.card_pos.mpr ⟨m, hm⟩; omega
  have hsub : hP < r → ∀ a ∈ J, a.val < r := by
    intro hlt a ha
    by_cases ham : a = m
    · subst ham; by_contra hh; have := hmr.mp (by omega); omega
    · exact hB (by omega) a (Finset.mem_erase.mpr ⟨ham, ha⟩)
  refine ⟨fun _ => ⟨hcJ, fun hr a ha => ?_, fun hr => hsub (by omega)⟩, fun hc' => absurd hc hc'⟩
  by_cases hr' : r ≤ hP
  · exact Finset.mem_of_mem_erase (hA hr' a ha)
  · have hs := hsub (by omega)
    have : J = univ.filter fun a : Fin (r + K) => a.val < r := by
      refine Finset.eq_of_subset_of_card_le (fun a ha => by simpa using hs a ha) ?_
      rw [plane_card]; omega
    rw [this]; simpa using ha

lemma NmH_contr_pos {c : ℤ} (hc : 1 ≤ c) {hP hN : ℕ} (hP' : hP = hN + 1) {J : Finset (Fin (r + K))} {m : Fin (r + K)}
    (hm : m ∉ J) (hmr : m.val < r ↔ hP ≤ r) (H : NmH c hP (insert m J)) : NmH c hN J := by
  classical
  obtain ⟨hcard, hA, hB⟩ := H.1 hc
  have hcJ : J.card = hN := by
    rw [Finset.card_insert_of_notMem hm] at hcard; omega
  have hsup : r < hP → ∀ a : Fin (r + K), a.val < r → a ∈ J := by
    intro hlt a ha
    have := hA (by omega) a ha
    rcases Finset.mem_insert.mp this with e | e
    · subst e; have := hmr.mp ha; omega
    · exact e
  refine ⟨fun _ => ⟨hcJ, fun hr => hsup (by omega), fun hr a ha => ?_⟩, fun hc' => absurd hc hc'⟩
  by_cases hr' : hP ≤ r
  · exact hB hr' a (Finset.mem_insert_of_mem ha)
  · have hs := hsup (by omega)
    have : (univ.filter fun a : Fin (r + K) => a.val < r) = J := by
      refine Finset.eq_of_subset_of_card_le (fun a ha => hs a (by simpa using ha)) ?_
      rw [plane_card]; omega
    rw [← this] at ha; simpa using ha

lemma NmH_wedge_neg {c : ℤ} (hc : ¬ 1 ≤ c) {hP hN : ℕ} {J : Finset (Fin (r + K))} {m : Fin (r + K)}
    (hmr : r ≤ m.val) (H : NmH c hP (J.erase m)) : NmH c hN J := by
  classical
  refine ⟨fun hc' => absurd hc' hc, fun _ a ha => ?_⟩
  by_cases ham : a = m
  · subst ham; exact hmr
  · exact H.2 hc a (Finset.mem_erase.mpr ⟨ham, ha⟩)

lemma NmH_contr_neg {c : ℤ} (hc : ¬ 1 ≤ c) {hP hN : ℕ} {J : Finset (Fin (r + K))} {m : Fin (r + K)}
    (H : NmH c hP (insert m J)) : NmH c hN J :=
  ⟨fun hc' => absurd hc' hc, fun _ a ha => H.2 hc a (Finset.mem_insert_of_mem ha)⟩

end Nom

section Dvd

variable {A : Type*} [CommRing A] {k : ℕ}

lemma colStep_dvd (D : A) (c : ℤ) (hP hN : ℕ) (hne : hP ≠ hN) (y : Fin k → A) (V : Finset (Fin k) → A)
    (J : Finset (Fin k))
    (H : ∀ m, (((hP < hN ∧ 1 ≤ c) ∨ (hN < hP ∧ ¬ 1 ≤ c)) → m ∈ J → D ∣ y m * V (J.erase m)) ∧
        (((hP < hN ∧ ¬ 1 ≤ c) ∨ (hN < hP ∧ 1 ≤ c)) → m ∉ J → D ∣ y m * V (insert m J))) :
    D ∣ colStep c hP hN y V J := by
  unfold colStep wedgeR contrR
  split_ifs with h1 h2 h3 h4
  · exact Finset.dvd_sum fun m hm => by
      rw [mul_assoc]; exact Dvd.dvd.mul_left ((H m).1 (Or.inl ⟨h1, h2⟩) hm) _
  · exact Finset.dvd_sum fun m hm => by
      rw [mul_assoc]; exact Dvd.dvd.mul_left ((H m).2 (Or.inl ⟨h1, h2⟩) (by simpa using hm)) _
  · exact Finset.dvd_sum fun m hm => by
      rw [mul_assoc]; exact Dvd.dvd.mul_left ((H m).2 (Or.inr ⟨h3, h4⟩) (by simpa using hm)) _
  · exact Finset.dvd_sum fun m hm => by
      rw [mul_assoc]; exact Dvd.dvd.mul_left ((H m).1 (Or.inr ⟨h3, h4⟩) hm) _
  · omega

end Dvd

section StepNom

variable {N r K : ℕ}

lemma step_nom (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (H : ColOK LL mu c)
    (j : ℕ) (h : j < N) (m : Fin (r + K)) (hnom : condUS LL ⟨j, h⟩ m ↔ IsCostly mu c ⟨j, h⟩)
    (J : Finset (Fin (r + K))) :
    (((colH (mu ⟨j, by omega⟩) c < colH (mu ⟨j + 1, by omega⟩) c ∧ 1 ≤ c) ∨
        (colH (mu ⟨j + 1, by omega⟩) c < colH (mu ⟨j, by omega⟩) c ∧ ¬ 1 ≤ c)) → m ∈ J →
      NmH c (colH (mu ⟨j, by omega⟩) c) (J.erase m) → NmH c (colH (mu ⟨j + 1, by omega⟩) c) J) ∧
    (((colH (mu ⟨j, by omega⟩) c < colH (mu ⟨j + 1, by omega⟩) c ∧ ¬ 1 ≤ c) ∨
        (colH (mu ⟨j + 1, by omega⟩) c < colH (mu ⟨j, by omega⟩) c ∧ 1 ≤ c)) → m ∉ J →
      NmH c (colH (mu ⟨j, by omega⟩) c) (insert m J) → NmH c (colH (mu ⟨j + 1, by omega⟩) c) J) := by
  rw [costly_iff] at hnom
  unfold condUS at hnom
  refine ⟨fun hw hm hN => ?_, fun hw hm hN => ?_⟩
  · rcases hw with ⟨h1, hc⟩ | ⟨h1, hc⟩
    · obtain ⟨hv, hN'⟩ := H.rise j h h1
      simp only [hv, true_and] at hnom
      refine NmH_wedge_pos hc hN' hm ⟨fun hh => ?_, fun hh => ?_⟩ hN
      · rcases hnom.mp (Or.inl hh) with ⟨_, x⟩ | ⟨x, _⟩ <;> omega
      · rcases hnom.mpr (Or.inl ⟨h1, hh⟩) with x | ⟨x, _⟩
        · exact x
        · exact absurd x (by simp)
    · obtain ⟨hv, _⟩ := H.fall j h h1
      have hd := H.dual hc j (by omega)
      refine NmH_wedge_neg hc ?_ hN
      by_contra hh
      rcases hnom.mp (Or.inr ⟨hv, by omega⟩) with ⟨x, _⟩ | ⟨_, x⟩ <;> omega
  · rcases hw with ⟨h1, hc⟩ | ⟨h1, hc⟩
    · exact NmH_contr_neg hc hN
    · obtain ⟨hv, hP'⟩ := H.fall j h h1
      simp only [hv, true_and] at hnom
      refine NmH_contr_pos hc hP' hm ⟨fun hh => ?_, fun hh => ?_⟩ hN
      · rcases hnom.mp (Or.inr hh) with ⟨x, _⟩ | ⟨_, x⟩ <;> omega
      · rcases hnom.mpr (Or.inr ⟨h1, hh⟩) with ⟨x, _⟩ | x
        · exact absurd x (by simp)
        · exact x

lemma step_van (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (H : ColOK LL mu c)
    (j : ℕ) (h : j < N) (hc : IsCostly mu c ⟨j, h⟩) (m : Fin (r + K)) (hm : ¬ condUS LL ⟨j, h⟩ m)
    (J : Finset (Fin (r + K))) :
    (((colH (mu ⟨j, by omega⟩) c < colH (mu ⟨j + 1, by omega⟩) c ∧ 1 ≤ c) ∨
        (colH (mu ⟨j + 1, by omega⟩) c < colH (mu ⟨j, by omega⟩) c ∧ ¬ 1 ≤ c)) → m ∈ J →
      ¬ NmH c (colH (mu ⟨j, by omega⟩) c) (J.erase m)) ∧
    (((colH (mu ⟨j, by omega⟩) c < colH (mu ⟨j + 1, by omega⟩) c ∧ ¬ 1 ≤ c) ∨
        (colH (mu ⟨j + 1, by omega⟩) c < colH (mu ⟨j, by omega⟩) c ∧ 1 ≤ c)) → m ∉ J →
      ¬ NmH c (colH (mu ⟨j, by omega⟩) c) (insert m J)) := by
  rw [costly_iff] at hc
  unfold condUS at hm
  refine ⟨fun hw hmJ hs => ?_, fun hw hmJ hs => ?_⟩
  · rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨hv, _⟩ := H.rise j h h1
      have hmr : m.val < r := by by_contra hh; exact hm (Or.inl ⟨hv, by omega⟩)
      have hr : r ≤ colH (mu ⟨j, by omega⟩) c := by rcases hc with ⟨_, x⟩ | ⟨x, _⟩ <;> omega
      exact (Finset.notMem_erase m J) ((hs.1 h2).2.1 hr m hmr)
    · have := H.dual h2 j (by omega)
      rcases hc with ⟨x, _⟩ | ⟨_, x⟩ <;> omega
  · rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨hv, _⟩ := H.rise j h h1
      have hmr : m.val < r := by by_contra hh; exact hm (Or.inl ⟨hv, by omega⟩)
      have := hs.2 h2 m (Finset.mem_insert_self m J); omega
    · obtain ⟨hv, _⟩ := H.fall j h h1
      have hmr : ¬ m.val < r := fun hh => hm (Or.inr ⟨hv, hh⟩)
      have hr : colH (mu ⟨j, by omega⟩) c ≤ r := by rcases hc with ⟨x, _⟩ | ⟨_, x⟩ <;> omega
      exact hmr ((hs.1 h2).2.2 hr m (Finset.mem_insert_self m J))

end StepNom

section Main

variable {N r K : ℕ}

structure TS {A : Type} [CommRing A] (p : ℕ) (W : A) (c : ℤ) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (pos : Fin N → ℤ)
    (ζ y : Fin N → Fin (r + K) → A) where
  T : ℤ → (Finset (Fin (r + K)) → A) → (Finset (Fin (r + K)) → A)
  step : ∀ (j : ℕ) (h : j < N) (Kv : Finset (Fin (r + K)) → A),
    T (pos ⟨j, h⟩) (colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (ζ ⟨j, h⟩) Kv) =
      colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (y ⟨j, h⟩) (T (pos ⟨j, h⟩) Kv)
  base : ∀ s J, J ≠ ∅ → T s extOne J = 0
  pw : ∀ (s s' : ℤ) (Kv : Finset (Fin (r + K)) → A) (o : ℕ), s ≤ s' → (∀ J, W ^ o ∣ T s Kv J) → ∀ J,
    W ^ (o * p ^ (s' - s).toNat) ∣ T s' (powC (p ^ (s' - s).toNat) Kv) J ∧
    (W ^ (o + 1) ∣ T s Kv J → W ^ (o * p ^ (s' - s).toNat + 1) ∣ T s' (powC (p ^ (s' - s).toNat) Kv) J ∧
      (s < s' → W ^ (o * p ^ (s' - s).toNat + 2) ∣ T s' (powC (p ^ (s' - s).toNat) Kv) J))
  inv : ∀ (s : ℤ) (Kv : Finset (Fin (r + K)) → A) (o : ℕ), (∀ J, W ^ o ∣ T s Kv J) → ∀ J, W ^ o ∣ Kv J

theorem Ord_main (p : ℕ) (hp0 : p ≠ 0) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (w : O)
    (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (H : ColOK LL mu c)
    (hmono : Monotone LL.pos)
    (hposc : ∀ i j : Fin N, i < j → IsUsed mu c i → IsCostly mu c j → LL.pos i < LL.pos j)
    (ζ : Fin N → Fin (r + K) → MvPolynomial (Fin N × Fin (r + K)) O)
    (ts : TS p (C w) c mu LL.pos ζ (yO w LL)) (j : ℕ) (hj : j ≤ N) :
    ∀ s : ℤ, (∀ i : Fin N, i.val < j → IsUsed mu c i → LL.pos i ≤ s) → ∀ J,
      C w ^ oS p LL.pos mu c j s ∣ ts.T s (ZZ p ζ LL.pos mu c j s) J ∧
      (¬ NmH c (colH (mu ⟨j, by omega⟩) c) J →
        C w ^ (oS p LL.pos mu c j s + 1) ∣ ts.T s (ZZ p ζ LL.pos mu c j s) J) := by
  induction j with
  | zero =>
    intro s _ J
    rw [ZZ_zero, oS_zero]
    refine ⟨by simp, fun hn => ?_⟩
    have hJ : J ≠ ∅ := by
      rintro rfl
      apply hn
      refine ⟨fun hc => ⟨by rw [H.start hc]; simp, fun hr a ha => ?_, by simp⟩, by simp⟩
      rw [H.start hc] at hr; omega
    rw [ts.base s J hJ]; exact dvd_zero _
  | succ j ih =>
    intro s hs J
    have h : j < N := hj
    have ih' := ih (by omega)
    by_cases hu : colH (mu ⟨j, by omega⟩) c = colH (mu ⟨j + 1, by omega⟩) c
    · have hnc : ¬ IsCostly mu c ⟨j, h⟩ := fun hc => costly_used mu c _ hc hu
      rw [ZZ_unused p _ _ mu c s j h hu, oS_succ p _ mu c s j h, if_neg hnc, add_zero, ← hu]
      exact ih' s (fun i hi => hs i (by omega)) J
    · set s0 := LL.pos ⟨j, h⟩ with hs0
      have hs0s : s0 ≤ s := hs ⟨j, h⟩ (by simp) hu
      have hprev : ∀ i : Fin N, i.val < j → IsUsed mu c i → LL.pos i ≤ s0 := fun i hi _ =>
        hmono (show i ≤ ⟨j, h⟩ from Fin.le_def.mpr (by simp; omega))
      have hWy : ∀ m : Fin (r + K), condUS LL ⟨j, h⟩ m → C w ∣ yO w LL ⟨j, h⟩ m := fun m hm => by
        rw [yO_cond _ _ _ _ hm]; exact Dvd.intro _ rfl
      have stepA : ∀ J, C w ^ oS p LL.pos mu c (j + 1) s0 ∣
            ts.T s0 (colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (ζ ⟨j, h⟩)
              (ZZ p ζ LL.pos mu c j s0)) J ∧
          (¬ NmH c (colH (mu ⟨j + 1, by omega⟩) c) J → C w ^ (oS p LL.pos mu c (j + 1) s0 + 1) ∣
            ts.T s0 (colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (ζ ⟨j, h⟩)
              (ZZ p ζ LL.pos mu c j s0)) J) := by
        intro J
        rw [hs0, ts.step j h, ← hs0, oS_succ p _ mu c s0 j h]
        by_cases hc : IsCostly mu c ⟨j, h⟩
        · have hs1 : ∀ i : Fin N, i.val < j → IsUsed mu c i → LL.pos i ≤ s0 - 1 := fun i hi hui => by
            have := hposc i ⟨j, h⟩ (Fin.lt_def.mpr (by simpa using hi)) hui hc
            omega
          have e1 : (s0 - (s0 - 1)).toNat = 1 := by omega
          have hpw := ts.pw (s0 - 1) s0 (ZZ p ζ LL.pos mu c j (s0 - 1)) (oS p LL.pos mu c j (s0 - 1)) (by omega)
            (fun J => (ih' (s0 - 1) hs1 J).1)
          rw [← ZZ_pow p hp0 _ _ mu c j (by omega) (s0 - 1) s0 (by omega) hs1,
            ← oS_pow p _ mu c j (s0 - 1) s0 (by omega) hs1] at hpw
          have d0 : ∀ J', C w ^ oS p LL.pos mu c j s0 ∣ ts.T s0 (ZZ p ζ LL.pos mu c j s0) J' :=
            fun J' => (hpw J').1
          have d2 : ∀ J', ¬ NmH c (colH (mu ⟨j, by omega⟩) c) J' →
              C w ^ (oS p LL.pos mu c j s0 + 2) ∣ ts.T s0 (ZZ p ζ LL.pos mu c j s0) J' :=
            fun J' hn => ((hpw J').2 ((ih' (s0 - 1) hs1 J').2 hn)).2 (by omega)
          rw [if_pos hc, ← hs0]
          simp only [sub_self, Int.toNat_zero, pow_zero]
          have tcond : ∀ m J', condUS LL ⟨j, h⟩ m → C w ^ (oS p LL.pos mu c j s0 + 1) ∣
              yO w LL ⟨j, h⟩ m * ts.T s0 (ZZ p ζ LL.pos mu c j s0) J' := fun m J' hm => by
            rw [pow_succ, mul_comm (C w ^ _)]; exact mul_dvd_mul (hWy m hm) (d0 J')
          refine ⟨colStep_dvd _ c _ _ hu _ _ J fun m => ?_, fun hn => colStep_dvd _ c _ _ hu _ _ J fun m => ?_⟩
          · by_cases hm : condUS LL ⟨j, h⟩ m
            · exact ⟨fun _ _ => tcond m _ hm, fun _ _ => tcond m _ hm⟩
            · have hv := step_van LL mu c H j h hc m hm J
              exact ⟨fun hw hmJ => Dvd.dvd.mul_left ((pow_dvd_pow _ (by omega)).trans (d2 _ (hv.1 hw hmJ))) _,
                fun hw hmJ => Dvd.dvd.mul_left ((pow_dvd_pow _ (by omega)).trans (d2 _ (hv.2 hw hmJ))) _⟩
          · by_cases hm : condUS LL ⟨j, h⟩ m
            · have hv := step_nom LL mu c H j h m (iff_of_true hm hc) J
              exact ⟨fun hw hmJ => Dvd.dvd.mul_left (d2 _ (fun hh => hn (hv.1 hw hmJ hh))) _,
                fun hw hmJ => Dvd.dvd.mul_left (d2 _ (fun hh => hn (hv.2 hw hmJ hh))) _⟩
            · have hv := step_van LL mu c H j h hc m hm J
              exact ⟨fun hw hmJ => Dvd.dvd.mul_left (d2 _ (hv.1 hw hmJ)) _,
                fun hw hmJ => Dvd.dvd.mul_left (d2 _ (hv.2 hw hmJ)) _⟩
        · have d0 := fun J' => (ih' s0 hprev J').1
          have d1 := fun J' => (ih' s0 hprev J').2
          rw [if_neg hc, add_zero]
          refine ⟨colStep_dvd _ c _ _ hu _ _ J fun m =>
            ⟨fun _ _ => Dvd.dvd.mul_left (d0 _) _, fun _ _ => Dvd.dvd.mul_left (d0 _) _⟩,
            fun hn => colStep_dvd _ c _ _ hu _ _ J fun m => ?_⟩
          by_cases hm : condUS LL ⟨j, h⟩ m
          · have tcond : ∀ J', C w ^ (oS p LL.pos mu c j s0 + 1) ∣
                yO w LL ⟨j, h⟩ m * ts.T s0 (ZZ p ζ LL.pos mu c j s0) J' := fun J' => by
              rw [pow_succ, mul_comm (C w ^ _)]; exact mul_dvd_mul (hWy m hm) (d0 J')
            exact ⟨fun _ _ => tcond _, fun _ _ => tcond _⟩
          · have hv := step_nom LL mu c H j h m (iff_of_false hm hc) J
            exact ⟨fun hw hmJ => Dvd.dvd.mul_left (d1 _ (fun hh => hn (hv.1 hw hmJ hh))) _,
              fun hw hmJ => Dvd.dvd.mul_left (d1 _ (fun hh => hn (hv.2 hw hmJ hh))) _⟩
      have hpw := ts.pw s0 s _ (oS p LL.pos mu c (j + 1) s0) hs0s (fun J => (stepA J).1) J
      have hle : ∀ i : Fin N, i.val < j + 1 → IsUsed mu c i → LL.pos i ≤ s0 := fun i hi _ =>
        hmono (show i ≤ ⟨j, h⟩ from Fin.le_def.mpr (by simp; omega))
      rw [ZZ_used p _ _ mu c s j h hu, ← hs0, oS_pow p _ mu c (j + 1) s0 s hs0s hle]
      exact ⟨hpw.1, fun hn => (hpw.2 ((stepA J).2 hn)).1⟩

end Main

end Formalism.MainNotions.LemmaBAlt
