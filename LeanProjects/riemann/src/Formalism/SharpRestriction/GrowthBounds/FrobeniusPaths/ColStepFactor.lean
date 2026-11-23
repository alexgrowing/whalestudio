import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ColumnKernelComponentsIntegral

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section Sym

variable {N r K : ℕ}

def condUS (LL : LiftLetters (Fin N)) (i : Fin N) (b : Fin (r + K)) : Prop :=
  (LL.vec i = true ∧ r ≤ b.val) ∨ (LL.vec i = false ∧ b.val < r)

open Classical in

def nomL (R : Type) [CommRing R] (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (i : Fin N) :
    Fin (r + K) → MvPolynomial (Fin N × Fin (r + K)) R :=
  fun b => if (condUS LL i b ↔ IsCostly mu c i) then X (i, b) else 0

def SgW (R : Type) [CommRing R] (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) :
    ℕ → Finset (Fin (r + K)) → MvPolynomial (Fin N × Fin (r + K)) R
  | 0 => extOne
  | j + 1 =>
    if h : j < N then
      colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (nomL R LL mu c ⟨j, h⟩) (SgW R LL mu c j)
    else SgW R LL mu c j

open Classical in

def oS (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (j : ℕ) (s : ℤ) : ℕ :=
  ∑ i : Fin N, if i.val < j ∧ IsCostly mu c i then p ^ (s - pos i).toNat else 0

lemma oS_zero (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (s : ℤ) :
    oS p pos mu c 0 s = 0 := by simp [oS]

open Classical in
lemma oS_succ (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (s : ℤ) (j : ℕ) (h : j < N) :
    oS p pos mu c (j + 1) s = oS p pos mu c j s +
      (if IsCostly mu c ⟨j, h⟩ then p ^ (s - pos ⟨j, h⟩).toNat else 0) := by
  unfold oS
  have key : ∀ i : Fin N, (if i.val < j + 1 ∧ IsCostly mu c i then p ^ (s - pos i).toNat else 0) =
      (if i.val < j ∧ IsCostly mu c i then p ^ (s - pos i).toNat else 0) +
      (if i = ⟨j, h⟩ then (if IsCostly mu c ⟨j, h⟩ then p ^ (s - pos ⟨j, h⟩).toNat else 0) else 0) := by
    intro i
    by_cases hi : i = ⟨j, h⟩
    · subst hi; simp
    · have hne : i.val ≠ j := fun e => hi (Fin.ext e)
      have e1 : (i.val < j + 1) ↔ (i.val < j) := by omega
      simp [hi, e1]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma oS_pow (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (j : ℕ) (s s' : ℤ)
    (hs : s ≤ s') (hpos : ∀ i : Fin N, i.val < j → IsUsed mu c i → pos i ≤ s) :
    oS p pos mu c j s' = oS p pos mu c j s * p ^ (s' - s).toNat := by
  classical
  unfold oS
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · have := hpos i hi.1 (costly_used mu c i hi.2)
    rw [← pow_add]; congr 1; omega
  · simp

lemma oS_top (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (z : ℤ) :
    oS p pos mu c N z = oc (fun i => p ^ (z - pos i).toNat) mu c := by
  classical
  unfold oS oc
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [i.isLt]

lemma SgW_supported (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (j : ℕ) :
    ∀ J, SgW ℤ LL mu c j J ∈ supported ℤ {v : Fin N × Fin (r + K) | v.1.val < j ∧ IsUsed mu c v.1} := by
  induction j with
  | zero =>
    intro J; simp only [SgW]; unfold extOne; split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  | succ j ih =>
    intro J
    have mono : supported ℤ {v : Fin N × Fin (r + K) | v.1.val < j ∧ IsUsed mu c v.1} ≤
        supported ℤ {v : Fin N × Fin (r + K) | v.1.val < j + 1 ∧ IsUsed mu c v.1} :=
      supported_mono fun v hv => ⟨by have := hv.1; omega, hv.2⟩
    simp only [SgW]
    split_ifs with h
    · by_cases hu : colH (mu ⟨j, by omega⟩) c = colH (mu ⟨j + 1, by omega⟩) c
      · have : colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (nomL ℤ LL mu c ⟨j, h⟩)
            (SgW ℤ LL mu c j) = SgW ℤ LL mu c j := by
          unfold colStep; rw [hu]; simp
        rw [this]; exact mono (ih J)
      · refine colStep_mem _ _ _ _ _ _ (fun b => ?_) (fun J => mono (ih J)) J
        unfold nomL; split_ifs
        · exact X_mem_supported.mpr ⟨by simp, hu⟩
        · exact Subalgebra.zero_mem _
    · exact mono (ih J)

end Sym

section Fac

variable {R R' : Type*} [CommRing R] [CommRing R'] {k : ℕ}

lemma sum_factor {ι' : Type*} (W : R) (π : R →+* R') (s : Finset ι') (e : ι' → ℕ) (a v : ι' → R) (a' v' : ι' → R')
    (H : ∀ m ∈ s, ∃ u, a m * v m = W * u ∧ π u = a' m * v' m) :
    ∃ Y, ∑ m ∈ s, (-1 : R) ^ e m * a m * v m = W * Y ∧ π Y = ∑ m ∈ s, (-1 : R') ^ e m * a' m * v' m := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | insert m s hm ih =>
    obtain ⟨Y, h1, h2⟩ := ih fun m' hm' => H m' (Finset.mem_insert_of_mem hm')
    obtain ⟨u, h3, h4⟩ := H m (Finset.mem_insert_self m s)
    refine ⟨(-1) ^ e m * u + Y, ?_, ?_⟩
    · rw [Finset.sum_insert hm, h1, mul_assoc, h3]; ring
    · rw [Finset.sum_insert hm, ← h2, map_add, map_mul, h4, map_pow, map_neg, map_one]; ring

lemma colStep_factor (W : R) (π : R →+* R') (c : ℤ) (hP hN : ℕ) (hne : hP ≠ hN) (y : Fin k → R)
    (V : Finset (Fin k) → R) (n' : Fin k → R') (S' : Finset (Fin k) → R')
    (H : ∀ m J, (((hP < hN ∧ 1 ≤ c) ∨ (hN < hP ∧ ¬ 1 ≤ c)) → m ∈ J →
          ∃ u, y m * V (J.erase m) = W * u ∧ π u = n' m * S' (J.erase m)) ∧
        (((hP < hN ∧ ¬ 1 ≤ c) ∨ (hN < hP ∧ 1 ≤ c)) → m ∉ J →
          ∃ u, y m * V (insert m J) = W * u ∧ π u = n' m * S' (insert m J))) (J : Finset (Fin k)) :
    ∃ Y, colStep c hP hN y V J = W * Y ∧ π Y = colStep c hP hN n' S' J := by
  unfold colStep
  split_ifs with h1 h2 h3 h4
  · exact sum_factor W π _ _ _ _ _ _ fun m hm => (H m J).1 (Or.inl ⟨h1, h2⟩) hm
  · exact sum_factor W π _ _ _ _ _ _ fun m hm => (H m J).2 (Or.inl ⟨h1, h2⟩) (by simpa using hm)
  · exact sum_factor W π _ _ _ _ _ _ fun m hm => (H m J).2 (Or.inr ⟨h3, h4⟩) (by simpa using hm)
  · exact sum_factor W π _ _ _ _ _ _ fun m hm => (H m J).1 (Or.inr ⟨h3, h4⟩) hm
  · omega

end Fac

section Ana

variable (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r K : ℕ}

lemma piR_ker {σ : Type} (S : UniformizedDVR p O) (Y : MvPolynomial σ O)
    (h : MvPolynomial.map (IsLocalRing.residue O) Y = 0) : ∃ T, Y = C S.w * T := by
  have : C S.w ∣ Y := by
    rw [MvPolynomial.C_dvd_iff_dvd_coeff]
    intro m
    have h1 : IsLocalRing.residue O (Y.coeff m) = 0 := by rw [← coeff_map, h, coeff_zero]
    rw [IsLocalRing.residue_eq_zero_iff, S.w_irr.maximalIdeal_eq, Ideal.mem_span_singleton] at h1
    exact h1
  exact this

lemma piR_w {σ : Type} (S : UniformizedDVR p O) :
    MvPolynomial.map (IsLocalRing.residue O) (C S.w : MvPolynomial σ O) = 0 := by
  have : IsLocalRing.residue O S.w = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, S.w_irr.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self _
  rw [map_C, this, C_0]

def piS (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (pos : Fin N → ℤ) (s : ℤ) :
    MvPolynomial (Fin N × Fin (r + K)) ℤ →+* MvPolynomial (Fin N × Fin (r + K)) (FF O) :=
  eval₂Hom (Int.castRingHom _) (fun v => X v ^ p ^ (s - pos v.1).toNat)

lemma piS_frob [CharP (FF O) p] (pos : Fin N → ℤ) (s s' : ℤ) (hs : s ≤ s') (V : Set (Fin N × Fin (r + K)))
    (hV : ∀ v ∈ V, pos v.1 ≤ s) (f : MvPolynomial (Fin N × Fin (r + K)) ℤ) (hf : f ∈ supported ℤ V) :
    (piS p O pos s f) ^ (p ^ (s' - s).toNat) = piS p O pos s' f := by
  have key : ((iterateFrobenius (MvPolynomial (Fin N × Fin (r + K)) (FF O)) p (s' - s).toNat).comp (piS p O pos s)) f =
      piS p O pos s' f := by
    refine MvPolynomial.hom_congr_vars (RingHom.ext_int _ _) (fun v hv _ => ?_) rfl
    have hv' := hV v ((mem_supported.mp hf) hv)
    simp only [RingHom.comp_apply, iterateFrobenius_def, piS, eval₂Hom_X']
    rw [← pow_mul, ← pow_add]; congr 2; omega
  simpa [iterateFrobenius_def] using key

def yO (w : O) (LL : LiftLetters (Fin N)) (i : Fin N) (b : Fin (r + K)) : MvPolynomial (Fin N × Fin (r + K)) O :=
  C (dW O w LL r i b) * X (i, b)

lemma yO_cond (w : O) (LL : LiftLetters (Fin N)) (i : Fin N) (b : Fin (r + K)) (h : condUS LL i b) :
    yO w LL i b = C w * X (i, b) := by
  unfold condUS at h; unfold yO dW; rw [if_pos h]

lemma yO_ncond (w : O) (LL : LiftLetters (Fin N)) (i : Fin N) (b : Fin (r + K)) (h : ¬ condUS LL i b) :
    yO w LL i b = X (i, b) := by
  unfold condUS at h; unfold yO dW; rw [if_neg h]; simp

def SgVanish (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) : Prop :=
  ∀ (j : ℕ) (h : j < N), IsCostly mu c ⟨j, h⟩ → ∀ m, ¬ condUS LL ⟨j, h⟩ m → ∀ J : Finset (Fin (r + K)),
    (((colH (mu ⟨j, by omega⟩) c < colH (mu ⟨j + 1, by omega⟩) c ∧ 1 ≤ c) ∨
        (colH (mu ⟨j + 1, by omega⟩) c < colH (mu ⟨j, by omega⟩) c ∧ ¬ 1 ≤ c)) → m ∈ J →
      SgW ℤ LL mu c j (J.erase m) = 0) ∧
    (((colH (mu ⟨j, by omega⟩) c < colH (mu ⟨j + 1, by omega⟩) c ∧ ¬ 1 ≤ c) ∨
        (colH (mu ⟨j + 1, by omega⟩) c < colH (mu ⟨j, by omega⟩) c ∧ 1 ≤ c)) → m ∉ J →
      SgW ℤ LL mu c j (insert m J) = 0)

theorem Inv_main [CharP (FF O) p] (S : UniformizedDVR p O) (LL : LiftLetters (Fin N))
    (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (hmono : Monotone LL.pos)
    (hposc : ∀ i j : Fin N, i < j → IsUsed mu c i → IsCostly mu c j → LL.pos i < LL.pos j)
    (HV : SgVanish LL mu c) (j : ℕ) (hj : j ≤ N) :
    ∀ s : ℤ, (∀ i : Fin N, i.val < j → IsUsed mu c i → LL.pos i ≤ s) → ∀ J, ∃ Y : MvPolynomial (Fin N × Fin (r + K)) O,
      ZZ p (yO S.w LL) LL.pos mu c j s J = C S.w ^ oS p LL.pos mu c j s * Y ∧
      MvPolynomial.map (IsLocalRing.residue O) Y = piS p O LL.pos s (SgW ℤ LL mu c j J) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  induction j with
  | zero =>
    intro s _ J
    refine ⟨extOne J, by rw [ZZ_zero, oS_zero]; simp, ?_⟩
    simp only [SgW]
    rw [extOne_map, extOne_map]
  | succ j ih =>
    intro s hs J
    have h : j < N := hj
    have ih' := ih (by omega)
    by_cases hu : colH (mu ⟨j, by omega⟩) c = colH (mu ⟨j + 1, by omega⟩) c
    · have hnc : ¬ IsCostly mu c ⟨j, h⟩ := fun hc => costly_used mu c _ hc hu
      obtain ⟨Y, h1, h2⟩ := ih' s (fun i hi => hs i (by omega)) J
      refine ⟨Y, ?_, ?_⟩
      · rw [ZZ_unused p _ _ mu c s j h hu, oS_succ p _ mu c s j h, if_neg hnc, add_zero]; exact h1
      · rw [h2]; simp only [SgW, dif_pos h]
        congr 1
        unfold colStep; rw [hu]; simp
    · set s0 := LL.pos ⟨j, h⟩ with hs0
      have hs0s : s0 ≤ s := hs ⟨j, h⟩ (by simp) hu
      have hprev : ∀ i : Fin N, i.val < j → IsUsed mu c i → LL.pos i ≤ s0 := fun i hi _ =>
        hmono (show i ≤ ⟨j, h⟩ from Fin.le_def.mpr (by simp; omega))

      have stepA : ∀ J, ∃ Y : MvPolynomial (Fin N × Fin (r + K)) O,
          colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (yO S.w LL ⟨j, h⟩)
            (ZZ p (yO S.w LL) LL.pos mu c j s0) J = C S.w ^ oS p LL.pos mu c (j + 1) s0 * Y ∧
          MvPolynomial.map (IsLocalRing.residue O) Y = piS p O LL.pos s0 (SgW ℤ LL mu c (j + 1) J) := by
        intro J
        have eS : piS p O LL.pos s0 (SgW ℤ LL mu c (j + 1) J) =
            colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c)
              (fun b => piS p O LL.pos s0 (nomL ℤ LL mu c ⟨j, h⟩ b))
              (fun J => piS p O LL.pos s0 (SgW ℤ LL mu c j J)) J := by
          simp only [SgW, dif_pos h, colStep_map]
        have eX : ∀ b : Fin (r + K), piS p O LL.pos s0 (X (⟨j, h⟩, b)) = X (⟨j, h⟩, b) := by
          intro b; simp [piS, hs0]
        rw [eS]
        by_cases hc : IsCostly mu c ⟨j, h⟩
        ·
          have hs1 : ∀ i : Fin N, i.val < j → IsUsed mu c i → LL.pos i ≤ s0 - 1 := fun i hi hui => by
            have := hposc i ⟨j, h⟩ (Fin.lt_def.mpr (by simpa using hi)) hui hc
            omega
          choose Y1 hY1 hY2 using ih' (s0 - 1) hs1
          have e1 : (s0 - (s0 - 1)).toNat = 1 := by omega
          have eZ : ZZ p (yO S.w LL) LL.pos mu c j s0 =
              fun J => C S.w ^ oS p LL.pos mu c j s0 * (Y1 J) ^ p := by
            rw [ZZ_pow p hp0 _ _ mu c j (by omega) (s0 - 1) s0 (by omega) hs1,
              oS_pow p _ mu c j (s0 - 1) s0 (by omega) hs1, e1, pow_one]
            funext J; simp only [powC]; rw [hY1, mul_pow, ← pow_mul]
          have eV : ∀ J, MvPolynomial.map (IsLocalRing.residue O) ((Y1 J) ^ p) =
              piS p O LL.pos s0 (SgW ℤ LL mu c j J) := by
            intro J
            rw [map_pow, hY2, ← piS_frob p LL.pos (s0 - 1) s0 (by omega) _ (fun v hv => hs1 v.1 hv.1 hv.2) _
              (SgW_supported LL mu c j J), e1, pow_one]
          have pair : ∀ m J', (condUS LL ⟨j, h⟩ m ∨ SgW ℤ LL mu c j J' = 0) →
              ∃ u, yO S.w LL ⟨j, h⟩ m * (Y1 J') ^ p = C S.w * u ∧
                MvPolynomial.map (IsLocalRing.residue O) u =
                  piS p O LL.pos s0 (nomL ℤ LL mu c ⟨j, h⟩ m) * piS p O LL.pos s0 (SgW ℤ LL mu c j J') := by
            intro m J' hm
            by_cases hcm : condUS LL ⟨j, h⟩ m
            · refine ⟨X (⟨j, h⟩, m) * (Y1 J') ^ p, by rw [yO_cond _ _ _ _ hcm]; ring, ?_⟩
              rw [map_mul, eV, map_X]
              have : nomL ℤ LL mu c ⟨j, h⟩ m = X (⟨j, h⟩, m) := by
                unfold nomL; rw [if_pos (iff_of_true hcm hc)]
              rw [this, eX]
            · have hz : SgW ℤ LL mu c j J' = 0 := hm.resolve_left hcm
              obtain ⟨T, hT⟩ := piR_ker p S (Y1 J') (by rw [hY2, hz, map_zero])
              have hp1 : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
              refine ⟨X (⟨j, h⟩, m) * (C S.w ^ (p - 1) * T ^ p), ?_, ?_⟩
              · rw [yO_ncond _ _ _ _ hcm, hT, mul_pow]
                have e : (C S.w : MvPolynomial (Fin N × Fin (r + K)) O) ^ p = C S.w ^ (p - 1) * C S.w := by
                  rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
                rw [e]; ring
              · rw [map_mul, map_mul, map_pow, piR_w p S, zero_pow hp1, hz, map_zero]; simp
          obtain ⟨Y, hYa, hYb⟩ := colStep_factor (C S.w) (MvPolynomial.map (IsLocalRing.residue O)) c _ _ hu
            (yO S.w LL ⟨j, h⟩) (fun J => (Y1 J) ^ p) (fun b => piS p O LL.pos s0 (nomL ℤ LL mu c ⟨j, h⟩ b))
            (fun J => piS p O LL.pos s0 (SgW ℤ LL mu c j J))
            (fun m J => ⟨fun hw hmJ => pair m _ (by
                by_cases hcm : condUS LL ⟨j, h⟩ m
                · exact Or.inl hcm
                · exact Or.inr ((HV j h hc m hcm J).1 hw hmJ)),
              fun hw hmJ => pair m _ (by
                by_cases hcm : condUS LL ⟨j, h⟩ m
                · exact Or.inl hcm
                · exact Or.inr ((HV j h hc m hcm J).2 hw hmJ))⟩) J
          refine ⟨Y, ?_, hYb⟩
          rw [eZ, colStep_smul, hYa, oS_succ p _ mu c s0 j h, if_pos hc, ← hs0]
          simp only [sub_self, Int.toNat_zero, pow_zero]
          ring
        ·
          choose Y hY1 hY2 using ih' s0 hprev
          have eZ : ZZ p (yO S.w LL) LL.pos mu c j s0 = fun J => C S.w ^ oS p LL.pos mu c j s0 * Y J :=
            funext hY1
          refine ⟨colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (yO S.w LL ⟨j, h⟩) Y J, ?_, ?_⟩
          · rw [eZ, colStep_smul, oS_succ p _ mu c s0 j h, if_neg hc, add_zero]
          · rw [colStep_map]
            congr 1
            · funext b
              by_cases hcm : condUS LL ⟨j, h⟩ b
              · rw [yO_cond _ _ _ _ hcm, map_mul, piR_w p S, zero_mul]
                have : nomL ℤ LL mu c ⟨j, h⟩ b = 0 := by
                  unfold nomL; rw [if_neg (fun e => hc (e.mp hcm))]
                rw [this, map_zero]
              · rw [yO_ncond _ _ _ _ hcm, map_X]
                have : nomL ℤ LL mu c ⟨j, h⟩ b = X (⟨j, h⟩, b) := by
                  unfold nomL; rw [if_pos (iff_of_false hcm hc)]
                rw [this, eX]
            · funext J'; exact hY2 J'

      obtain ⟨Y, hYa, hYb⟩ := stepA J
      refine ⟨Y ^ (p ^ (s - s0).toNat), ?_, ?_⟩
      · rw [ZZ_used p _ _ mu c s j h hu]
        simp only [powC]
        rw [← hs0, hYa, mul_pow, ← pow_mul, oS_pow p _ mu c (j + 1) s0 s hs0s]
        intro i hi hui
        exact hmono (show i ≤ ⟨j, h⟩ from Fin.le_def.mpr (by simp; omega))
      · rw [map_pow, hYb]
        exact piS_frob p LL.pos s0 s hs0s _
          (fun v hv => hmono (show v.1 ≤ ⟨j, h⟩ from Fin.le_def.mpr (by have := hv.1; simp; omega))) _
          (SgW_supported LL mu c (j + 1) J)

end Ana

end Formalism.MainNotions.LemmaBAlt
