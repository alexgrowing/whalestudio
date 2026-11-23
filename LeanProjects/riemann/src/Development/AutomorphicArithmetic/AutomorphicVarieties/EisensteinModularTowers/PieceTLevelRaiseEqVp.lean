import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinPieceUnitSetLevelSuccEqStatement
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinCongrOfModEq
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.pieceT_level_raise_eq_vp :
    ∀ {K : Type} [Field K] [CharZero K] (l : ℕ) [Fact l.Prime] (N m k : ℕ) (c d : ℤ) (z₀ : ZMod (l ^ m)), 0 < N → ¬ l ∣ N → 1 ≤ m → 3 ≤ k → ¬ (l : ℤ) ∣ c → ¬ (l : ℤ) ∣ d → ∀ (n : ℕ) (ζ : K) (v v' u u' : ℤ × ℤ), IsPrimitiveRoot ζ (N * l ^ (m + n)) → (l : ℤ) ^ n * v.1 ≡ u.1 [ZMOD N] → (l : ℤ) ^ n * v.2 ≡ u.2 [ZMOD N] → (l : ℤ) ^ n * v'.1 ≡ u'.1 [ZMOD N] → (l : ℤ) ^ n * v'.2 ≡ u'.2 [ZMOD N] → ∀ r : ℕ, pieceT N l (m + n) m k (1 : DirichletCharacter K (l ^ m)) c d v v' ζ ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = z₀) r = vp (l ^ n) (pieceT N l m m k (1 : DirichletCharacter K (l ^ m)) c d u u' (ζ ^ (l ^ n)) ((unitSet l m).filter fun γ : GL (Fin 2) (ZMod (l ^ m)) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det.val : ℕ) : ZMod (l ^ m)) = z₀)) r := by
  intro K _ _ l hl N m k c d z₀ hN hlN hm hk hc hd n
  have cop : IsCoprime (l : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hlN)
  induction n with
  | zero =>
    intro ζ v v' u u' hζ h1 h2 h3 h4 r
    simp only [pow_zero, one_mul, pow_one, Nat.add_zero] at *
    have hv : ∀ f : ℕ → K, vp 1 f r = f r := fun f => by simp [vp]
    rw [hv]
    unfold pieceT
    congr 1
    refine Finset.sum_congr rfl fun γ _ => ?_
    congr 1
    have M0 : 0 < N * l ^ m := Nat.mul_pos hN (pow_pos hl.out.pos _)
    have key : ∀ (a : ℤ) {s t : ℤ}, s ≡ t [ZMOD N] → a + (l : ℤ) ^ m * s ≡ a + (l : ℤ) ^ m * t [ZMOD ((N * l ^ m : ℕ) : ℤ)] := by
      intro a s t h
      refine Int.ModEq.add_left _ ?_
      have := h.mul_left' (c := (l : ℤ) ^ m)
      push_cast
      rwa [mul_comm (N : ℤ)]
    congr 1
    · exact UpperTheory.smoothedEisenstein_congr_of_modEq _ _ _ _ M0 hζ.pow_eq_one (key _ h1) (key _ h2)
    · exact UpperTheory.smoothedEisenstein_congr_of_modEq _ _ _ _ M0 hζ.pow_eq_one (key _ h3) (key _ h4)
  | succ n ih =>
    intro ζ v v' u u' hζ h1 h2 h3 h4 r
    have hX := GlobalTheory.T.eisensteinPiece_unitSet_level_succ_eq l N (m + n) m k K (1 : DirichletCharacter K (l ^ m)) c d ((l : ℤ) * v.1, (l : ℤ) * v.2) ((l : ℤ) * v'.1, (l : ℤ) * v'.2) v v' ζ
      ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = z₀)
      hζ hN hlN hm (Nat.le_add_right m n) hk hc hd rfl rfl rfl rfl (fun γ hγ => by
        simpa [unitSet] using (Finset.mem_filter.1 hγ).1) r
    have hζ' : IsPrimitiveRoot (ζ ^ l) (N * l ^ (m + n)) :=
      hζ.pow (Nat.mul_pos hN (pow_pos hl.out.pos _)) (by rw [← Nat.add_assoc, pow_succ]; ring)
    have e : ∀ {s t : ℤ}, (l : ℤ) ^ (n + 1) * s ≡ t [ZMOD N] → (l : ℤ) ^ n * ((l : ℤ) * s) ≡ t [ZMOD N] := fun h => by
      rwa [pow_succ, mul_assoc] at h
    have hI := funext (ih (ζ ^ l) ((l : ℤ) * v.1, (l : ℤ) * v.2) ((l : ℤ) * v'.1, (l : ℤ) * v'.2) u u' hζ' (e h1) (e h2) (e h3) (e h4))
    rw [hI] at hX
    have hval : ∀ (j : ℕ) (hj : l ^ j ∣ l ^ (m + n)) (a : ZMod (l ^ (m + n + 1))),
        (((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (m + n))) (ZMod (l ^ (m + n))) a).val : ℕ) : ZMod (l ^ j)) = ((a.val : ℕ) : ZMod (l ^ j)) := by
      intro j hj a
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, ZMod.natCast_eq_natCast_iff]
      exact (Nat.mod_modEq _ _).of_dvd hj
    have hdv : ∀ a : ZMod (l ^ (m + n + 1)),
        l ∣ (ZMod.castHom (pow_dvd_pow l (Nat.le_succ (m + n))) (ZMod (l ^ (m + n))) a).val ↔ l ∣ a.val := by
      intro a
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
      exact Nat.dvd_mod_iff (dvd_pow_self l (by omega))
    refine Eq.trans ?_ (hX.trans ?_)
    · congr 1
      ext γ
      simp only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have d1 : ((Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ (m + n))) (ZMod (l ^ (m + n)))) γ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))) = (ZMod.castHom (pow_dvd_pow l (Nat.le_succ (m + n))) (ZMod (l ^ (m + n)))).mapMatrix (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n + 1)))) := rfl
      rw [d1, ← RingHom.map_det, hval m (pow_dvd_pow l (Nat.le_add_right m n))]
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hdv]
    · rw [← pow_mul, ← pow_succ']
      simp only [vp]
      by_cases h : l ∣ r
      · obtain ⟨r', rfl⟩ := h
        have : l ^ (n + 1) ∣ l * r' ↔ l ^ n ∣ r' := by rw [pow_succ', Nat.mul_dvd_mul_iff_left hl.out.pos]
        rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hl.out.pos]
        simp only [this]
        rw [pow_succ' l n, Nat.mul_div_mul_left _ _ hl.out.pos]
      · rw [if_neg h, if_neg (fun h' => h ((dvd_pow_self l (Nat.succ_ne_zero n)).trans h'))]
