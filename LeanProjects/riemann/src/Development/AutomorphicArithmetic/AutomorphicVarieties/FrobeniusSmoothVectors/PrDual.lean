import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem tri_zero {K G ι : Type} [Field K] [Fintype ι] [LinearOrder ι] (M : G → Matrix ι ι K) (ω : G → K)
    (Φ : Matrix ι ι K) (hM : ∀ g i j, j < i → M g i j = 0)
    (h : ∀ g i j, ∑ p, M g i p * Φ p j = ω g * ∑ q, Φ i q * M g q j)
    (key : ∀ i j, (∀ g, M g i i * Φ i j = ω g * (Φ i j * M g j j)) → Φ i j = 0) : ∀ i j, Φ i j = 0 := by
  intro i
  induction i using WellFoundedGT.induction with
  | _ i ih =>
  intro j
  induction j using WellFoundedLT.induction with
  | _ j ih' =>
  refine key i j fun g => ?_
  have := h g i j
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j] at this
  · exact this
  · intro q _ hq
    rcases lt_or_gt_of_ne hq with h1 | h1
    · rw [ih' q h1, zero_mul]
    · rw [hM g q j h1, mul_zero]
  · simp
  · intro p _ hp
    rcases lt_or_gt_of_ne hp with h1 | h1
    · rw [hM g i p h1, zero_mul]
    · rw [ih p h1 j, mul_zero]
  · simp

private theorem om_map {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (F : Frame l k) {K : Type} [Field K]
    [CharP K l] (φ : k →+* K) (g : F.Γ) : φ (F.om k g : k) = (F.om K g : K) := by
  have : φ.comp (ZMod.castHom (dvd_refl l) k) = ZMod.castHom (dvd_refl l) K := Subsingleton.elim _ _
  exact RingHom.congr_fun this _

private theorem w_cases {n : ℕ} (hn : n = 2 ∨ n = 3) (i j : Fin n) :
    w n j - w n i = 0 ∨ (w n j - w n i = 1 ∨ w n j - w n i = -1) ∨
      ((w n j - w n i = 2 ∨ w n j - w n i = -2) ∧ j = i.rev) := by
  rcases hn with rfl | rfl
  · revert i j; decide
  · revert i j; decide

private theorem thetaLie_single {K : Type} [Field K] {n : ℕ} (i : Fin n) :
    thetaLie (Matrix.single i i.rev (1 : K)) = -Matrix.single i i.rev (1 : K) := by
  unfold thetaLie
  congr 1
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single b.rev, Matrix.mul_apply, Finset.sum_eq_single a.rev]
  · simp only [Jmat, Matrix.transpose_apply, Matrix.single_apply, Fin.rev_rev, if_true, one_mul, mul_one,
      Fin.rev_inj]
    congr 1
    refine propext ⟨?_, ?_⟩
    · rintro ⟨rfl, rfl⟩; simp
    · rintro ⟨rfl, rfl⟩; simp
  · intro p _ hp
    simp [Jmat, hp]
  · simp
  · intro p _ hp
    have : b ≠ p.rev := fun h => hp (by simp [h])
    simp [Jmat, this]
  · simp

theorem UpperTheory.V.Fr.pr_dual :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (K : Type) [Field K] [CharP K l] (φ : k →+* K) (ρ : NRep F n K) (B : Box F n K), B.Of ρ → ρ.IsBar φ → ((∀ g, UpT (ρ.r g)) ∨ ∀ g, UpT (ρ.r g)ᵀ) → ∀ f : Matrix (Fin n) (Fin n) K →ₗ[K] K, (∀ g X, f (B.ad g X) = F.om K g * f X) → f = 0 := by
  intro l _ k _ _ F C₀ n ok hn K _ _ φ ρ B hB hbar htri f hf
  set Φ : Matrix (Fin n) (Fin n) K := fun i j => f (Matrix.single i j 1) with hΦ
  have hsum : ∀ X : Matrix (Fin n) (Fin n) K, f X = ∑ i, ∑ j, X i j * Φ i j := fun X => by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hΦ, ← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have h0 : ∀ (g : F.G0) X, f (ρ.r g * X) = F.om K g * f (X * ρ.r g) := fun g X => by
    rw [← hf]
    congr 1
    have hr : (B.r g).right = 1 := (B.nu g).trans g.2
    show _ = (B.r g).adFun _
    rw [GG.adFun, if_pos hr, ← hB.res g, GG.mat]
    simp [Matrix.mul_assoc]
  have h1 : ∀ (g : F.G0) i j, ∑ p, ρ.r g p i * Φ p j = F.om K g * ∑ q, Φ i q * ρ.r g j q := fun g i j => by
    have := h0 g (Matrix.single i j 1)
    rw [hsum, hsum] at this
    rw [Finset.sum_eq_single i (s := Finset.univ) (f := fun a => ∑ b, (Matrix.single i j (1 : K) * ρ.r g) a b * Φ a b)]
      at this
    · convert this using 2 with p
      · rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb
          rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hb, zero_mul]
        · simp
      · simp [mul_comm]
    · intro a _ ha
      exact Finset.sum_eq_zero fun b _ => by rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ ha, zero_mul]
    · simp
  have hc : ∀ i, -Φ i i.rev = F.om K F.c * Φ i i.rev := fun i => by
    rw [hΦ]
    dsimp only
    rw [← hf, ← map_neg, ← thetaLie_single]
    congr 1
    have hr : (B.r F.c).right ≠ 1 := by rw [B.nu, ok.del_c]; decide
    have hl : (B.r F.c).left = 1 := Units.ext hB.atc
    show _ = (B.r F.c).adFun _
    rw [GG.adFun, if_neg hr, GG.mat, hl]
    simp
  have key : ∀ i j, (∀ g : F.G0, ρ.r g i i * Φ i j = F.om K g * (Φ i j * ρ.r g j j)) → Φ i j = 0 := by
    intro i j h
    by_contra hne
    have h2 : ∀ g : F.G0, F.om k g * F.Ψ g ^ (w n j - w n i) = 1 := fun g => by
      have e := h g
      rw [hbar.1, hbar.1, ← om_map F φ, mul_comm (Φ i j), ← mul_assoc, ← map_mul] at e
      have e2 := φ.injective (mul_right_cancel₀ hne e)
      rw [← Units.val_mul, Units.val_inj] at e2
      rw [_root_.zpow_sub, ← mul_assoc, ← e2, mul_inv_cancel]
    rcases w_cases hn i j with h3 | h3 | ⟨h3, rfl⟩
    · obtain ⟨g, hg⟩ := ok.f2a
      exact hg (by simpa [h3] using h2 g)
    · obtain ⟨g, hg⟩ := ok.f2b _ h3
      exact hg (h2 g)
    · obtain ⟨g, hg⟩ := ok.f2c _ h3
      apply hg
      rcases Int.units_eq_one_or (F.del g) with hd | hd
      · rw [h2 ⟨g, hd⟩, one_mul]
        simp [Frame.delK, hd]
      · have hm : g * F.c ∈ F.del.ker := by rw [MonoidHom.mem_ker, map_mul, hd, ok.del_c]; rfl
        have e := h2 ⟨_, hm⟩
        have ec : F.om k F.c = -1 := by
          apply Units.ext
          apply φ.injective
          rw [om_map]
          have := hc i
          rw [← neg_one_mul] at this
          rw [← mul_right_cancel₀ hne this]
          simp
        have ed : F.delK k g = -1 := by
          apply Units.ext
          simp [Frame.delK, hd]
        simp only [map_mul, ec, ok.Ψ_c, mul_one] at e
        rw [ed, mul_right_comm, e]
  have hz : ∀ i j, Φ i j = 0 := by
    rcases htri with ht | ht
    · exact tri_zero (ι := (Fin n)ᵒᵈ) (fun g : F.G0 => (ρ.r g)ᵀ) (fun g => F.om K g) Φ
        (fun g i j hij => ht g j i hij) h1 key
    · exact tri_zero (fun g : F.G0 => (ρ.r g)ᵀ) (fun g => F.om K g) Φ ht h1 key
  ext1 X
  simp [hsum, hz]
