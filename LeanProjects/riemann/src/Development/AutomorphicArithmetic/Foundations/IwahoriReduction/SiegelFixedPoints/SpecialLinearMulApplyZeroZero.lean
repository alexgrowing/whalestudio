import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjectiveStatement

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L

private abbrev rd (a : ℕ) : SL(2, ℤ) →* SL(2, ZMod a) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod a))

private def red {a b : ℕ} (h : b ∣ a) : SL(2, ZMod a) →* SL(2, ZMod b) :=
  Matrix.SpecialLinearGroup.map (ZMod.castHom h (ZMod b))

private lemma rd_apply (a : ℕ) (g : SL(2, ℤ)) (i j : Fin 2) : (rd a g) i j = ((g i j : ℤ) : ZMod a) := rfl

private lemma red_apply {a b : ℕ} (h : b ∣ a) (γ : SL(2, ZMod a)) (i j : Fin 2) :
    (red h γ) i j = ZMod.castHom h (ZMod b) (γ i j) := rfl

private def cj {R : Type} [CommRing R] (u : Rˣ) (h : SL(2, R)) : SL(2, R) :=
  ⟨!![h 0 0, (u : R) * h 0 1; ((u⁻¹ : Rˣ) : R) * h 1 0, h 1 1], by
    have hd := h.det_coe
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]
    have hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := u.mul_inv
    linear_combination hd - h 0 1 * h 1 0 * hu⟩

private lemma cj00 {R : Type} [CommRing R] (u : Rˣ) (h : SL(2, R)) : (cj u h) 0 0 = h 0 0 := rfl
private lemma cj01 {R : Type} [CommRing R] (u : Rˣ) (h : SL(2, R)) : (cj u h) 0 1 = u * h 0 1 := rfl
private lemma cj10 {R : Type} [CommRing R] (u : Rˣ) (h : SL(2, R)) : (cj u h) 1 0 = ((u⁻¹ : Rˣ) : R) * h 1 0 := rfl

open Classical in
private noncomputable def H2 (N : ℕ) [NeZero N] : Finset SL(2, ZMod (N * N)) :=
  Finset.univ.filter fun η => η ∈ (CongruenceSubgroup.Gamma1 N).map (rd (N * N))

private lemma gam_iff {N l : ℕ} {g : SL(2, ℤ)} :
    g ∈ Gam N l ↔ g ∈ CongruenceSubgroup.Gamma1 N ∧ g ∈ CongruenceSubgroup.Gamma0 l :=
  Subgroup.mem_inf

end UpperTheory.Kd.L

private theorem coe_uel_eq_umat (c d M : ℤ) (hc : c ≠ 0)
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c → (p : ℤ) ∣ d → (p : ℤ) ∣ M → False) :
    ∃ t : ℤ, IsCoprime c (d + t * M) := by
  classical
  refine ⟨((∏ p ∈ c.natAbs.primeFactors.filter (fun p : ℕ => ¬ (p : ℤ) ∣ d), (p : ℕ) : ℕ) : ℤ), ?_⟩
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  rw [Int.gcd_eq_natAbs] at hpg
  have hpc : (p : ℤ) ∣ c := Int.ofNat_dvd_left.2 (hpg.trans (Nat.gcd_dvd_left _ _))
  have hpe := Int.ofNat_dvd_left.2 (hpg.trans (Nat.gcd_dvd_right _ _))
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases hpd : (p : ℤ) ∣ d
  · have htM := (dvd_add_right hpd).1 hpe
    rcases hpz.dvd_or_dvd htM with hpt | hpM
    · obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 (Int.natCast_dvd_natCast.1 hpt)
      rw [Finset.mem_filter, Nat.mem_primeFactors] at hq
      have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hq.1.1).1 hpq
      subst hpq'
      exact hq.2 hpd
    · exact h p hp hpc hpd hpM
  · have hpt : (p : ℤ) ∣ ((∏ p ∈ c.natAbs.primeFactors.filter (fun p : ℕ => ¬ (p : ℤ) ∣ d), (p : ℕ) : ℕ) : ℤ) := by
      apply Int.natCast_dvd_natCast.2
      apply Finset.dvd_prod_of_mem
      rw [Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hp, Int.ofNat_dvd_left.1 hpc, Int.natAbs_ne_zero.2 hc⟩, hpd⟩
    exact hpd ((dvd_add_left (dvd_mul_of_dvd_left hpt M)).1 hpe)

private theorem exists_rd_eq (M : ℕ) (γ : SL(2, ZMod M)) : ∃ g : SL(2, ℤ), rd M g = γ := by
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective (γ 0 0)
  obtain ⟨b, hb⟩ := ZMod.intCast_surjective (γ 0 1)
  obtain ⟨c0, hc0⟩ := ZMod.intCast_surjective (γ 1 0)
  obtain ⟨d0, hd0⟩ := ZMod.intCast_surjective (γ 1 1)
  have h1 : (a : ZMod M) * d0 - b * c0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    rw [ha, hb, hc0, hd0]
    exact this
  obtain ⟨s, hs⟩ : (M : ℤ) ∣ a * d0 - b * c0 - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h1]
    ring
  obtain ⟨c, d, hc, hd, hcd⟩ : ∃ c d : ℤ, (c : ZMod M) = γ 1 0 ∧ (d : ZMod M) = γ 1 1 ∧ IsCoprime c d := by
    by_cases hc00 : c0 + (if c0 = 0 then (M : ℤ) else 0) = 0
    · have hc0z : c0 = 0 := by
        by_contra hne
        simp [hne] at hc00
      have hM : (M : ℤ) = 0 := by simpa [hc0z] using hc00
      refine ⟨c0, d0, hc0, hd0, ⟨0, a, ?_⟩⟩
      rw [hM, hc0z] at hs
      linarith
    · obtain ⟨t, ht⟩ := coe_uel_eq_umat _ d0 (M : ℤ) hc00 (by
        intro p hp h1 h2 h3
        have h1' : (p : ℤ) ∣ c0 := by
          split_ifs at h1 with hz
          · rw [hz]
            exact dvd_zero _
          · simpa using h1
        have h4 : (p : ℤ) ∣ 1 := by
          have e : (1 : ℤ) = a * d0 - b * c0 - M * s := by linarith
          rw [e]
          exact dvd_sub (dvd_sub (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1' _))
            (dvd_mul_of_dvd_left h3 _)
        have h5 := Int.eq_one_of_dvd_one (by positivity) h4
        exact hp.one_lt.ne' (by exact_mod_cast h5))
      refine ⟨_, _, ?_, ?_, ht⟩
      · split_ifs <;> push_cast <;> simp [hc0]
      · push_cast
        simp [hd0]
  obtain ⟨u, v, huv⟩ := hcd
  have h1' : (a : ZMod M) * d - b * c = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    rw [ha, hb, hc, hd]
    exact this
  have h2 : (v : ZMod M) * d + u * c = 1 := by
    have := congrArg (fun x : ℤ => (x : ZMod M)) huv
    push_cast at this
    linear_combination this
  obtain ⟨g, hg⟩ : ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) =
      !![v + ((b + u) * v + (a - v) * u) * c, -u + ((b + u) * v + (a - v) * u) * d; c, d] :=
    ⟨⟨_, by
      rw [Matrix.det_fin_two_of]
      linear_combination huv⟩, rfl⟩
  refine ⟨g, ?_⟩
  ext i j
  rw [rd_apply, hg]
  fin_cases i <;> fin_cases j
  · simp
    rw [← ha]
    linear_combination (-(v : ZMod M)) * h1' + (a : ZMod M) * h2
  · simp
    rw [← hb]
    linear_combination (u : ZMod M) * h1' + (b : ZMod M) * h2
  · simp [hc]
  · simp [hd]

private theorem red_rd_eq_rd_of_dvd {a b : ℕ} (h : b ∣ a) (g : SL(2, ℤ)) : red h (rd a g) = rd b g := by
  ext i j
  simp [red_apply, rd_apply]
private theorem chineseRemainder_fst_snd_eq_castHom {L Q : ℕ} (hLQ : L.Coprime Q) (x : ZMod (L * Q)) :
    (ZMod.chineseRemainder hLQ x).1 = ZMod.castHom (dvd_mul_right L Q) (ZMod L) x ∧
    (ZMod.chineseRemainder hLQ x).2 = ZMod.castHom (dvd_mul_left Q L) (ZMod Q) x := by
  constructor
  · show ((ZMod.cast x : ZMod L × ZMod Q)).1 = _
    rw [Prod.fst_zmod_cast]
    rfl
  · show ((ZMod.cast x : ZMod L × ZMod Q)).2 = _
    rw [Prod.snd_zmod_cast]
    rfl

private theorem eq_of_red_eq_of_coprime {L Q : ℕ} (hLQ : L.Coprime Q) (x y : SL(2, ZMod (L * Q)))
    (h1 : red (dvd_mul_right L Q) x = red (dvd_mul_right L Q) y)
    (h2 : red (dvd_mul_left Q L) x = red (dvd_mul_left Q L) y) : x = y := by
  ext i j
  apply (ZMod.chineseRemainder hLQ).injective
  have e1 := congrArg (fun z : SL(2, ZMod L) => z i j) h1
  have e2 := congrArg (fun z : SL(2, ZMod Q) => z i j) h2
  simp only [red_apply] at e1 e2
  refine Prod.ext ?_ ?_
  · rw [(chineseRemainder_fst_snd_eq_castHom hLQ _).1, (chineseRemainder_fst_snd_eq_castHom hLQ _).1]
    exact e1
  · rw [(chineseRemainder_fst_snd_eq_castHom hLQ _).2, (chineseRemainder_fst_snd_eq_castHom hLQ _).2]
    exact e2

private theorem exists_red_eq_pair_of_coprime {L Q : ℕ} (hLQ : L.Coprime Q) (δ : SL(2, ZMod L)) (η : SL(2, ZMod Q)) :
    ∃ x : SL(2, ZMod (L * Q)), red (dvd_mul_right L Q) x = δ ∧ red (dvd_mul_left Q L) x = η := by
  have hA : ∀ z : ZMod L × ZMod Q,
      ZMod.castHom (dvd_mul_right L Q) (ZMod L) ((ZMod.chineseRemainder hLQ).symm z) = z.1 :=
    fun z => by
      rw [← (chineseRemainder_fst_snd_eq_castHom hLQ _).1]
      exact congrArg Prod.fst ((ZMod.chineseRemainder hLQ).apply_symm_apply z)
  have hB : ∀ z : ZMod L × ZMod Q,
      ZMod.castHom (dvd_mul_left Q L) (ZMod Q) ((ZMod.chineseRemainder hLQ).symm z) = z.2 :=
    fun z => by
      rw [← (chineseRemainder_fst_snd_eq_castHom hLQ _).2]
      exact congrArg Prod.snd ((ZMod.chineseRemainder hLQ).apply_symm_apply z)
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin 2) (Fin 2) (ZMod (L * Q)),
      X = fun i j => (ZMod.chineseRemainder hLQ).symm (δ i j, η i j) := ⟨_, rfl⟩
  have hXA : (ZMod.castHom (dvd_mul_right L Q) (ZMod L)).mapMatrix X = (δ : Matrix (Fin 2) (Fin 2) (ZMod L)) := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hX]
    exact hA _
  have hXB : (ZMod.castHom (dvd_mul_left Q L) (ZMod Q)).mapMatrix X = (η : Matrix (Fin 2) (Fin 2) (ZMod Q)) := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hX]
    exact hB _
  have hdet : X.det = 1 := by
    apply (ZMod.chineseRemainder hLQ).injective
    rw [map_one]
    refine Prod.ext ?_ ?_
    · rw [(chineseRemainder_fst_snd_eq_castHom hLQ _).1]
      show ZMod.castHom (dvd_mul_right L Q) (ZMod L) X.det = 1
      rw [RingHom.map_det, hXA, δ.det_coe]
    · rw [(chineseRemainder_fst_snd_eq_castHom hLQ _).2]
      show ZMod.castHom (dvd_mul_left Q L) (ZMod Q) X.det = 1
      rw [RingHom.map_det, hXB, η.det_coe]
  obtain ⟨x, hx⟩ : ∃ x : SL(2, ZMod (L * Q)), (x : Matrix (Fin 2) (Fin 2) (ZMod (L * Q))) = X :=
    ⟨⟨X, hdet⟩, rfl⟩
  refine ⟨x, ?_, ?_⟩
  · ext i j
    rw [red_apply, hx]
    exact congrFun (congrFun hXA i) j
  · ext i j
    rw [red_apply, hx]
    exact congrFun (congrFun hXB i) j

private theorem mem_gs_iff_exists_rd_eq (N l M : ℕ) [NeZero M] (γ : SL(2, ZMod M)) :
    γ ∈ Gs N l M ↔ ∃ g ∈ Gam N l, rd M g = γ := by
  unfold Gs
  simp [Subgroup.mem_map]

private theorem castHom_eq_zero_iff_dvd_val (l k : ℕ) [NeZero (l ^ k)] (hd : l ∣ l ^ k) (x : ZMod (l ^ k)) :
    ZMod.castHom hd (ZMod l) x = 0 ↔ l ∣ x.val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
private theorem sum_gs_red_eq_card_smul_sum_lower_zero (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (k : ℕ) (hk : k ≠ 0)
    (hlN : ¬ l ∣ N) [NeZero (l ^ k * (N * N))] {V : Type} [AddCommMonoid V]
    (F : SL(2, ZMod (l ^ k)) → V) :
    ∑ γ ∈ Gs N l (l ^ k * (N * N)), F (red (dvd_mul_right (l ^ k) (N * N)) γ) =
      (H2 N).card • ∑ δ ∈ Finset.univ.filter
        (fun δ : SL(2, ZMod (l ^ k)) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (δ 1 0) = 0), F δ := by
  classical
  have hl : l.Prime := Fact.out
  have hLQ : (l ^ k).Coprime (N * N) := by
    have h : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hl).2 hlN
    exact Nat.Coprime.pow_left _ (Nat.Coprime.mul_right h h)
  set B := Finset.univ.filter
    (fun δ : SL(2, ZMod (l ^ k)) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (δ 1 0) = 0) with hB
  calc ∑ γ ∈ Gs N l (l ^ k * (N * N)), F (red (dvd_mul_right (l ^ k) (N * N)) γ)
        = ∑ p ∈ B ×ˢ H2 N, F p.1 := by
        apply Finset.sum_nbij (fun γ => (red (dvd_mul_right (l ^ k) (N * N)) γ,
          red (dvd_mul_left (N * N) (l ^ k)) γ))
        · intro γ hγ
          obtain ⟨g, hg, rfl⟩ := (mem_gs_iff_exists_rd_eq _ _ _ γ).1 hγ
          rw [gam_iff] at hg
          rw [red_rd_eq_rd_of_dvd, red_rd_eq_rd_of_dvd, Finset.mem_product, hB, Finset.mem_filter]
          refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · rw [rd_apply, map_intCast]
            exact CongruenceSubgroup.Gamma0_mem.1 hg.2
          · unfold H2
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ _, Subgroup.mem_map_of_mem _ hg.1⟩
        · intro x _ y _ hxy
          simp only [Prod.mk.injEq] at hxy
          exact eq_of_red_eq_of_coprime hLQ x y hxy.1 hxy.2
        · rintro ⟨δ, η⟩ hp
          rw [Finset.mem_coe, Finset.mem_product, hB, Finset.mem_filter] at hp
          obtain ⟨⟨_, hδ⟩, hη⟩ := hp
          unfold H2 at hη
          rw [Finset.mem_filter] at hη
          obtain ⟨g0, hg0, hg0e⟩ := Subgroup.mem_map.1 hη.2
          obtain ⟨x, hx1, hx2⟩ := exists_red_eq_pair_of_coprime hLQ δ η
          obtain ⟨g, rfl⟩ := exists_rd_eq _ x
          rw [red_rd_eq_rd_of_dvd] at hx1 hx2
          refine ⟨rd _ g, ?_, ?_⟩
          · rw [Finset.mem_coe, mem_gs_iff_exists_rd_eq]
            refine ⟨g, ?_, rfl⟩
            rw [gam_iff]
            constructor
            · have E := congrArg (red (dvd_mul_right N N)) (hx2.trans hg0e.symm)
              rw [red_rd_eq_rd_of_dvd, red_rd_eq_rd_of_dvd] at E
              have e : ∀ i j, ((g i j : ℤ) : ZMod N) = ((g0 i j : ℤ) : ZMod N) := fun i j => by
                have := congrArg (fun z : SL(2, ZMod N) => z i j) E
                simpa only [rd_apply] using this
              rw [CongruenceSubgroup.Gamma1_mem] at hg0 ⊢
              rw [e, e, e]
              exact hg0
            · rw [CongruenceSubgroup.Gamma0_mem]
              have := congrArg
                (fun z : SL(2, ZMod (l ^ k)) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (z 1 0)) hx1
              simp only [rd_apply, map_intCast] at this
              rw [this]
              exact hδ
          · dsimp only
            rw [red_rd_eq_rd_of_dvd, red_rd_eq_rd_of_dvd, hx1, hx2]
        · intro _ _
          rfl
    _ = ∑ δ ∈ B, ∑ _η ∈ H2 N, F δ := Finset.sum_product _ _ _
    _ = (H2 N).card • ∑ δ ∈ B, F δ := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl (fun δ _ => Finset.sum_const _)
private theorem cj_inv_cj_eq_self {R : Type} [CommRing R] (u : Rˣ) (X : SL(2, R)) : cj u⁻¹ (cj u X) = X := by
  have e11 : ∀ (v : Rˣ) (Y : SL(2, R)), (cj v Y) 1 1 = Y 1 1 := fun _ _ => rfl
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cj00, cj01, cj10, e11]

private theorem sum_cj_eq_sum_entries_not_dvd (l : ℕ) [Fact l.Prime] (k : ℕ) (hk : k ≠ 0)
    (gm : (ZMod l)ˣ → SL(2, ℤ))
    (col : ∀ r : (ZMod l)ˣ, ((gm r 1 0 : ℤ) : ZMod l) = -(r : ZMod l) * ((gm r 0 0 : ℤ) : ZMod l))
    (u : (ZMod (l ^ k))ˣ) {V : Type} [AddCommMonoid V] (Φ : SL(2, ZMod (l ^ k)) → V) :
    ∑ r : (ZMod l)ˣ, ∑ δ ∈ Finset.univ.filter
        (fun δ : SL(2, ZMod (l ^ k)) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (δ 1 0) = 0),
        Φ (cj u (rd (l ^ k) (gm r) * δ)) =
      ∑ h ∈ Finset.univ.filter
        (fun h : SL(2, ZMod (l ^ k)) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), Φ h := by
  classical
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hl.ne_zero⟩
  set π := ZMod.castHom (dvd_pow_self l hk) (ZMod l) with hπ
  set B := Finset.univ.filter (fun δ : SL(2, ZMod (l ^ k)) => π (δ 1 0) = 0) with hB
  set S := Finset.univ.filter
    (fun h : SL(2, ZMod (l ^ k)) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val) with hS
  have hS' : ∀ h, h ∈ S ↔ π (h 0 0) ≠ 0 ∧ π (h 1 0) ≠ 0 := by
    intro h
    rw [hS, Finset.mem_filter]
    constructor
    · rintro ⟨_, a, b⟩
      exact ⟨fun h0 => a ((castHom_eq_zero_iff_dvd_val l k (dvd_pow_self l hk) _).1 h0),
        fun h0 => b ((castHom_eq_zero_iff_dvd_val l k (dvd_pow_self l hk) _).1 h0)⟩
    · rintro ⟨a, b⟩
      exact ⟨Finset.mem_univ _, fun h0 => a ((castHom_eq_zero_iff_dvd_val l k (dvd_pow_self l hk) _).2 h0),
        fun h0 => b ((castHom_eq_zero_iff_dvd_val l k (dvd_pow_self l hk) _).2 h0)⟩
  have hu : π (u : ZMod (l ^ k)) * π ((u⁻¹ : (ZMod (l ^ k))ˣ) : ZMod (l ^ k)) = 1 := by
    rw [← map_mul, u.mul_inv, map_one]
  have hu1 : π ((u⁻¹ : (ZMod (l ^ k))ˣ) : ZMod (l ^ k)) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hu
    exact zero_ne_one hu
  have hu2 : π (u : ZMod (l ^ k)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hu
    exact zero_ne_one hu
  have hA : ∀ r, π (rd (l ^ k) (gm r) 1 0) = -(r : ZMod l) * π (rd (l ^ k) (gm r) 0 0) := by
    intro r
    rw [rd_apply, rd_apply, map_intCast, map_intCast]
    exact col r
  have hA00 : ∀ r, π (rd (l ^ k) (gm r) 0 0) ≠ 0 := by
    intro r h0
    have hd := (gm r).det_coe
    rw [Matrix.det_fin_two] at hd
    have h1 := congrArg (fun x : ℤ => (x : ZMod l)) hd
    push_cast at h1
    rw [col r] at h1
    rw [rd_apply, map_intCast] at h0
    rw [h0] at h1
    simp at h1
  have pm : ∀ (X Y : SL(2, ZMod (l ^ k))) (i j : Fin 2),
      π ((X * Y) i j) = π (X i 0) * π (Y 0 j) + π (X i 1) * π (Y 1 j) := by
    intro X Y i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, map_mul]
  have pinv : ∀ X : SL(2, ZMod (l ^ k)), (X⁻¹) 1 0 = - X 1 0 ∧ (X⁻¹) 1 1 = X 0 0 := by
    intro X
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp
  have hB00 : ∀ δ ∈ B, π (δ 0 0) ≠ 0 := by
    intro δ hδ h0
    rw [hB, Finset.mem_filter] at hδ
    have hd := δ.det_coe
    rw [Matrix.det_fin_two] at hd
    have h1 := congrArg π hd
    rw [map_sub, map_mul, map_mul, h0, hδ.2, map_one] at h1
    simp at h1
  have e11 : ∀ (v : (ZMod (l ^ k))ˣ) (Y : SL(2, ZMod (l ^ k))), (cj v Y) 1 1 = Y 1 1 := fun _ _ => rfl
  obtain ⟨w, hw⟩ : ∃ w : ZMod l → (ZMod l)ˣ, ∀ x, x ≠ 0 → (w x : ZMod l) = x :=
    ⟨fun x => if hx : x = 0 then 1 else Units.mk0 x hx, fun x hx => by simp [hx]⟩
  obtain ⟨R, hR⟩ : ∃ R : SL(2, ZMod (l ^ k)) → (ZMod l)ˣ, ∀ h,
      R h = w (-(π ((cj u⁻¹ h) 1 0)) / π ((cj u⁻¹ h) 0 0)) := ⟨_, fun _ => rfl⟩
  have hcc : ∀ X, cj u (cj u⁻¹ X) = X := by
    intro X
    have := cj_inv_cj_eq_self u⁻¹ X
    rwa [inv_inv] at this
  rw [(Finset.sum_product' Finset.univ B (fun r δ => Φ (cj u (rd (l ^ k) (gm r) * δ)))).symm]
  apply Finset.sum_nbij' (fun p => cj u (rd (l ^ k) (gm p.1) * p.2))
    (fun h => (R h, (rd (l ^ k) (gm (R h)))⁻¹ * cj u⁻¹ h))
  · rintro ⟨r, δ⟩ hp
    rw [Finset.mem_product] at hp
    have hδ := hp.2
    have hδ' : π (δ 1 0) = 0 := by
      rw [hB, Finset.mem_filter] at hδ
      exact hδ.2
    rw [hS']
    dsimp only
    rw [cj00, cj10, map_mul, pm, pm, hδ', hA]
    refine ⟨?_, ?_⟩
    · rw [mul_zero, add_zero]
      exact mul_ne_zero (hA00 r) (hB00 δ hδ)
    · rw [mul_zero, add_zero]
      exact mul_ne_zero hu1 (mul_ne_zero (mul_ne_zero (neg_ne_zero.2 r.ne_zero) (hA00 r)) (hB00 δ hδ))
  · intro h hh
    rw [hS'] at hh
    rw [Finset.mem_product, hB, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
    have h00 : π ((cj u⁻¹ h) 0 0) = π (h 0 0) := by rw [cj00]
    have h10 : π ((cj u⁻¹ h) 1 0) = π (u : ZMod (l ^ k)) * π (h 1 0) := by
      rw [cj10, inv_inv, map_mul]
    have hx : ((R h : (ZMod l)ˣ) : ZMod l) = -(π ((cj u⁻¹ h) 1 0)) / π ((cj u⁻¹ h) 0 0) := by
      rw [hR]
      apply hw
      rw [h00, h10]
      simp [hh.1, hh.2, hu2]
    have hh1 := hh.1
    rw [pm, (pinv _).1, (pinv _).2, map_neg, hA, hx, h00, h10]
    field_simp
    ring
  · rintro ⟨r, δ⟩ hp
    rw [Finset.mem_product] at hp
    have hδ := hp.2
    have hδ' : π (δ 1 0) = 0 := by
      rw [hB, Finset.mem_filter] at hδ
      exact hδ.2
    have hA0 := hA00 r
    have hδ0 := hB00 δ hδ
    have hRr : R (cj u (rd (l ^ k) (gm r) * δ)) = r := by
      rw [hR, cj_inv_cj_eq_self]
      apply Units.ext
      rw [hw]
      · rw [pm, pm, hδ', hA]
        simp only [mul_zero, add_zero]
        field_simp
      · rw [pm, pm, hδ', hA]
        simp only [mul_zero, add_zero]
        exact div_ne_zero (neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (neg_ne_zero.2 r.ne_zero) hA0) hδ0))
          (mul_ne_zero hA0 hδ0)
    dsimp only
    rw [cj_inv_cj_eq_self, hRr, inv_mul_cancel_left]
  · intro h _
    dsimp only
    rw [mul_inv_cancel_left, hcc]
  · intro p _
    rfl
private theorem rd_liftSL (M : ℕ) (γ : SL(2, ZMod M)) : rd M (liftSL M γ) = γ := by
  unfold liftSL
  exact Classical.epsilon_spec (exists_rd_eq M γ)

theorem UpperTheory.Kd.L.count :
    ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N], ∃ μ : ℕ, 0 < μ ∧ ∀ (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (n m : ℕ), 1 ≤ m → ∀ (V : Type) [AddCommMonoid V] (Φ : SL(2, ZMod (l ^ (m + n))) → V) (Ψ : SL(2, ℤ) → V), (∀ g ∈ CongruenceSubgroup.Gamma0 N, ((en g 0 0 : ℤ) : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) → ∀ h : SL(2, ZMod (l ^ (m + n))), h 0 0 = (en g 0 0 : ℤ) → h 0 1 = ((N : ℤ) * en g 0 1 : ℤ) → (N : ZMod (l ^ (m + n))) * h 1 0 = (en g 1 0 : ℤ) → h 1 1 = (en g 1 1 : ℤ) → Ψ g = Φ h) → ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ Gs N l (topMu l n m N), Ψ (gm r₀ * liftSL _ γ) = μ • ∑ h ∈ Finset.univ.filter (fun h : SL(2, ZMod (l ^ (m + n))) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), Φ h := by
  classical
  intro l _ N _
  have hl : l.Prime := Fact.out
  refine ⟨(H2 N).card, ?_, ?_⟩
  · apply Finset.card_pos.2
    refine ⟨1, ?_⟩
    unfold H2
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨1, Subgroup.one_mem _, map_one _⟩⟩
  intro c d gm hP n m hm V _ Φ Ψ hΨ
  obtain ⟨_, _, cop, _, _, _, _, g0, ga, col⟩ := hP
  unfold topMu
  have hk : m + n ≠ 0 := by omega
  haveI : NeZero (l ^ (m + n) * (N * N)) :=
    ⟨mul_ne_zero (pow_ne_zero _ hl.ne_zero) (mul_ne_zero (NeZero.ne N) (NeZero.ne N))⟩
  have hcop : N.Coprime (l ^ (m + n)) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hl).2 cop).symm
  obtain ⟨u, hu⟩ : ∃ u : (ZMod (l ^ (m + n)))ˣ, (u : ZMod (l ^ (m + n))) = N :=
    ⟨ZMod.unitOfCoprime N hcop, ZMod.coe_unitOfCoprime _ _⟩
  have hNM : N ∣ l ^ (m + n) * (N * N) := (dvd_mul_right N N).trans (dvd_mul_left (N * N) _)
  have key : ∀ r₀ : (ZMod l)ˣ, ∀ γ ∈ Gs N l (l ^ (m + n) * (N * N)),
      Ψ (gm r₀ * liftSL _ γ) =
        Φ (cj u (rd (l ^ (m + n)) (gm r₀) * red (dvd_mul_right (l ^ (m + n)) (N * N)) γ)) := by
    intro r₀ γ hγ
    obtain ⟨g1, hg1, rfl⟩ := (mem_gs_iff_exists_rd_eq _ _ _ γ).1 hγ
    rw [gam_iff] at hg1
    have hL := rd_liftSL _ (rd (l ^ (m + n) * (N * N)) g1)
    set L1 := liftSL _ (rd (l ^ (m + n) * (N * N)) g1)
    rw [← hL, red_rd_eq_rd_of_dvd, ← map_mul]
    have E := congrArg (red hNM) hL
    rw [red_rd_eq_rd_of_dvd, red_rd_eq_rd_of_dvd] at E
    have e : ∀ i j, ((L1 i j : ℤ) : ZMod N) = ((g1 i j : ℤ) : ZMod N) := fun i j => by
      have := congrArg (fun z : SL(2, ZMod N) => z i j) E
      simpa only [rd_apply] using this
    have hg1' := (CongruenceSubgroup.Gamma1_mem _ _).1 hg1.1
    have hL00 : ((L1 0 0 : ℤ) : ZMod N) = 1 := by rw [e]; exact hg1'.1
    have hL10 : ((L1 1 0 : ℤ) : ZMod N) = 0 := by rw [e]; exact hg1'.2.2
    have hgΓ : gm r₀ * L1 ∈ CongruenceSubgroup.Gamma0 N :=
      Subgroup.mul_mem _ (g0 r₀) (CongruenceSubgroup.Gamma0_mem.2 hL10)
    have hg00 : ((en (gm r₀ * L1) 0 0 : ℤ) : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) := by
      rw [← ga r₀]
      unfold en
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      push_cast
      rw [hL00, hL10]
      ring
    apply hΨ _ hgΓ hg00
    · rw [cj00, rd_apply]
      rfl
    · rw [cj01, rd_apply, hu]
      unfold en
      push_cast
      ring
    · rw [cj10, ← hu, ← mul_assoc, Units.mul_inv, one_mul, rd_apply]
      rfl
    · rw [show (cj u (rd (l ^ (m + n)) (gm r₀ * L1))) 1 1 = (rd (l ^ (m + n)) (gm r₀ * L1)) 1 1 from rfl,
        rd_apply]
      rfl
  calc ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ Gs N l (l ^ (m + n) * (N * N)), Ψ (gm r₀ * liftSL _ γ)
      = ∑ r₀ : (ZMod l)ˣ, (H2 N).card • ∑ δ ∈ Finset.univ.filter
          (fun δ : SL(2, ZMod (l ^ (m + n))) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (δ 1 0) = 0),
          Φ (cj u (rd (l ^ (m + n)) (gm r₀) * δ)) := by
        apply Finset.sum_congr rfl
        intro r₀ _
        rw [Finset.sum_congr rfl (key r₀)]
        exact sum_gs_red_eq_card_smul_sum_lower_zero l N (m + n) hk cop (fun δ => Φ (cj u (rd (l ^ (m + n)) (gm r₀) * δ)))
    _ = (H2 N).card • ∑ r₀ : (ZMod l)ˣ, ∑ δ ∈ Finset.univ.filter
          (fun δ : SL(2, ZMod (l ^ (m + n))) => ZMod.castHom (dvd_pow_self l hk) (ZMod l) (δ 1 0) = 0),
          Φ (cj u (rd (l ^ (m + n)) (gm r₀) * δ)) := by
        rw [Finset.smul_sum]
    _ = _ := by
        rw [sum_cj_eq_sum_entries_not_dvd l (m + n) hk gm col u Φ]
