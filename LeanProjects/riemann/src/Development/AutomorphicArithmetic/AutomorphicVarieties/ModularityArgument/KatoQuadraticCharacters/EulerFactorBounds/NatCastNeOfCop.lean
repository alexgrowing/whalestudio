import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic

noncomputable section

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

def rz (M : ℕ) (a : Fin 2 → ℤ) : Row M := fun i => ((a i : ℤ) : ZMod M)

def aU (l L N : ℕ) (x : ZMod N) : Fin 2 → ℤ := ![(N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L, 0]

def aV (l L N : ℕ) : Fin 2 → ℤ := ![(topT l L N : ℤ) * (l : ℤ) ^ L, (N : ℤ)]

def aUT (l L N p : ℕ) (x : ZMod N) : Fin 2 → ℤ :=
  ![bar l L N p * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L) * p + N * (l : ℤ) ^ L, 0]

def aVT (l L N p : ℕ) : Fin 2 → ℤ :=
  ![bar l L N p * (topT l L N : ℤ) * (l : ℤ) ^ L * p, bar l L N p * N * p + N * (l : ℤ) ^ L]

theorem rz_toQ (M : ℕ) [NeZero M] (a : Fin 2 → ℤ) (i : Fin 2) :
    ∃ j : ℤ, ((a i : ℤ) : ℚ) / (M : ℚ) = toQ M (rz M a) i + j := by
  refine ⟨a i / M, ?_⟩
  have hM : (M : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hv : (((a i : ZMod M).val : ℤ)) = a i % M := ZMod.val_intCast (a i)
  have k : a i % M + M * (a i / M) = a i := by rw [Int.emod_def]; ring
  simp only [toQ, rz]
  rw [div_add' _ _ _ hM, div_left_inj' hM]
  have e : (((a i : ZMod M).val : ℕ) : ℚ) = ((a i % M : ℤ) : ℚ) := by exact_mod_cast hv
  rw [e]
  have k' : ((a i % M + M * (a i / M) : ℤ) : ℚ) = ((a i : ℤ) : ℚ) := by exact_mod_cast k
  push_cast at k' ⊢
  linarith

theorem rz_congr {M : ℕ} {a b : Fin 2 → ℤ} (h : ∀ i, (M : ℤ) ∣ b i - a i) : rz M a = rz M b := by
  funext i
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (h i)

theorem smul_rz (M : ℕ) (k : ℤ) (a : Fin 2 → ℤ) : (k : ZMod M) • rz M a = rz M (k • a) := by
  funext i
  simp [rz]

theorem up_rz (k M : ℕ) [NeZero M] (a : Fin 2 → ℤ) : up k M (rz M a) = rz (k * M) ((k : ℤ) • a) := by
  funext i
  simp only [up, rz, Pi.smul_apply, smul_eq_mul]
  have hv : (((a i : ZMod M).val : ℤ)) = a i % M := ZMod.val_intCast (a i)
  rw [show ((k * (a i : ZMod M).val : ℕ) : ZMod (k * M)) = (((k * (a i % M) : ℤ)) : ZMod (k * M)) by
    rw [← hv]; push_cast; rfl]
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2
  refine ⟨a i / M, ?_⟩
  have k' : a i % M + M * (a i / M) = a i := by rw [Int.emod_def]; ring
  push_cast
  linear_combination (-(k : ℤ)) * k'

theorem two_smul_rz_ne {M l : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (h : l ∣ M) (a : Fin 2 → ℤ) (i : Fin 2)
    (ha : ((a i : ℤ) : ZMod l) ≠ 0) : (2 : ZMod M) • rz M a ≠ 0 := by
  haveI := Fact.mk hl
  intro hz
  have h' := congrFun hz i
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, rz] at h'
  have h'' := congrArg (ZMod.castHom h (ZMod l)) h'
  rw [map_mul, map_intCast, map_zero, map_ofNat] at h''
  rcases mul_eq_zero.1 h'' with h2' | h2'
  · have h3 : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h2'
    have h4 := (CharP.cast_eq_zero_iff (ZMod l) l 2).1 h3
    exact h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 h4)
  · exact ha h2'

theorem natCast_ne_of_cop {l N : ℕ} (hl : l.Prime) (hc : Nat.Coprime l N) : (N : ZMod l) ≠ 0 := by
  intro h0
  have hd := (CharP.cast_eq_zero_iff (ZMod l) l N).1 h0
  exact hl.ne_one (Nat.Coprime.eq_one_of_dvd hc hd)

theorem bar_mul {l N p : ℕ} (L : ℕ) (hl : l ≠ 0) (hN : N ≠ 0) (hp : Nat.Coprime p (l * N)) :
    ((N * l ^ L : ℕ) : ℤ) ∣ bar l L N p * p - 1 := by
  have h1 : Nat.Coprime p l := Nat.Coprime.coprime_dvd_right (dvd_mul_right l N) hp
  have h2 : Nat.Coprime p N := Nat.Coprime.coprime_dvd_right (dvd_mul_left N l) hp
  have hcop : Nat.Coprime p (N * l ^ L) := Nat.Coprime.mul_right h2 (Nat.Coprime.pow_right L h1)
  haveI : NeZero (N * l ^ L) := ⟨mul_ne_zero hN (pow_ne_zero _ hl)⟩
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub 1 _ _).1
  unfold bar
  push_cast
  rw [ZMod.natCast_zmod_val]
  exact (ZMod.coe_mul_inv_eq_one p hcop).symm.trans (mul_comm _ _)

theorem bar_mul_l {l N p L : ℕ} (hL : 1 ≤ L) (hl : l ≠ 0) (hN : N ≠ 0) (hp : Nat.Coprime p (l * N)) :
    ((bar l L N p : ℤ) : ZMod l) * (p : ZMod l) = 1 := by
  have h6 := bar_mul L hl hN hp
  have hl' : (l : ℤ) ∣ ((N * l ^ L : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.2 (Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N)
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (bar l L N p * p) l).2 (dvd_trans hl' h6)
  push_cast at hd
  exact hd.symm

theorem aU_mod {l L N : ℕ} (hL : 1 ≤ L) (x : ZMod N) :
    ((aU l L N x 0 : ℤ) : ZMod l) = N ∧ ((aU l L N x 1 : ℤ) : ZMod l) = 0 := by
  constructor
  · simp only [aU, Matrix.cons_val_zero]
    push_cast
    rw [ZMod.natCast_self, zero_pow (by omega), mul_zero, add_zero]
  · simp [aU]

theorem aV_mod {l L N : ℕ} (hL : 1 ≤ L) :
    ((aV l L N 0 : ℤ) : ZMod l) = 0 ∧ ((aV l L N 1 : ℤ) : ZMod l) = N := by
  constructor
  · simp only [aV, Matrix.cons_val_zero]
    push_cast
    rw [ZMod.natCast_self, zero_pow (by omega), mul_zero]
  · simp [aV]

theorem aUT_mod {l L N p : ℕ} (hL : 1 ≤ L) (hl : l ≠ 0) (hN : N ≠ 0) (hp : Nat.Coprime p (l * N)) (x : ZMod N) :
    ((aUT l L N p x 0 : ℤ) : ZMod l) = N ∧ ((aUT l L N p x 1 : ℤ) : ZMod l) = 0 := by
  have hb := bar_mul_l hL hl hN hp
  constructor
  · simp only [aUT, Matrix.cons_val_zero]
    push_cast
    rw [ZMod.natCast_self, zero_pow (by omega)]
    linear_combination (N : ZMod l) * hb
  · simp [aUT]

theorem aVT_mod {l L N p : ℕ} (hL : 1 ≤ L) (hl : l ≠ 0) (hN : N ≠ 0) (hp : Nat.Coprime p (l * N)) :
    ((aVT l L N p 0 : ℤ) : ZMod l) = 0 ∧ ((aVT l L N p 1 : ℤ) : ZMod l) = N := by
  have hb := bar_mul_l hL hl hN hp
  constructor
  · simp only [aVT, Matrix.cons_val_zero]
    push_cast
    rw [ZMod.natCast_self, zero_pow (by omega)]
    ring
  · simp only [aVT, Matrix.cons_val_one, Matrix.head_cons]
    push_cast
    rw [ZMod.natCast_self, zero_pow (by omega)]
    linear_combination (N : ZMod l) * hb

theorem ok_of_mod {M l N : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (hc : Nat.Coprime l N) (h : l ∣ M) {a b : Fin 2 → ℤ}
    (ha : ((a 0 : ℤ) : ZMod l) = N) (hb : ((b 1 : ℤ) : ZMod l) = N) : Ok (rz M a) (rz M b) := by
  refine ⟨?_, ?_⟩
  · have hne := two_smul_rz_ne hl h2 h a 0 (by rw [ha]; exact natCast_ne_of_cop hl hc)
    intro hz
    apply hne
    funext j
    have hj := congrFun hz j
    simp only [Pi.smul_apply, Pi.zero_apply] at hj ⊢
    simpa [two_nsmul, two_zsmul, two_smul] using hj
  · have hne := two_smul_rz_ne hl h2 h b 1 (by rw [hb]; exact natCast_ne_of_cop hl hc)
    intro hz
    apply hne
    funext j
    have hj := congrFun hz j
    simp only [Pi.smul_apply, Pi.zero_apply] at hj ⊢
    simpa [two_nsmul, two_zsmul, two_smul] using hj

theorem ok_UV {M l L N : ℕ} (hl : l.Prime) (h2 : l ≠ 2) (hc : Nat.Coprime l N) (hL : 1 ≤ L) (h : l ∣ M) (x : ZMod N) :
    Ok (rz M (aU l L N x)) (rz M (aV l L N)) :=
  ok_of_mod hl h2 hc h (aU_mod hL x).1 (aV_mod hL).2

theorem ok_UVT {M l L N p : ℕ} [NeZero N] (hl : l.Prime) (h2 : l ≠ 2) (hc : Nat.Coprime l N) (hL : 1 ≤ L) (h : l ∣ M)
    (hp : Nat.Coprime p (l * N)) (x : ZMod N) : Ok (rz M (aUT l L N p x)) (rz M (aVT l L N p)) :=
  ok_of_mod hl h2 hc h (aUT_mod hL hl.ne_zero (NeZero.ne N) hp x).1 (aVT_mod hL hl.ne_zero (NeZero.ne N) hp).2

theorem ixU_toQ {M l L N : ℕ} [NeZero M] (hM : M = N * l ^ L) (x : ZMod N) (i : Fin 2) :
    ∃ j : ℤ, ixU l L N x i = toQ M (rz M (aU l L N x)) i + j := by
  subst hM
  obtain ⟨j, hj⟩ := rz_toQ (N * l ^ L) (aU l L N x) i
  refine ⟨j, ?_⟩
  rw [← hj]
  fin_cases i <;> rfl

theorem ixV_toQ {M l L N : ℕ} [NeZero M] (hM : M = N * l ^ L) (i : Fin 2) :
    ∃ j : ℤ, ixV l L N i = toQ M (rz M (aV l L N)) i + j := by
  subst hM
  obtain ⟨j, hj⟩ := rz_toQ (N * l ^ L) (aV l L N) i
  refine ⟨j, ?_⟩
  rw [← hj]
  fin_cases i <;> rfl

theorem ixUT_toQ {M l L N p : ℕ} [NeZero M] (hM : M = N * l ^ L * p) (x : ZMod N) (i : Fin 2) :
    ∃ j : ℤ, ixUT l L N p x i = toQ M (rz M (aUT l L N p x)) i + j := by
  subst hM
  obtain ⟨j, hj⟩ := rz_toQ (N * l ^ L * p) (aUT l L N p x) i
  refine ⟨j, ?_⟩
  rw [← hj]
  fin_cases i <;> rfl

theorem ixVT_toQ {M l L N p : ℕ} [NeZero M] (hM : M = N * l ^ L * p) (i : Fin 2) :
    ∃ j : ℤ, ixVT l L N p i = toQ M (rz M (aVT l L N p)) i + j := by
  subst hM
  obtain ⟨j, hj⟩ := rz_toQ (N * l ^ L * p) (aVT l L N p) i
  refine ⟨j, ?_⟩
  rw [← hj]
  fin_cases i <;> rfl

theorem Hyp.lv {l N c d : ℕ} {g : SL(2, ℤ)} (H : Hyp l N c d g) (hl : l ≠ 0) (hN : N ≠ 0) {M L : ℕ} (hM : M = N * l ^ L) :
    Lv c d M := by
  subst hM
  refine ⟨Nat.pos_of_ne_zero (mul_ne_zero hN (pow_ne_zero _ hl)), ?_, ?_⟩
  · have h1 : c.Coprime l := Nat.Coprime.coprime_dvd_right (Dvd.intro (6 * N) (by ring)) H.cc
    have h2 : c.Coprime N := Nat.Coprime.coprime_dvd_right (Dvd.intro_left (6 * l) rfl) H.cc
    exact Nat.Coprime.mul_right h2 (Nat.Coprime.pow_right L h1)
  · have h1 : d.Coprime l := Nat.Coprime.coprime_dvd_right (Dvd.intro (6 * N) (by ring)) H.cd
    have h2 : d.Coprime N := Nat.Coprime.coprime_dvd_right (Dvd.intro_left (6 * l) rfl) H.cd
    exact Nat.Coprime.mul_right h2 (Nat.Coprime.pow_right L h1)

theorem Hyp.lvT {l N c d p : ℕ} {g : SL(2, ℤ)} (H : Hyp l N c d g) (hl : l ≠ 0) (hN : N ≠ 0) (hp0 : p ≠ 0)
    (hp : Nat.Coprime p (l * N * c * d)) {M L : ℕ} (hM : M = N * l ^ L * p) : Lv c d M := by
  subst hM
  obtain ⟨h0, h1, h2⟩ := H.lv hl hN (rfl : N * l ^ L = N * l ^ L)
  exact ⟨Nat.mul_pos h0 (Nat.pos_of_ne_zero hp0),
    h1.mul_right (Nat.Coprime.coprime_mul_left_right (Nat.Coprime.coprime_mul_right_right hp)).symm,
    h2.mul_right (Nat.Coprime.coprime_mul_left_right hp).symm⟩

end UpperTheory.V.Z.Kato.Nb

end
