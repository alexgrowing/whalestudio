import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.NatCastNeOfCop
import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

private theorem rows_p (M p : ℕ) (b : ℤ) (hb : (M : ℤ) ∣ b * p - 1) (a : Fin 2 → ℤ) :
    (p : ZMod M) • rz M (b • a) = rz M a := by
  have h := smul_rz M (p : ℤ) (b • a)
  rw [Int.cast_natCast] at h
  rw [h]
  apply rz_congr
  intro i
  have e : a i - ((p : ℤ) • b • a) i = -((b * p - 1) * a i) := by
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  exact (Dvd.dvd.mul_right hb _).neg_right

private theorem up_rz_add_tp_eq_rz_mul_of_eq (M p : ℕ) [NeZero M] (t : Fin 2 → ZMod p) (a c : Fin 2 → ℤ)
    (hc : ∀ i, c i = p * a i + M * ((t i).val : ℤ)) :
    up p M (rz M a) + tp p M t = rz (p * M) c := by
  rw [up_rz]
  funext i
  simp only [Pi.add_apply, rz, tp, Pi.smul_apply, smul_eq_mul, hc i]
  push_cast
  rfl

theorem UpperTheory.exists_rows_hecke_compatible_level_prime_pow :
    ∀ (l N p L : ℕ) [Fact l.Prime] [NeZero N] [Fact p.Prime] (x : ZMod N), l ≠ 2 → Nat.Coprime l N → Nat.Coprime p (l * N) → 1 ≤ L →
        ∃ xb yb : Row (N * l ^ L), Ok xb yb ∧ Ok ((p : ZMod (N * l ^ L)) • xb) ((p : ZMod (N * l ^ L)) • yb) ∧
          Ok (up p (N * l ^ L) xb + tp p (N * l ^ L) ![1, 0]) (up p (N * l ^ L) yb + tp p (N * l ^ L) ![0, 1]) ∧
          (∀ i, ∃ j : ℤ, ixU l L N x i = toQ (N * l ^ L) ((p : ZMod (N * l ^ L)) • xb) i + j) ∧
          (∀ i, ∃ j : ℤ, ixV l L N i = toQ (N * l ^ L) ((p : ZMod (N * l ^ L)) • yb) i + j) ∧
          (∀ i, ∃ j : ℤ, ixUT l L N p x i = toQ (p * (N * l ^ L)) (up p (N * l ^ L) xb + tp p (N * l ^ L) ![1, 0]) i + j) ∧
          (∀ i, ∃ j : ℤ, ixVT l L N p i = toQ (p * (N * l ^ L)) (up p (N * l ^ L) yb + tp p (N * l ^ L) ![0, 1]) i + j) := by
  intro l N p L _ _ _ x hl2 hlN hp hL
  have hl : l.Prime := Fact.out
  have hpp : p.Prime := Fact.out
  have hb0 := bar_mul (l := l) (N := N) (p := p) L hl.ne_zero (NeZero.ne N) hp
  generalize hM : N * l ^ L = M at hb0 ⊢
  have hM0 : M ≠ 0 := hM ▸ Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hl.ne_zero)
  haveI : NeZero M := ⟨hM0⟩
  haveI : NeZero (p * M) := ⟨Nat.mul_ne_zero hpp.ne_zero hM0⟩
  have hlM : l ∣ M := hM ▸ Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N
  have h1 := rows_p M p _ hb0 (aU l L N x)
  have h2 := rows_p M p _ hb0 (aV l L N)
  have hok := ok_UV hl hl2 hlN hL hlM x
  have hokT := ok_UVT (M := p * M) hl hl2 hlN hL (dvd_mul_of_dvd_right hlM p) hp x
  have hU : up p M (rz M (bar l L N p • aU l L N x)) + tp p M ![1, 0] = rz (p * M) (aUT l L N p x) := by
    apply up_rz_add_tp_eq_rz_mul_of_eq M p ![1, 0]
    intro i
    fin_cases i <;> simp [aU, aUT, ZMod.val_one, ← hM] <;> ring
  have hV : up p M (rz M (bar l L N p • aV l L N)) + tp p M ![0, 1] = rz (p * M) (aVT l L N p) := by
    apply up_rz_add_tp_eq_rz_mul_of_eq M p ![0, 1]
    intro i
    fin_cases i <;> simp [aV, aVT, ZMod.val_one, ← hM] <;> ring
  refine ⟨rz M (bar l L N p • aU l L N x), rz M (bar l L N p • aV l L N), ?_⟩
  rw [h1, h2, hU, hV]
  refine ⟨⟨?_, ?_⟩, hok, hokT, fun i => ixU_toQ hM.symm x i, fun i => ixV_toQ hM.symm i,
    fun i => ixUT_toQ (by rw [← hM]; ring) x i, fun i => ixVT_toQ (by rw [← hM]; ring) i⟩
  · intro h
    apply hok.1
    rw [← h1, smul_comm, h, smul_zero]
  · intro h
    apply hok.2
    rw [← h2, smul_comm, h, smul_zero]
