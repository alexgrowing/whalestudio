import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.heckeMatrix_mem_gammaZero_inf_and_exists_unit_inv :
    ∀ (l N p L : ℕ) [Fact l.Prime] [NeZero N], Nat.Coprime l N → Nat.Coprime p (l * N) →
        sgD N l p ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l ∧ ∃ ν : (ZMod (l ^ L * (N * N)))ˣ,
          (((ν : ZMod (l ^ L * (N * N))).val : ℕ) : ZMod N) = (en (sgD N l p) 0 0 : ZMod N) ∧
          (((ν : ZMod (l ^ L * (N * N))).val : ℕ) : ZMod (l ^ L)) = 1 ∧
          (((ν : ZMod (l ^ L * (N * N))).val : ℕ) : ZMod N) * (p : ZMod N) = 1 := by
  intro l N p L _ _ hlN hpN
  have hN0 : N ≠ 0 := NeZero.ne N
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hpN' : p.Coprime N := Nat.Coprime.coprime_dvd_right (dvd_mul_left N l) hpN
  obtain ⟨hmem, hd⟩ := Betti.isDiam_sgD (N := N) (l := l) hN0 hl0 hpN'
  refine ⟨hmem, ?_⟩
  have hc := CongruenceSubgroup.Gamma0_mem.1 hmem.1
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hc
  have hdet : (sgD N l p : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (sgD N l p : Matrix (Fin 2) (Fin 2) ℤ) 1 1
      - (sgD N l p : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (sgD N l p : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have h := (sgD N l p).2
    rwa [Matrix.det_fin_two] at h
  have hd' : (((sgD N l p : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = ((p : ℤ) : ZMod N) := by
    rw [Int.cast_natCast]; exact hd
  rw [show en (sgD N l p) 0 0 = (sgD N l p : Matrix (Fin 2) (Fin 2) ℤ) 0 0 from rfl]
  generalize (sgD N l p : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = a at hdet ⊢
  generalize (sgD N l p : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = d at hdet hd'
  generalize (sgD N l p : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = b at hdet
  generalize (sgD N l p : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = c at hdet hk
  subst hk
  have hcop : Nat.Coprime (l ^ L) (N * N) := Nat.Coprime.mul_right (hlN.pow_left L) (hlN.pow_left L)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  push_cast at huv
  set m : ℤ := 1 + (a - 1) * u * (l : ℤ) ^ L with hm
  have hmN : m = a + (1 - a) * v * ((N : ℤ) * N) := by
    rw [hm]; linear_combination (a - 1) * huv
  have hAN : IsCoprime a (N : ℤ) := ⟨d, -(b * k), by linear_combination hdet⟩
  have hMN : IsCoprime m (N : ℤ) := by
    obtain ⟨s, t, hst⟩ := hAN
    refine ⟨s, t - s * ((1 - a) * v * N), ?_⟩
    rw [hmN]; linear_combination hst
  have hML : IsCoprime m ((l : ℤ) ^ L) := ⟨1, -((a - 1) * u), by rw [hm]; ring⟩
  have hMn : IsCoprime m (((l ^ L * (N * N) : ℕ)) : ℤ) := by
    push_cast
    exact hML.mul_right (hMN.mul_right hMN)
  haveI : NeZero (l ^ L * (N * N)) := ⟨by positivity⟩
  have hU : IsUnit (m : ZMod (l ^ L * (N * N))) := by
    obtain ⟨s, t, hst⟩ := hMn
    have h2 := congrArg (fun x : ℤ => (x : ZMod (l ^ L * (N * N)))) hst
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, add_zero,
      Int.cast_one] at h2
    exact ⟨⟨(m : ZMod (l ^ L * (N * N))), (s : ZMod (l ^ L * (N * N))), (mul_comm _ _).trans h2,
      h2⟩, rfl⟩
  refine ⟨hU.unit, ?_, ?_, ?_⟩
  · rw [ZMod.natCast_val, IsUnit.unit_spec, ZMod.cast_intCast (dvd_mul_of_dvd_right (dvd_mul_right N N) _),
      ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact ⟨-((1 - a) * v * N), by rw [hmN]; ring⟩
  · rw [ZMod.natCast_val, IsUnit.unit_spec, ZMod.cast_intCast (dvd_mul_right (l ^ L) (N * N)),
      ← Int.cast_one, ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact ⟨-((a - 1) * u), by push_cast; rw [hm]; ring⟩
  · rw [ZMod.natCast_val, IsUnit.unit_spec, ZMod.cast_intCast (dvd_mul_of_dvd_right (dvd_mul_right N N) _),
      ← Int.cast_natCast p, ← hd', ← Int.cast_mul, ← Int.cast_one, ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact ⟨-(b * k) - (1 - a) * v * N * d, by rw [hmN]; linear_combination (-1 : ℤ) * hdet⟩
