import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.TopRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.TopCocG

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

private theorem frac_eq (D D' : ℕ) [NeZero D] (h : D' = D) (a : ℤ) :
    ∃ j : ℤ, (a : ℚ) / (D' : ℚ) = (((a : ZMod D).val : ℕ) : ℚ) / D + j := by
  subst h
  refine ⟨a / (D' : ℤ), ?_⟩
  have h1 : ((((a : ZMod D').val : ℕ) : ℤ)) = a % (D' : ℤ) := ZMod.val_intCast a
  have h2 : (((a : ZMod D').val : ℕ) : ℚ) = ((a % (D' : ℤ) : ℤ) : ℚ) := by
    rw [← h1]
    push_cast
    rfl
  have hD : (D' : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne D'
  have e : a % (D' : ℤ) = a - (D' : ℤ) * (a / (D' : ℤ)) := Int.emod_def a D'
  rw [h2, e]
  push_cast
  field_simp
  ring

private theorem two_ne (l D : ℕ) [Fact l.Prime] (hl : l ≠ 2) (hD : l ∣ D) (a : ℤ) (ha : (a : ZMod l) ≠ 0) :
    (2 : ZMod D) * (a : ZMod D) ≠ 0 := by
  intro h0
  have h1 := congrArg (ZMod.castHom hD (ZMod l)) h0
  simp only [map_mul, map_ofNat, map_intCast, map_zero] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · have h3 : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact hl ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h3)
  · exact ha h2

private theorem bar_mul (l L N p : ℕ) (hL : L ≠ 0) (h : Nat.Coprime p (N * l ^ L)) :
    ((bar l L N p : ℤ) : ZMod l) * (p : ZMod l) = 1 := by
  by_cases hM : N * l ^ L = 0
  · have hp : p = 1 := by
      simpa [hM] using h
    subst hp
    have hv : ((1 : ZMod (N * l ^ L))⁻¹).val = 1 := by
      rw [ZMod.inv_one, ZMod.val_one'' (by omega)]
    simp only [bar, Nat.cast_one, hv, Int.cast_one, mul_one]
  · haveI : NeZero (N * l ^ L) := ⟨hM⟩
    have hdvd : l ∣ N * l ^ L := Dvd.dvd.mul_left (dvd_pow_self l hL) N
    have hu : ((p : ZMod (N * l ^ L)) * (p : ZMod (N * l ^ L))⁻¹) = 1 := ZMod.coe_mul_inv_eq_one p h
    have h1 := congrArg (ZMod.castHom hdvd (ZMod l)) hu
    rw [map_mul, map_one, map_natCast] at h1
    have h2 : ((bar l L N p : ℤ) : ZMod l) = ZMod.castHom hdvd (ZMod l) ((p : ZMod (N * l ^ L))⁻¹) := by
      unfold bar
      rw [Int.cast_natCast, ZMod.natCast_val]
      rfl
    rw [h2, mul_comm]
    exact h1

theorem UpperTheory.V.Z.Kato.Nb.sTopT :
    UpperTheory.V.Z.Kato.Nb.STopT := by
  intro Ω _ _ _ ε X l _ N p _ _ x c d w g hH hP hcop hLw hLift n r
  obtain ⟨ws, hws⟩ := hLw
  have api := sApi Ω ε X l
  have inv := sInvApi Ω ε X l N w
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨fun σ _ => (inv 0).2.2.2.2.2.2.1 _, fun σ _ τ _ => (api 0).2.2.2.2.2.2.2.2.1 _ _,
      ⟨∅, fun σ _ τ _ _ => (api 0).2.2.2.2.2.2.2.2.1 _ _⟩⟩
  · have hl2 : l ≠ 2 := hH.odd
    have hlp : l.Prime := Fact.out
    have hL0 : r + n ≠ 0 := by omega
    have hpl : p.Coprime l := Nat.Coprime.coprime_dvd_right ⟨N * c * d, by ring⟩ hcop
    have hpN : p.Coprime N := Nat.Coprime.coprime_dvd_right ⟨l * c * d, by ring⟩ hcop
    have hpc : p.Coprime c := Nat.Coprime.coprime_dvd_right ⟨l * N * d, by ring⟩ hcop
    have hpNL : p.Coprime (N * l ^ (r + n)) := Nat.Coprime.mul_right hpN (Nat.Coprime.pow_right _ hpl)
    have hcN : c.Coprime N := Nat.Coprime.coprime_dvd_right ⟨6 * l, by ring⟩ hH.cc
    have hcl : c.Coprime l := Nat.Coprime.coprime_dvd_right ⟨6 * N, by ring⟩ hH.cc
    have hdN : d.Coprime N := Nat.Coprime.coprime_dvd_right ⟨6 * l, by ring⟩ hH.cd
    have hdl : d.Coprime l := Nat.Coprime.coprime_dvd_right ⟨6 * N, by ring⟩ hH.cd
    have hpd : p.Coprime d := Nat.Coprime.coprime_dvd_right ⟨l * N * c, by ring⟩ hcop
    have hM0 : N * l ^ (r + n) * p ≠ 0 :=
      mul_ne_zero (mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hlp.ne_zero)) (NeZero.ne p)
    haveI : NeZero (N * l ^ (r + n) * p) := ⟨hM0⟩
    have hMeq : lvT l n r N p = N * (N * l ^ (r + n) * p) := by
      unfold lvT
      ring
    haveI : NeZero (lvT l n r N p) := ⟨by rw [hMeq]; exact mul_ne_zero (NeZero.ne N) hM0⟩
    have hLev : Lev l n N (N * l ^ (r + n) * p) (lvT l n r N p) g :=
      ⟨hMeq, ⟨l ^ (r + n) * p, by ring⟩, ⟨N * l ^ r * p, by ring⟩, hn, hH.cop, hH.g0⟩
    have hLv : Lv c d (N * l ^ (r + n) * p) :=
      ⟨Nat.pos_of_ne_zero hM0,
        Nat.Coprime.mul_right (Nat.Coprime.mul_right hcN (Nat.Coprime.pow_right _ hcl)) hpc.symm,
        Nat.Coprime.mul_right (Nat.Coprime.mul_right hdN (Nat.Coprime.pow_right _ hdl)) hpd.symm⟩
    have hdvdl : l ∣ N * l ^ (r + n) * p := Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self l hL0) N) p
    have hbp : ((bar l (r + n) N p : ℤ) : ZMod l) * (p : ZMod l) = 1 := bar_mul l (r + n) N p hL0 hpNL
    have hlL : ((l : ZMod l)) ^ (r + n) = 0 := by
      rw [ZMod.natCast_self]
      exact zero_pow hL0
    have hN0 : (N : ZMod l) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hlp).mp hH.cop
    have ha0 : (((bar l (r + n) N p * ((N : ℤ) + ((x.val : ℕ) : ℤ) * ((topT l (r + n) N : ℕ) : ℤ) * (l : ℤ) ^ (r + n)) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod l) ≠ 0 := by
      have e : (((bar l (r + n) N p * ((N : ℤ) + ((x.val : ℕ) : ℤ) * ((topT l (r + n) N : ℕ) : ℤ) * (l : ℤ) ^ (r + n)) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod l) = (N : ZMod l) := by
        push_cast
        linear_combination (N : ZMod l) * hbp + (((bar l (r + n) N p : ℤ) : ZMod l) * ((x.val : ℕ) : ZMod l) * ((topT l (r + n) N : ℕ) : ZMod l) * (p : ZMod l) + (N : ZMod l)) * hlL
      rw [e]
      exact hN0
    have hb1 : (((bar l (r + n) N p * (N : ℤ) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod l) ≠ 0 := by
      have e : (((bar l (r + n) N p * (N : ℤ) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod l) = (N : ZMod l) := by
        push_cast
        linear_combination (N : ZMod l) * hbp + (N : ZMod l) * hlL
      rw [e]
      exact hN0
    let x₀ : Row (N * l ^ (r + n) * p) :=
      ![(((bar l (r + n) N p * ((N : ℤ) + ((x.val : ℕ) : ℤ) * ((topT l (r + n) N : ℕ) : ℤ) * (l : ℤ) ^ (r + n)) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod (N * l ^ (r + n) * p)),
        (((0 : ℤ)) : ZMod (N * l ^ (r + n) * p))]
    let y₀ : Row (N * l ^ (r + n) * p) :=
      ![(((bar l (r + n) N p * ((topT l (r + n) N : ℕ) : ℤ) * (l : ℤ) ^ (r + n) * (p : ℤ)) : ℤ) : ZMod (N * l ^ (r + n) * p)),
        (((bar l (r + n) N p * (N : ℤ) * (p : ℤ) + (N : ℤ) * (l : ℤ) ^ (r + n)) : ℤ) : ZMod (N * l ^ (r + n) * p))]
    have hOk : Ok x₀ y₀ := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have h1 := congrFun h 0
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat] at h1
        exact two_ne l _ hl2 hdvdl _ ha0 h1
      · have h1 := congrFun h 1
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat] at h1
        exact two_ne l _ hl2 hdvdl _ hb1 h1
    have hx : ∀ i : Fin 2, ∃ j : ℤ, ixUT l (r + n) N p x i = toQ (N * l ^ (r + n) * p) x₀ i + j := by
      intro i
      fin_cases i
      · exact frac_eq _ _ rfl _
      · exact frac_eq _ _ rfl _
    have hy : ∀ i : Fin 2, ∃ j : ℤ, ixVT l (r + n) N p i = toQ (N * l ^ (r + n) * p) y₀ i + j := by
      intro i
      fin_cases i
      · exact frac_eq _ _ rfl _
      · exact frac_eq _ _ rfl _
    obtain ⟨β, hβ, hcg⟩ := sTopRel Ω ε X l n N (N * l ^ (r + n) * p) (lvT l n r N p) w g hLev hLift c d ws hws hLv
      x₀ y₀ hOk _ _ hx hy
    exact sTopCocG Ω ε X l n N _ _ w g hLev hLift x₀ y₀ hOk (ws n _) (hws.coc n _ hLv) _ β hβ hcg
