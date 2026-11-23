import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CohApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.TopRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.RepSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SXiCoh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.XiDist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.XiScal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCycZ

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.NormOneTraceTorsion

private def rw0 (M : ℕ) (v : Fin 2 → ℤ) : Row M := fun i => (v i : ZMod M)

private theorem val_cast {M D : ℕ} [NeZero M] (h : D ∣ M) (a : ℤ) : (((a : ZMod M).val : ℕ) : ZMod D) = (a : ZMod D) := by
  rw [ZMod.natCast_val, ZMod.cast_intCast h]

private theorem exists_int_div_eq_toQ_rw0_add (M : ℕ) [NeZero M] (v : Fin 2 → ℤ) (i : Fin 2) : ∃ j : ℤ, (v i : ℚ) / (M : ℚ) = toQ M (rw0 M v) i + j := by
  refine ⟨v i / (M : ℤ), ?_⟩
  have hM : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have h1 : (((v i : ZMod M).val : ℕ) : ℤ) = v i % (M : ℤ) := ZMod.val_intCast (v i)
  have h2 : v i % (M : ℤ) + (M : ℤ) * (v i / (M : ℤ)) = v i := Int.emod_add_mul_ediv _ _
  rw [← h1] at h2
  have h3 := congrArg (fun z : ℤ => (z : ℚ)) h2
  push_cast at h3
  simp only [toQ, rw0]
  rw [← h3, add_div, mul_div_cancel_left₀ _ hM]

private theorem dn_rw0_mul_eq_rw0 (k M : ℕ) (v : Fin 2 → ℤ) : dn k M (rw0 (k * M) v) = rw0 M v := by
  funext i
  simp only [dn, rw0, map_intCast]

private theorem two_ne {l M : ℕ} [Fact l.Prime] (hl : l ≠ 2) (h : l ∣ M) (v : Fin 2 → ℤ) (i : Fin 2) (hv : (v i : ZMod l) ≠ 0) :
    (2 : ZMod M) • rw0 M v ≠ 0 := by
  intro h0
  have h1 := congrFun h0 i
  simp only [Pi.smul_apply, smul_eq_mul, rw0, Pi.zero_apply] at h1
  have h2 := congrArg (ZMod.castHom h (ZMod l)) h1
  simp only [map_mul, map_intCast, map_ofNat, map_zero] at h2
  have h3 : (2 : ZMod l) ≠ 0 := by
    intro h4
    have h5 : l ∣ 2 := (ZMod.natCast_eq_zero_iff 2 l).mp (by exact_mod_cast h4)
    exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h5)
  exact hv ((mul_eq_zero.mp h2).resolve_left h3)

private def rU (l L N p : ℕ) (x : ZMod N) : Fin 2 → ℤ :=
  ![bar l L N p * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L) * p + N * (l : ℤ) ^ L, 0]

private def rV (l L N p : ℕ) : Fin 2 → ℤ :=
  ![bar l L N p * (topT l L N : ℤ) * (l : ℤ) ^ L * p, bar l L N p * N * p + N * (l : ℤ) ^ L]

private theorem ixUT_eq (l L N p : ℕ) (x : ZMod N) (i : Fin 2) :
    ixUT l L N p x i = (rU l L N p x i : ℚ) / ((N * l ^ L * p : ℕ) : ℚ) := by
  fin_cases i <;> rfl

private theorem ixVT_eq (l L N p : ℕ) (i : Fin 2) : ixVT l L N p i = (rV l L N p i : ℚ) / ((N * l ^ L * p : ℕ) : ℚ) := by
  fin_cases i <;> rfl

private theorem bar_mul {l L N p D : ℕ} [NeZero (N * l ^ L)] (hp : Nat.Coprime p (N * l ^ L)) (h : D ∣ N * l ^ L) :
    (bar l L N p : ZMod D) * p = 1 := by
  have h1 : (p : ZMod (N * l ^ L)) * (p : ZMod (N * l ^ L))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime p _).mpr hp)
  have h2 := congrArg (ZMod.castHom h (ZMod D)) h1
  simp only [map_mul, map_natCast, map_one] at h2
  simp only [bar]
  push_cast
  rw [ZMod.natCast_val, mul_comm]
  exact h2

private theorem rows_l {l L N p : ℕ} [Fact l.Prime] [NeZero N] (x : ZMod N) (hL : 1 ≤ L) (hp : Nat.Coprime p (N * l ^ L)) :
    (rU l L N p x 0 : ZMod l) = N ∧ (rV l L N p 1 : ZMod l) = N ∧ rU l L N p x 1 = 0 := by
  haveI : NeZero (N * l ^ L) := ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
  have hb : (bar l L N p : ZMod l) * p = 1 := bar_mul hp (Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N)
  have h0 : (l : ZMod l) ^ L = 0 := by rw [ZMod.natCast_self, zero_pow (by omega)]
  refine ⟨?_, ?_, rfl⟩
  · simp only [rU, Matrix.cons_val_zero]
    push_cast
    rw [h0]
    linear_combination (N : ZMod l) * hb
  · simp only [rV, Matrix.cons_val_one, Matrix.cons_val_zero]
    push_cast
    rw [h0]
    linear_combination (N : ZMod l) * hb

private theorem crt {m n : ℕ} (h : Nat.Coprime m n) {a b : ℤ} (h1 : (a : ZMod m) = b) (h2 : (a : ZMod n) = b) :
    (a : ZMod (m * n)) = b := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1 h2 ⊢
  push_cast
  exact (Nat.isCoprime_iff_coprime.mpr h).mul_dvd h1 h2

private theorem topT_succ {l L N : ℕ} [NeZero N] (h : Nat.Coprime l N) :
    (topT l (L + 1) N : ZMod (N * l ^ L)) * (l : ZMod (N * l ^ L)) ^ (L + 1) = (topT l L N : ZMod (N * l ^ L)) * (l : ZMod (N * l ^ L)) ^ L := by
  have key : ∀ s : ℕ, ((topT l s N : ℕ) : ZMod N) * (l : ZMod N) ^ s = 1 := by
    intro s
    have h1 : ((l ^ s : ℕ) : ZMod N) * ((l ^ s : ℕ) : ZMod N)⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime _ _).mpr (Nat.Coprime.pow_left s h))
    push_cast at h1
    simp only [topT, ZMod.natCast_zmod_val]
    rw [mul_comm]
    exact h1
  have e := crt (m := N) (n := l ^ L) (Nat.Coprime.pow_right L h.symm)
    (a := (topT l (L + 1) N : ℤ) * (l : ℤ) ^ (L + 1)) (b := (topT l L N : ℤ) * (l : ℤ) ^ L) ?_ ?_
  · push_cast at e
    exact e
  · push_cast
    rw [key, key]
  · push_cast
    have hz : (l : ZMod (l ^ L)) ^ L = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [pow_succ, hz]
    ring

private theorem eval_succ_eq_smul_of_inv_p_of_k_eq_one {R : Type*} [CommRing R] (b1 b0 t1 t0 N l xv p k : R) (L : ℕ)
    (hb1 : b1 * p = 1) (hb0 : b0 * p = 1) (ht : t1 * l ^ (L + 1) = t0 * l ^ L) (hz : N * l ^ L = 0) (k1 : k = 1) :
    b1 * (N + xv * t1 * l ^ (L + 1)) * p + N * l ^ (L + 1) = k * (b0 * (N + xv * t0 * l ^ L) * p + N * l ^ L) := by
  linear_combination (N + xv * t1 * l ^ (L + 1)) * hb1 - (N + xv * t0 * l ^ L) * hb0 + xv * ht + (l - 1) * hz -
    (b0 * (N + xv * t0 * l ^ L) * p + N * l ^ L) * k1

private theorem eval_succ_eq_smul_of_p_eq_zero_of_k_eq_l {R : Type*} [CommRing R] (b1 b0 t1 t0 N l xv p k : R) (L : ℕ)
    (hp : p = 0) (k2 : k = l) :
    b1 * (N + xv * t1 * l ^ (L + 1)) * p + N * l ^ (L + 1) = k * (b0 * (N + xv * t0 * l ^ L) * p + N * l ^ L) := by
  linear_combination (b1 * (N + xv * t1 * l ^ (L + 1)) - k * b0 * (N + xv * t0 * l ^ L)) * hp - N * l ^ L * k2

private theorem twist_succ_eq_smul_of_inv_p_of_k_eq_one {R : Type*} [CommRing R] (b1 b0 t1 t0 l p k : R) (L : ℕ)
    (hb1 : b1 * p = 1) (hb0 : b0 * p = 1) (ht : t1 * l ^ (L + 1) = t0 * l ^ L) (k1 : k = 1) :
    b1 * t1 * l ^ (L + 1) * p = k * (b0 * t0 * l ^ L * p) := by
  linear_combination t1 * l ^ (L + 1) * hb1 + ht - t0 * l ^ L * hb0 - t0 * l ^ L * b0 * p * k1

private theorem twist_succ_eq_smul_of_p_eq_zero {R : Type*} [CommRing R] (b1 b0 t1 t0 l p k : R) (L : ℕ) (hp : p = 0) :
    b1 * t1 * l ^ (L + 1) * p = k * (b0 * t0 * l ^ L * p) := by
  linear_combination (b1 * t1 * l ^ (L + 1) - k * b0 * t0 * l ^ L) * hp

private theorem const_succ_eq_smul_of_inv_p_of_k_eq_one {R : Type*} [CommRing R] (b1 b0 N l p k : R) (L : ℕ)
    (hb1 : b1 * p = 1) (hb0 : b0 * p = 1) (hz : N * l ^ L = 0) (k1 : k = 1) :
    b1 * N * p + N * l ^ (L + 1) = k * (b0 * N * p + N * l ^ L) := by
  linear_combination N * hb1 - N * hb0 + (l - 1) * hz - (b0 * N * p + N * l ^ L) * k1

private theorem const_succ_eq_smul_of_p_eq_zero_of_k_eq_l {R : Type*} [CommRing R] (b1 b0 N l p k : R) (L : ℕ) (hp : p = 0) (k2 : k = l) :
    b1 * N * p + N * l ^ (L + 1) = k * (b0 * N * p + N * l ^ L) := by
  linear_combination (b1 * N - k * b0 * N) * hp - N * l ^ L * k2

private theorem rows_succ {l L N p k : ℕ} [Fact l.Prime] [NeZero N] (x : ZMod N) (h : Nat.Coprime l N)
    (hp : Nat.Coprime p (N * l ^ (L + 1))) (k1 : (k : ZMod (N * l ^ L)) = 1) (k2 : (k : ZMod p) = l) :
    rw0 (N * l ^ L * p) (rU l (L + 1) N p x) = (k : ZMod (N * l ^ L * p)) • rw0 (N * l ^ L * p) (rU l L N p x) ∧
    rw0 (N * l ^ L * p) (rV l (L + 1) N p) = (k : ZMod (N * l ^ L * p)) • rw0 (N * l ^ L * p) (rV l L N p) := by
  haveI : NeZero (N * l ^ (L + 1)) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
  haveI : NeZero (N * l ^ L) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
  have hdv : N * l ^ L ∣ N * l ^ (L + 1) := Nat.mul_dvd_mul_left N (pow_dvd_pow l (Nat.le_succ L))
  have hp0 : Nat.Coprime p (N * l ^ L) := Nat.Coprime.coprime_dvd_right hdv hp
  have hb1 := bar_mul (D := N * l ^ L) hp hdv
  have hb0 := bar_mul (D := N * l ^ L) hp0 dvd_rfl
  have ht := topT_succ (L := L) h
  have hz : (N : ZMod (N * l ^ L)) * (l : ZMod (N * l ^ L)) ^ L = 0 := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, ZMod.natCast_self]
  have hpz : (p : ZMod p) = 0 := ZMod.natCast_self p
  have c1 : ∀ a b : ℤ, (a : ZMod (N * l ^ L)) = (k : ZMod (N * l ^ L)) * (b : ZMod (N * l ^ L)) →
      (a : ZMod p) = (k : ZMod p) * (b : ZMod p) →
      (a : ZMod (N * l ^ L * p)) = (k : ZMod (N * l ^ L * p)) * (b : ZMod (N * l ^ L * p)) := by
    intro a b h1 h2
    have e := crt hp0.symm (a := a) (b := (k : ℤ) * b) (by push_cast; exact h1) (by push_cast; exact h2)
    rw [e]
    push_cast
    ring
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩ <;> fin_cases i
  · show ((rU l (L + 1) N p x 0 : ℤ) : ZMod (N * l ^ L * p)) = (k : ZMod _) * ((rU l L N p x 0 : ℤ) : ZMod _)
    apply c1 <;> simp only [rU, Matrix.cons_val_zero] <;> push_cast
    · exact eval_succ_eq_smul_of_inv_p_of_k_eq_one _ _ _ _ _ _ _ _ _ L hb1 hb0 ht hz k1
    · exact eval_succ_eq_smul_of_p_eq_zero_of_k_eq_l _ _ _ _ _ _ _ _ _ L hpz k2
  · show ((rU l (L + 1) N p x 1 : ℤ) : ZMod (N * l ^ L * p)) = (k : ZMod _) * ((rU l L N p x 1 : ℤ) : ZMod _)
    simp [rU]
  · show ((rV l (L + 1) N p 0 : ℤ) : ZMod (N * l ^ L * p)) = (k : ZMod _) * ((rV l L N p 0 : ℤ) : ZMod _)
    apply c1 <;> simp only [rV, Matrix.cons_val_zero] <;> push_cast
    · exact twist_succ_eq_smul_of_inv_p_of_k_eq_one _ _ _ _ _ _ _ L hb1 hb0 ht k1
    · exact twist_succ_eq_smul_of_p_eq_zero _ _ _ _ _ _ _ L hpz
  · show ((rV l (L + 1) N p 1 : ℤ) : ZMod (N * l ^ L * p)) = (k : ZMod _) * ((rV l L N p 1 : ℤ) : ZMod _)
    apply c1 <;> simp only [rV, Matrix.cons_val_one, Matrix.head_cons] <;> push_cast
    · exact const_succ_eq_smul_of_inv_p_of_k_eq_one _ _ _ _ _ _ L hb1 hb0 hz k1
    · exact const_succ_eq_smul_of_p_eq_zero_of_k_eq_l _ _ _ _ _ _ L hpz k2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private theorem down (hA : SApi) (hC : SCohApi) (hM : SXiMul) (hX : SXiCoh) (hD : SXiDist) (hS : SXiScal) (hG : SSlD)
    (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M M' w c d : ℕ) [NeZero N] [NeZero M₀] [NeZero M] [NeZero M'] [NeZero (l * M₀)]
    (g : SL(2, ℤ)) (lev : Lev l n N M₀ M g) (hL : LiftsWith X l N w (cL X l N w)) (h : M ∣ M') (e : M' = N * (l * M₀))
    (ws) (law : Laws X l c d ws) (lv : Lv c d (l * M₀)) (x' y' : Row (l * M₀)) (x y : Row M₀) (ok' : Ok x' y') (ok : Ok x y)
    (bas : Bas l N x' y') (ν : (ZMod M)ˣ) (n1 : ((ν : ZMod M).val : ZMod N) = 1) (n2 : ((ν : ZMod M).val : ZMod (l ^ n)) = 1)
    (ex : dn l M₀ x' = ((ν : ZMod M).val : ZMod M₀) • x) (ey : dn l M₀ y' = ((ν : ZMod M).val : ZMod M₀) • y)
    (A : Type) [CommGroup A] (π : (ZMod M)ˣ →* A) :
    CohB X l N w n (fun s => (π (cycM M s))⁻¹)
      (fun s t => Xi X l (n + 1) N (l * M₀) M' w g x' y'
        (fun z => π (Units.map (ZMod.castHom h (ZMod M)).toMonoidHom z) = t) (ws (n + 1) (l * M₀) s))
      (fun s t => Xi X l n N M₀ M w g x y (fun z => π z = t * π ν ^ 2) (ws n M₀ s)) := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hCA := hC Ω ε X l N w n hN A (fun s => (π (cycM M s))⁻¹)
  have hE := hCA.1
  have hAp := hA Ω ε X l n
  have lev' : Lev l n N (l * M₀) M' g :=
    ⟨e, dvd_mul_of_dvd_right lev.dN l, dvd_mul_of_dvd_right lev.dl l, lev.pos, lev.cop, lev.g0⟩
  have hκ : (fun s : Ω ≃ₐ[ℚ] Ω => ((π.comp (Units.map (ZMod.castHom h (ZMod M)).toMonoidHom)) (cycM M' s))⁻¹) =
      (fun s : Ω ≃ₐ[ℚ] Ω => (π (cycM M s))⁻¹) := by
    funext s
    have e4 := ((hG Ω ε X 1 one_pos).2.2.2.2.2.2.2 M' s).2.2.2.2 M h
    exact congrArg (fun u => (π u)⁻¹) e4
  have C1 := hCA.2.1
    (fun s t => Xi X l (n + 1) N (l * M₀) M' w g x' y'
      (fun z => π (Units.map (ZMod.castHom h (ZMod M)).toMonoidHom z) = t) (ws (n + 1) (l * M₀) s))
    (fun s t => Xi X l n N (l * M₀) M' w g x' y'
      (fun z => π (Units.map (ZMod.castHom h (ZMod M)).toMonoidHom z) = t) (ws (n + 1) (l * M₀) s))
    (fun s t => (hM Ω ε X l n N (l * M₀) M' w g lev' x' y' ok' _).2.2.1 _)
  have C2 := hX Ω ε X l n N (l * M₀) M' w g lev' hL x' y' ok' A
    (π.comp (Units.map (ZMod.castHom h (ZMod M)).toMonoidHom)) _ _ (law.red n (l * M₀) lv)
  rw [hκ] at C2
  have C3 := hCA.2.1
    (fun s t => Xi X l n N (l * M₀) M' w g x' y'
      (fun z => π (Units.map (ZMod.castHom h (ZMod M)).toMonoidHom z) = t) (ws n (l * M₀) s))
    (fun s t => Xi X l n N M₀ M w g (((ν : ZMod M).val : ZMod M₀) • x) (((ν : ZMod M).val : ZMod M₀) • y)
      (fun z => π z = t) (pushD X l M₀ (ws n (l * M₀) s)))
    (fun s t => by
      have h3 := hD Ω ε X l n N M₀ M w g lev M' h e x' y' bas (fun z => π z = t) (ws n (l * M₀) s)
      rw [ex, ey] at h3
      exact h3)
  have hdv : ∀ j : ℕ, (l : ℤ_[l]) ^ n ∣ (((ν : ZMod M).val : ℕ) : ℤ_[l]) ^ j - 1 := by
    intro j
    have h1 : ((l ^ n : ℕ) : ℤ) ∣ (((ν : ZMod M).val : ℕ) : ℤ) - 1 :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (((ν : ZMod M).val : ℕ) : ℤ) (l ^ n)).mp (by push_cast; exact n2.symm)
    have h2 : ((l ^ n : ℕ) : ℤ) ∣ (((ν : ZMod M).val : ℕ) : ℤ) ^ j - 1 := by
      have h4 := sub_dvd_pow_sub_pow ((((ν : ZMod M).val : ℕ) : ℤ)) 1 j
      rw [one_pow] at h4
      exact dvd_trans h1 h4
    have h3 := map_dvd (Int.castRingHom ℤ_[l]) h2
    simpa using h3
  have hsc : ∀ (k : ℤ_[l]) (F : X.Fn l), (l : ℤ_[l]) ^ n ∣ k - 1 → CgF X l n (k • F) F := by
    intro k F hk u
    have h5 := hAp.2.2.2.2.1 k 1 (F u) hk
    simpa using h5
  have hpred : ∀ t : A, (fun z : (ZMod M)ˣ => π (z * ν⁻¹ ^ 2) = t) = (fun z => π z = t * π ν ^ 2) := by
    intro t
    funext z
    rw [map_mul, map_pow, map_inv, inv_pow, mul_inv_eq_iff_eq_mul]
  have C4 := hCA.2.1
    (fun s t => Xi X l n N M₀ M w g (((ν : ZMod M).val : ZMod M₀) • x) (((ν : ZMod M).val : ZMod M₀) • y)
      (fun z => π z = t) (pushD X l M₀ (ws n (l * M₀) s)))
    (fun s t => Xi X l n N M₀ M w g x y (fun z => π z = t * π ν ^ 2) (pushD X l M₀ (ws n (l * M₀) s)))
    (fun s t => by
      have hs := hS Ω ε X l n N M₀ M w g lev x y (fun z => π z = t) (pushD X l M₀ (ws n (l * M₀) s)) ν n1
      beta_reduce at hs
      rw [hpred t] at hs
      exact hAp.1.trans (hAp.1.symm (hsc _ _ (hdv w))) (hAp.1.trans hs (hsc _ _ (hdv 2))))
  have C5 := hX Ω ε X l n N M₀ M w g lev hL x y ok A π _ _ (law.dist n l M₀ lv)
  have C6 := hCA.2.2.2.1 1 (π ν ^ 2) _ _ C5
  simp only [one_smul] at C6
  exact hE.trans C1 (hE.trans C2 (hE.trans C3 (hE.trans C4 C6)))

private theorem topXi (hT : STopRel) (hB : SBridge)
    (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w c d : ℕ) [NeZero N] [NeZero M₀] [NeZero M]
    (g : SL(2, ℤ)) (lev : Lev l n N M₀ M g) (hL : LiftsWith X l N w (cL X l N w))
    (ws) (law : Laws X l c d ws) (lv : Lv c d M₀) (U V : Fin 2 → ℤ) (ok : Ok (rw0 M₀ U) (rw0 M₀ V)) (x' y' : Fin 2 → ℚ)
    (hx : ∀ i, x' i = (U i : ℚ) / (M₀ : ℚ)) (hy : ∀ i, y' i = (V i : ℚ) / (M₀ : ℚ))
    (A : Type) [Group A] [DecidableEq A] (π : (ZMod M)ˣ →* A) :
    CohB X l N w n (fun s => (π (cycM M s))⁻¹) (GlobalTheory.KA.push π (shB X l M (clsG X l n N M w c d g x' y')))
      fun s t => Xi X l n N M₀ M w g (rw0 M₀ U) (rw0 M₀ V) (fun z => π z = t) (ws n M₀ s) := by
  have hx' : ∀ i, ∃ j : ℤ, x' i = toQ M₀ (rw0 M₀ U) i + j := fun i => by
    obtain ⟨j, hj⟩ := exists_int_div_eq_toQ_rw0_add M₀ U i
    exact ⟨j, by rw [hx i, hj]⟩
  have hy' : ∀ i, ∃ j : ℤ, y' i = toQ M₀ (rw0 M₀ V) i + j := fun i => by
    obtain ⟨j, hj⟩ := exists_int_div_eq_toQ_rw0_add M₀ V i
    exact ⟨j, by rw [hy i, hj]⟩
  obtain ⟨β, hβ, hσ⟩ := hT Ω ε X l n N M₀ M w g lev hL c d ws law lv (rw0 M₀ U) (rw0 M₀ V) ok x' y' hx' hy'
  exact hB Ω ε X l n N M₀ M w g lev hL (rw0 M₀ U) (rw0 M₀ V) ok (ws n M₀) (law.coc n M₀ lv) _ β hβ hσ A π

private def rdH (l n r N p : ℕ) : (ZMod (lvT l n r N p))ˣ →* (ZMod p)ˣ × (ZMod (l ^ r))ˣ :=
  (Units.map (ZMod.castHom (Dvd.intro_left _ rfl : p ∣ lvT l n r N p) (ZMod p)).toMonoidHom).prod
   (Units.map (ZMod.castHom ((Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) (N * N)).mul_right p)
     (ZMod (l ^ r))).toMonoidHom)

private theorem rdH_comp (l n r N p : ℕ) (h : lvT l n r N p ∣ lvT l (n + 1) r N p) (z : (ZMod (lvT l (n + 1) r N p))ˣ) :
    rdH l n r N p (Units.map (ZMod.castHom h (ZMod (lvT l n r N p))).toMonoidHom z) = rdH l (n + 1) r N p z := by
  have e1 : ∀ {a b c : ℕ} (h1 : b ∣ a) (h2 : c ∣ b) (h3 : c ∣ a) (z : ZMod a),
      ZMod.castHom h2 (ZMod c) (ZMod.castHom h1 (ZMod b) z) = ZMod.castHom h3 (ZMod c) z :=
    fun h1 h2 h3 z => RingHom.congr_fun (RingHom.ext_zmod ((ZMod.castHom h2 _).comp (ZMod.castHom h1 _)) (ZMod.castHom h3 _)) z
  have d2 : l ^ r ∣ lvT l n r N p :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) (N * N)) p
  have d3 : l ^ r ∣ lvT l (n + 1) r N p := dvd_trans d2 h
  have q2 : p ∣ lvT l n r N p := Dvd.intro_left _ rfl
  have q3 : p ∣ lvT l (n + 1) r N p := Dvd.intro_left _ rfl
  apply Prod.ext <;> apply Units.ext <;>
    simp only [rdH, MonoidHom.prod_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  · exact e1 h q2 q3 _
  · erw [Units.coe_map, Units.coe_map, Units.coe_map]
    exact e1 h d2 d3 _

private theorem rdH_cyc (hG : SSlD) (hZ : SCycZ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N p : ℕ) [NeZero N] [NeZero p] :
    (fun s : Ω ≃ₐ[ℚ] Ω => (rdH l n r N p (cycM (lvT l n r N p) s))⁻¹) = kT l r p := by
  funext s
  have h := ((hG Ω ε X N (Nat.pos_of_ne_zero (NeZero.ne N))).2.2.2.2.2.2.2 (lvT l n r N p) s).2.2.2.2
  unfold kT
  rw [(hZ Ω l r s).1]
  exact Prod.ext (congrArg Inv.inv (h p _)) (congrArg Inv.inv (h (l ^ r) _))

private theorem main (hA : SApi) (hC : SCohApi) (hM : SXiMul) (hX : SXiCoh) (hD : SXiDist) (hS : SXiScal) (hG : SSlD)
    (hT : STopRel) (hB : SBridge) (hZ : SCycZ) : KatoTwistedClassCompatibleModPowers := by
  unfold KatoTwistedClassCompatibleModPowers
  intro Ω _ _ _ ε X l _ N p _ _ x c d w g hyp hpp hcop hws hL n r
  obtain ⟨ws, law⟩ := hws
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hCA := hC Ω ε X l N w n hN ((ZMod p)ˣ × (ZMod (l ^ r))ˣ) (kT l r p)
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    exact hCA.2.2.2.2.2.1 _ _
  have hE := hCA.1
  have lp : l.Prime := Fact.out
  haveI : NeZero l := ⟨lp.ne_zero⟩
  have hl0 : l ≠ 0 := lp.ne_zero
  have hpl : Nat.Coprime p l := Nat.Coprime.coprime_dvd_right
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right l N) c) d) hcop
  have hpN : Nat.Coprime p N := Nat.Coprime.coprime_dvd_right
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left N l) c) d) hcop
  have hpc : Nat.Coprime p c := Nat.Coprime.coprime_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left c (l * N)) d) hcop
  have hpd : Nat.Coprime p d := Nat.Coprime.coprime_dvd_right (dvd_mul_left d (l * N * c)) hcop
  have hpNL : ∀ j, Nat.Coprime p (N * l ^ j) := fun j => Nat.Coprime.mul_right hpN (Nat.Coprime.pow_right j hpl)
  have cpq : ∀ q j, Nat.Coprime q (6 * l * N) → Nat.Coprime p q →
      Nat.Coprime q (N * l ^ j * p) ∧ Nat.Coprime q (l * (N * l ^ j * p)) := by
    intro q j hq hpq
    have qN : Nat.Coprime q N := Nat.Coprime.coprime_dvd_right (dvd_mul_left N (6 * l)) hq
    have ql : Nat.Coprime q l := Nat.Coprime.coprime_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left l 6) N) hq
    have h1 : Nat.Coprime q (N * l ^ j * p) :=
      Nat.Coprime.mul_right (Nat.Coprime.mul_right qN (Nat.Coprime.pow_right j ql)) hpq.symm
    exact ⟨h1, Nat.Coprime.mul_right ql h1⟩
  have pos0 : ∀ j, 0 < N * l ^ j * p := fun j =>
    Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hl0)) (NeZero.ne p))
  have lvM : ∀ j, Lv c d (N * l ^ j * p) := fun j => ⟨pos0 j, (cpq c j hyp.cc hpc).1, (cpq d j hyp.cd hpd).1⟩
  have lvM1 : ∀ j, Lv c d (l * (N * l ^ j * p)) := fun j =>
    ⟨Nat.mul_pos lp.pos (pos0 j), (cpq c j hyp.cc hpc).2, (cpq d j hyp.cd hpd).2⟩
  have dl0 : l ^ n ∣ N * l ^ (r + n) * p :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow l (Nat.le_add_left n r)) N) p
  have lev0 : Lev l n N (N * l ^ (r + n) * p) (lvT l n r N p) g :=
    ⟨by simp only [lvT]; ring, Dvd.dvd.mul_right (dvd_mul_right N _) p, dl0, hn, hyp.cop, hyp.g0⟩
  have lev1 : Lev l (n + 1) N (l * (N * l ^ (r + n) * p)) (lvT l (n + 1) r N p) g :=
    ⟨by simp only [lvT]; ring, dvd_mul_of_dvd_right (Dvd.dvd.mul_right (dvd_mul_right N _) p) l,
     by rw [pow_succ']; exact Nat.mul_dvd_mul_left l dl0, by omega, hyp.cop, hyp.g0⟩
  have e1 : lvT l (n + 1) r N p = N * (l * (N * l ^ (r + n) * p)) := by simp only [lvT]; ring
  haveI i0 : NeZero (N * l ^ (r + n) * p) := ⟨(pos0 _).ne'⟩
  haveI i1 : NeZero (l * (N * l ^ (r + n) * p)) := ⟨(Nat.mul_pos lp.pos (pos0 _)).ne'⟩
  haveI i2 : NeZero (lvT l n r N p) := ⟨by rw [lev0.eq]; exact mul_ne_zero (NeZero.ne N) (pos0 _).ne'⟩
  haveI i3 : NeZero (lvT l (n + 1) r N p) := ⟨by rw [e1]; exact mul_ne_zero (NeZero.ne N) (NeZero.ne _)⟩
  have hNl : (N : ZMod l) ≠ 0 := by
    intro h0
    exact (Nat.Prime.coprime_iff_not_dvd lp).mp hyp.cop ((ZMod.natCast_eq_zero_iff N l).mp h0)
  have okOf : ∀ (Mx : ℕ) (U V : Fin 2 → ℤ), l ∣ Mx → (U 0 : ZMod l) ≠ 0 → (V 1 : ZMod l) ≠ 0 →
      Ok (rw0 Mx U) (rw0 Mx V) := by
    intro Mx U V hd hU hV
    exact ⟨two_ne hyp.odd hd U 0 hU, two_ne hyp.odd hd V 1 hV⟩
  have rl0 := rows_l (l := l) (L := r + n) (N := N) (p := p) x (by omega) (hpNL _)
  have rl1 := rows_l (l := l) (L := r + n + 1) (N := N) (p := p) x (by omega) (hpNL _)
  have ok0 := okOf (N * l ^ (r + n) * p) (rU l (r + n) N p x) (rV l (r + n) N p)
    (Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N) p)
    (by rw [rl0.1]; exact hNl) (by rw [rl0.2.1]; exact hNl)
  have ok1 := okOf (l * (N * l ^ (r + n) * p)) (rU l (r + n + 1) N p x) (rV l (r + n + 1) N p)
    (dvd_mul_right l _) (by rw [rl1.1]; exact hNl) (by rw [rl1.2.1]; exact hNl)
  have TA := topXi hT hB X l n N (N * l ^ (r + n) * p) (lvT l n r N p) w c d g lev0 hL ws law (lvM _)
    (rU l (r + n) N p x) (rV l (r + n) N p) ok0 (ixUT l (r + n) N p x) (ixVT l (r + n) N p)
    (ixUT_eq l (r + n) N p x) (ixVT_eq l (r + n) N p) _ (rdH l n r N p)
  rw [rdH_cyc hG hZ X l n r N p] at TA
  have hx1 : ∀ i, ixUT l (r + (n + 1)) N p x i =
      (rU l (r + n + 1) N p x i : ℚ) / ((l * (N * l ^ (r + n) * p) : ℕ) : ℚ) := by
    intro i
    rw [ixUT_eq]
    congr 1
    push_cast
    ring
  have hy1 : ∀ i, ixVT l (r + (n + 1)) N p i =
      (rV l (r + n + 1) N p i : ℚ) / ((l * (N * l ^ (r + n) * p) : ℕ) : ℚ) := by
    intro i
    rw [ixVT_eq]
    congr 1
    push_cast
    ring
  have TB := topXi hT hB X l (n + 1) N (l * (N * l ^ (r + n) * p)) (lvT l (n + 1) r N p) w c d g lev1 hL ws law
    (lvM1 _) (rU l (r + n + 1) N p x) (rV l (r + n + 1) N p) ok1 (ixUT l (r + (n + 1)) N p x)
    (ixVT l (r + (n + 1)) N p) hx1 hy1 _ (rdH l (n + 1) r N p)
  rw [rdH_cyc hG hZ X l (n + 1) r N p] at TB
  have TB' := hCA.2.2.2.2.1 _ _ TB
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder (Nat.Coprime.symm (hpNL (r + n))) 1 l
  have k1 : (k : ZMod (N * l ^ (r + n))) = 1 := by
    have h0 := (ZMod.natCast_eq_natCast_iff k 1 (N * l ^ (r + n))).mpr hk1
    simpa using h0
  have k2 : (k : ZMod p) = l := (ZMod.natCast_eq_natCast_iff k l p).mpr hk2
  have k1' : ∀ D, D ∣ N * l ^ (r + n) → (k : ZMod D) = 1 := by
    intro D hD
    have h0 := congrArg (ZMod.castHom hD (ZMod D)) k1
    rw [map_natCast, map_one] at h0
    exact h0
  have kcNL : Nat.Coprime k (N * l ^ (r + n)) := (ZMod.isUnit_iff_coprime k _).mp (by rw [k1]; exact isUnit_one)
  have kcp : Nat.Coprime k p :=
    (ZMod.isUnit_iff_coprime k p).mp (by rw [k2]; exact (ZMod.isUnit_iff_coprime l p).mpr hpl.symm)
  have kcM : Nat.Coprime k (lvT l n r N p) := by
    have kN : Nat.Coprime k N := Nat.Coprime.coprime_dvd_right (dvd_mul_right N _) kcNL
    have kl : Nat.Coprime k (l ^ (r + n)) := Nat.Coprime.coprime_dvd_right (dvd_mul_left _ N) kcNL
    exact Nat.Coprime.mul_right (Nat.Coprime.mul_right kl (Nat.Coprime.mul_right kN kN)) kcp
  have vcast : ∀ D, D ∣ lvT l n r N p →
      ((((ZMod.unitOfCoprime k kcM : (ZMod (lvT l n r N p))ˣ) : ZMod (lvT l n r N p)).val : ℕ) : ZMod D) = (k : ZMod D) := by
    intro D hD
    show (((k : ZMod (lvT l n r N p)).val : ℕ) : ZMod D) = (k : ZMod D)
    rw [ZMod.natCast_val, ZMod.cast_natCast hD]
  have dN : N ∣ lvT l n r N p := Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_mul_right N N) _) p
  have dLn : l ^ n ∣ lvT l n r N p := Dvd.dvd.mul_right (Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_left n r)) _) p
  have dM0 : N * l ^ (r + n) * p ∣ lvT l n r N p := ⟨N, by simp only [lvT]; ring⟩
  have n1 := (vcast N dN).trans (k1' N (dvd_mul_right N _))
  have n2 := (vcast (l ^ n) dLn).trans (k1' (l ^ n) (Dvd.dvd.mul_left (pow_dvd_pow l (Nat.le_add_left n r)) N))
  have rs := rows_succ (l := l) (L := r + n) (N := N) (p := p) (k := k) x hyp.cop (hpNL _) k1 k2
  have ex : dn l (N * l ^ (r + n) * p) (rw0 (l * (N * l ^ (r + n) * p)) (rU l (r + n + 1) N p x)) =
      ((((ZMod.unitOfCoprime k kcM : (ZMod (lvT l n r N p))ˣ) : ZMod (lvT l n r N p)).val : ℕ) :
        ZMod (N * l ^ (r + n) * p)) • rw0 (N * l ^ (r + n) * p) (rU l (r + n) N p x) := by
    rw [dn_rw0_mul_eq_rw0, vcast _ dM0, rs.1]
  have ey : dn l (N * l ^ (r + n) * p) (rw0 (l * (N * l ^ (r + n) * p)) (rV l (r + n + 1) N p)) =
      ((((ZMod.unitOfCoprime k kcM : (ZMod (lvT l n r N p))ˣ) : ZMod (lvT l n r N p)).val : ℕ) :
        ZMod (N * l ^ (r + n) * p)) • rw0 (N * l ^ (r + n) * p) (rV l (r + n) N p) := by
    rw [dn_rw0_mul_eq_rw0, vcast _ dM0, rs.2]
  have bas : Bas l N (rw0 (l * (N * l ^ (r + n) * p)) (rU l (r + n + 1) N p x))
      (rw0 (l * (N * l ^ (r + n) * p)) (rV l (r + n + 1) N p)) := by
    refine ⟨hyp.cop, ?_⟩
    simp only [rw0, val_cast (dvd_mul_right l (N * l ^ (r + n) * p)), rl1.1, rl1.2.1, rl1.2.2, Int.cast_zero,
      zero_mul, sub_zero, ZMod.val_zero, Nat.cast_zero]
    exact mul_ne_zero hNl hNl
  have hdvd : lvT l n r N p ∣ lvT l (n + 1) r N p := ⟨l, by simp only [lvT]; ring⟩
  have TC := down hA hC hM hX hD hS hG X l n N (N * l ^ (r + n) * p) (lvT l n r N p) (lvT l (n + 1) r N p) w c d g
    lev0 hL hdvd e1 ws law (lvM1 _) _ _ _ _ ok1 ok0 bas (ZMod.unitOfCoprime k kcM) n1 n2 ex ey _ (rdH l n r N p)
  rw [rdH_cyc hG hZ X l n r N p] at TC
  simp only [rdH_comp] at TC
  have hlu : IsUnit (l : ZMod p) := (ZMod.isUnit_iff_coprime l p).mpr hpl.symm
  have hinv : ((inv1 p l : (ZMod p)ˣ) : ZMod p) * l = 1 := by
    simp only [inv1, dif_pos hlu]
    exact hlu.val_inv_mul
  have hν1 : (((rdH l n r N p (ZMod.unitOfCoprime k kcM)).1 : (ZMod p)ˣ) : ZMod p) = l := by
    show ZMod.castHom (Dvd.intro_left _ rfl : p ∣ lvT l n r N p) (ZMod p) (k : ZMod (lvT l n r N p)) = _
    rw [map_natCast, k2]
  have hν2 : (rdH l n r N p (ZMod.unitOfCoprime k kcM)).2 = 1 := by
    apply Units.ext
    show ZMod.castHom ((Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) (N * N)).mul_right p)
      (ZMod (l ^ r)) (k : ZMod (lvT l n r N p)) = 1
    erw [map_natCast]
    exact k1' (l ^ r) (Dvd.dvd.mul_left (pow_dvd_pow l (Nat.le_add_right r n)) N)
  have hc : ∀ y : (ZMod p)ˣ × (ZMod (l ^ r))ˣ,
      y * (inv1 p l ^ (2 * (r + (n + 1))), 1) * rdH l n r N p (ZMod.unitOfCoprime k kcM) ^ 2 =
        y * (inv1 p l ^ (2 * (r + n)), 1) := by
    intro y
    apply Prod.ext
    · apply Units.ext
      simp only [Prod.fst_mul, Prod.pow_fst, Units.val_mul, Units.val_pow_eq_pow_val, hν1]
      linear_combination ((y.1 : ZMod p) * ((inv1 p l : (ZMod p)ˣ) : ZMod p) ^ (2 * (r + n)) *
        (((inv1 p l : (ZMod p)ˣ) : ZMod p) * l + 1)) * hinv
    · simp only [Prod.snd_mul, Prod.pow_snd, hν2, one_pow, mul_one]
  have cA := hCA.2.2.2.1 1 (inv1 p l ^ (2 * (r + n)), 1) _ _ TA
  have cB := hCA.2.2.2.1 1 (inv1 p l ^ (2 * (r + (n + 1))), 1) _ _ TB'
  have cC := hCA.2.2.2.1 1 (inv1 p l ^ (2 * (r + (n + 1))), 1) _ _ TC
  simp only [one_smul] at cA cB cC
  simp only [hc] at cC
  have hY : ∀ m, YT X l m r N p x c d w g = fun s y => GlobalTheory.KA.push (rdT l m r N p)
      (shB X l (lvT l m r N p) (clsT X l m r N p x c d w g)) s (y * (inv1 p l ^ (2 * (r + m)), 1)) := by
    intro m
    funext s y
    exact congrArg (GlobalTheory.KA.push (rdT l m r N p) (shB X l (lvT l m r N p) (clsT X l m r N p x c d w g)) s)
      (Prod.ext rfl (mul_one y.2).symm)
  rw [hY (n + 1), hY n]
  exact hE.trans cB (hE.trans cC (hE.symm cA))

end UpperTheory.V.Z.Kato.Nb.NormOneTraceTorsion

theorem UpperTheory.V.Z.Kato.Nb.kato_normRelation_levelTower :
    UpperTheory.V.Z.Kato.Nb.KatoTwistedClassCompatibleModPowers :=
  UpperTheory.V.Z.Kato.Nb.NormOneTraceTorsion.main sApi sCohApi sXiMul sXiCoh sXiDist sXiScal sSlD sTopRel sBridge sCycZ
