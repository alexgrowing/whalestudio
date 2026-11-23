import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CohApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.TopRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SXiCoh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.XiDist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.XiScal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCycZ

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.NormOneTrace

private def rw0 (M : ℕ) (v : Fin 2 → ℤ) : Row M := fun i => (v i : ZMod M)

private theorem val_cast {M D : ℕ} [NeZero M] (h : D ∣ M) (a : ℤ) : (((a : ZMod M).val : ℕ) : ZMod D) = (a : ZMod D) := by
  rw [ZMod.natCast_val, ZMod.cast_intCast h]

private theorem exists_int_div_eq_toQ_rw0_add (M : ℕ) [NeZero M] (v : Fin 2 → ℤ) (i : Fin 2) : ∃ j : ℤ, (v i : ℚ) / (M : ℚ) = toQ M (rw0 M v) i + j := by
  refine ⟨v i / (M : ℤ), ?_⟩
  have hM : (M : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have h1 : (((v i : ZMod M).val : ℕ) : ℤ) = v i % (M : ℤ) := ZMod.val_intCast _
  have h3 : (((v i : ZMod M).val : ℕ) : ℚ) = ((v i % (M : ℤ) : ℤ) : ℚ) := by exact_mod_cast h1
  have h2 : v i % (M : ℤ) + (M : ℤ) * (v i / (M : ℤ)) = v i := by rw [Int.emod_def]; ring
  have h4 : (v i : ℚ) = ((v i % (M : ℤ) + (M : ℤ) * (v i / (M : ℤ)) : ℤ) : ℚ) := by rw [h2]
  simp only [toQ, rw0]
  rw [h3, h4]
  push_cast
  field_simp

private theorem dn_rw0_mul_eq_rw0 (k M : ℕ) (v : Fin 2 → ℤ) : dn k M (rw0 (k * M) v) = rw0 M v := by
  funext i
  simp only [dn, rw0, map_intCast]

private theorem two_ne {l M : ℕ} [Fact l.Prime] (hl : l ≠ 2) (h : l ∣ M) (v : Fin 2 → ℤ) (i : Fin 2) (hv : (v i : ZMod l) ≠ 0) :
    (2 : ZMod M) • rw0 M v ≠ 0 := by
  intro h0
  have h1 := congrFun h0 i
  simp only [Pi.smul_apply, smul_eq_mul, rw0, Pi.zero_apply] at h1
  have h2 := congrArg (ZMod.castHom h (ZMod l)) h1
  simp only [map_mul, map_ofNat, map_intCast, map_zero] at h2
  have hp : l.Prime := Fact.out
  have h3 : (2 : ZMod l) ≠ 0 := by
    intro h4
    have h5 : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h4
    have h6 : l ∣ 2 := (CharP.cast_eq_zero_iff (ZMod l) l 2).1 h5
    exact hl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h6)
  exact hv ((mul_eq_zero.1 h2).resolve_left h3)

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
  have h1 : ((p : ZMod (N * l ^ L)) * (p : ZMod (N * l ^ L))⁻¹) = 1 := ZMod.coe_mul_inv_eq_one p hp
  have h2 := congrArg (ZMod.castHom h (ZMod D)) h1
  simp only [map_mul, map_natCast, map_one, ZMod.castHom_apply] at h2
  simp only [bar]
  rw [Int.cast_natCast, ZMod.natCast_val, mul_comm]
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
  exact (Nat.isCoprime_iff_coprime.2 h).mul_dvd h1 h2

private theorem topT_succ {l L N : ℕ} [NeZero N] (h : Nat.Coprime l N) :
    (topT l (L + 1) N : ZMod (N * l ^ L)) * (l : ZMod (N * l ^ L)) ^ (L + 1) = (topT l L N : ZMod (N * l ^ L)) * (l : ZMod (N * l ^ L)) ^ L := by
  have hc : Nat.Coprime N (l ^ L) := Nat.Coprime.pow_right L h.symm
  have hu : IsUnit (l : ZMod N) := (ZMod.unitOfCoprime l h).isUnit
  have key : (((topT l (L + 1) N * l ^ (L + 1) : ℕ) : ℤ) : ZMod (N * l ^ L)) =
      (((topT l L N * l ^ L : ℕ) : ℤ) : ZMod (N * l ^ L)) := by
    apply crt hc
    · push_cast
      simp only [topT, ZMod.natCast_val, ZMod.cast_id', id]
      rw [ZMod.inv_mul_of_unit _ (hu.pow _), ZMod.inv_mul_of_unit _ (hu.pow _)]
    · push_cast
      have h0 : ((l : ZMod (l ^ L))) ^ L = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
      rw [pow_succ, h0]
      simp
  push_cast at key
  exact key

private theorem rows_succ {l L N p k : ℕ} [Fact l.Prime] [NeZero N] (x : ZMod N) (h : Nat.Coprime l N)
    (hp : Nat.Coprime p (N * l ^ (L + 1))) (k1 : (k : ZMod (N * l ^ L)) = 1) (k2 : (k : ZMod p) = l) :
    rw0 (N * l ^ L * p) (rU l (L + 1) N p x) = (k : ZMod (N * l ^ L * p)) • rw0 (N * l ^ L * p) (rU l L N p x) ∧
    rw0 (N * l ^ L * p) (rV l (L + 1) N p) = (k : ZMod (N * l ^ L * p)) • rw0 (N * l ^ L * p) (rV l L N p) := by
  have hpr : l.Prime := Fact.out
  have hdv : N * l ^ L ∣ N * l ^ (L + 1) := Nat.mul_dvd_mul_left N (pow_dvd_pow l (Nat.le_succ L))
  have hp' : Nat.Coprime p (N * l ^ L) := Nat.Coprime.coprime_dvd_right hdv hp
  have hc : Nat.Coprime (N * l ^ L) p := hp'.symm
  haveI : NeZero (N * l ^ L) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hpr.ne_zero)⟩
  haveI : NeZero (N * l ^ (L + 1)) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hpr.ne_zero)⟩
  have e1 := bar_mul (l := l) (L := L + 1) (N := N) (p := p) (D := N * l ^ L) hp hdv
  have e2 := bar_mul (l := l) (L := L) (N := N) (p := p) (D := N * l ^ L) hp' dvd_rfl
  have e3 := topT_succ (l := l) (L := L) (N := N) h
  have e4 : (N : ZMod (N * l ^ L)) * (l : ZMod (N * l ^ L)) ^ L = 0 := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, ZMod.natCast_self]
  have f0 : (p : ZMod p) = 0 := ZMod.natCast_self p
  have lift : ∀ a b : ℤ, (a : ZMod (N * l ^ L)) = (k : ZMod (N * l ^ L)) * b → (a : ZMod p) = (k : ZMod p) * b →
      (a : ZMod (N * l ^ L * p)) = (k : ZMod (N * l ^ L * p)) * b := by
    intro a b h1 h2
    have h3 := crt hc (a := a) (b := (k : ℤ) * b) (by push_cast; exact h1) (by push_cast; exact h2)
    push_cast at h3
    exact h3
  refine ⟨?_, ?_⟩
  · funext i
    fin_cases i
    · simp only [rw0, Pi.smul_apply, smul_eq_mul]
      apply lift
      · simp only [rU, Matrix.cons_val_zero, Fin.zero_eta]
        push_cast
        linear_combination ((N : ZMod (N * l ^ L)) + x.val * topT l (L + 1) N * l ^ (L + 1)) * e1
          - (k * (N + x.val * topT l L N * l ^ L) : ZMod (N * l ^ L)) * e2 + (x.val : ZMod (N * l ^ L)) * e3
          + ((l : ZMod (N * l ^ L)) - k) * e4 - ((N : ZMod (N * l ^ L)) + x.val * topT l L N * l ^ L) * k1
      · simp only [rU, Matrix.cons_val_zero, Fin.zero_eta]
        push_cast
        linear_combination ((bar l (L + 1) N p : ZMod p) * (N + x.val * topT l (L + 1) N * l ^ (L + 1))
          - k * bar l L N p * (N + x.val * topT l L N * l ^ L)) * f0 - ((N : ZMod p) * l ^ L) * k2
    · simp only [rw0, Pi.smul_apply, smul_eq_mul, rU, Matrix.cons_val_one, Matrix.head_cons, Fin.mk_one]
      simp
  · funext i
    fin_cases i
    · simp only [rw0, Pi.smul_apply, smul_eq_mul]
      apply lift
      · simp only [rV, Matrix.cons_val_zero, Fin.zero_eta]
        push_cast
        linear_combination ((topT l (L + 1) N : ZMod (N * l ^ L)) * l ^ (L + 1)) * e1 + e3
          - ((k : ZMod (N * l ^ L)) * topT l L N * l ^ L) * e2 - ((topT l L N : ZMod (N * l ^ L)) * l ^ L) * k1
      · simp only [rV, Matrix.cons_val_zero, Fin.zero_eta]
        push_cast
        linear_combination ((bar l (L + 1) N p : ZMod p) * topT l (L + 1) N * l ^ (L + 1)
          - k * bar l L N p * topT l L N * l ^ L) * f0
    · simp only [rw0, Pi.smul_apply, smul_eq_mul]
      apply lift
      · simp only [rV, Matrix.cons_val_one, Matrix.head_cons, Fin.mk_one]
        push_cast
        linear_combination (N : ZMod (N * l ^ L)) * e1 - ((k : ZMod (N * l ^ L)) * N) * e2
          + ((l : ZMod (N * l ^ L)) - k) * e4 - (N : ZMod (N * l ^ L)) * k1
      · simp only [rV, Matrix.cons_val_one, Matrix.head_cons, Fin.mk_one]
        push_cast
        linear_combination ((bar l (L + 1) N p : ZMod p) * N - k * bar l L N p * N) * f0 - ((N : ZMod p) * l ^ L) * k2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private theorem down (hA : SApi) (hC : SCohApi) (hX : SXiCoh) (hD : SXiDist) (hS : SXiScal)
    (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M M' w c d : ℕ) [NeZero N] [NeZero M₀] [NeZero M] [NeZero M'] [NeZero (l * M₀)]
    (g : SL(2, ℤ)) (lev : Lev l n N M₀ M g) (hL : LiftsWith X l N w (cL X l N w)) (h : M ∣ M') (e : M' = N * (l * M₀))
    (ws) (law : Laws X l c d ws) (lv : Lv c d (l * M₀)) (x' y' : Row (l * M₀)) (x y : Row M₀) (ok : Ok x y)
    (bas : Bas l N x' y') (ν : (ZMod M)ˣ) (n1 : ((ν : ZMod M).val : ZMod N) = 1) (n2 : ((ν : ZMod M).val : ZMod (l ^ n)) = 1)
    (ex : dn l M₀ x' = ((ν : ZMod M).val : ZMod M₀) • x) (ey : dn l M₀ y' = ((ν : ZMod M).val : ZMod M₀) • y)
    (A : Type) [CommGroup A] (π : (ZMod M)ˣ →* A) :
    CohB X l N w n (fun s => (π (cycM M s))⁻¹)
      (fun s t => Xi X l n N (l * M₀) M' w g x' y'
        (fun z => π (Units.map (ZMod.castHom h (ZMod M)).toMonoidHom z) = t) (ws n (l * M₀) s))
      (fun s t => Xi X l n N M₀ M w g x y (fun z => π z = t * π ν ^ 2) (ws n M₀ s)) := by
  have hpr : l.Prime := Fact.out
  haveI : NeZero l := ⟨hpr.ne_zero⟩
  have EF := (hA Ω ε X l n).1
  have hC' := hC Ω ε X l N w n (Nat.pos_of_ne_zero (NeZero.ne N)) A (fun s => (π (cycM M s))⁻¹)
  have EC := hC'.1
  have sc : ∀ (k : ℤ_[l]) (a : X.Fn l), (l : ℤ_[l]) ^ n ∣ k - 1 → CgF X l n (k • a) a := by
    intro k a hk u
    have := (hA Ω ε X l n).2.2.2.2.1 k 1 (a u) hk
    simpa using this
  have d1 : ((l ^ n : ℕ) : ℤ) ∣ (((ν : ZMod M).val : ℕ) : ℤ) - 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub 1 _ (l ^ n)).1 (by push_cast; exact n2.symm)
  have d2 : (l : ℤ_[l]) ^ n ∣ (((ν : ZMod M).val : ℕ) : ℤ_[l]) - 1 := by
    simpa using map_dvd (Int.castRingHom ℤ_[l]) d1
  have dpow : ∀ m : ℕ, (l : ℤ_[l]) ^ n ∣ (((ν : ZMod M).val : ℕ) : ℤ_[l]) ^ m - 1 := fun m =>
    d2.trans (by simpa using sub_dvd_pow_sub_pow (((ν : ZMod M).val : ℕ) : ℤ_[l]) 1 m)
  have hdvd : M₀ ∣ M := ⟨N, by rw [lev.eq, mul_comm]⟩
  have cu : IsUnit (((ν : ZMod M).val : ZMod M₀)) := by
    rw [ZMod.natCast_val]
    exact ν.isUnit.map (ZMod.castHom hdvd (ZMod M₀))
  have okd : Ok (dn l M₀ x') (dn l M₀ y') := by
    rw [ex, ey]
    have ok' : (2 : ZMod M₀) • x ≠ 0 ∧ (2 : ZMod M₀) • y ≠ 0 := ok
    refine ⟨fun h0 => ok'.1 ?_, fun h0 => ok'.2 ?_⟩
    · rw [smul_comm] at h0
      exact cu.smul_left_cancel.1 (h0.trans (smul_zero _).symm)
    · rw [smul_comm] at h0
      exact cu.smul_left_cancel.1 (h0.trans (smul_zero _).symm)
  refine EC.trans (y := fun s t => Xi X l n N M₀ M w g (dn l M₀ x') (dn l M₀ y') (fun z => π z = t)
    (pushD X l M₀ (ws n (l * M₀) s))) ?_ ?_
  · apply hC'.2.1
    intro s t
    exact hD Ω ε X l n N M₀ M w g lev M' h e x' y' bas (fun z => π z = t) (ws n (l * M₀) s)
  refine EC.trans (hX Ω ε X l n N M₀ M w g lev hL (dn l M₀ x') (dn l M₀ y') okd A π _ _ (law.dist n l M₀ lv)) ?_
  rw [ex, ey]
  apply hC'.2.1
  intro s t
  have key : (fun z => π (z * ν⁻¹ ^ 2) = t) = (fun z => π z = t * π ν ^ 2) := by
    funext z
    apply propext
    rw [map_mul, map_pow, map_inv, inv_pow, mul_inv_eq_iff_eq_mul]
  rw [← key]
  have hs := hS Ω ε X l n N M₀ M w g lev x y (fun z => π z = t) (ws n M₀ s) ν n1
  have e1 := sc _ (Xi X l n N M₀ M w g (((ν : ZMod M).val : ZMod M₀) • x) (((ν : ZMod M).val : ZMod M₀) • y)
    (fun z => π z = t) (ws n M₀ s)) (dpow w)
  have e2 := sc _ (Xi X l n N M₀ M w g x y (fun z => π (z * ν⁻¹ ^ 2) = t) (ws n M₀ s)) (dpow 2)
  exact EF.trans (EF.symm e1) (EF.trans hs e2)

private theorem topXi (hT : STopRel) (hB : SBridge)
    (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w c d : ℕ) [NeZero N] [NeZero M₀] [NeZero M]
    (g : SL(2, ℤ)) (lev : Lev l n N M₀ M g) (hL : LiftsWith X l N w (cL X l N w))
    (ws) (law : Laws X l c d ws) (lv : Lv c d M₀) (U V : Fin 2 → ℤ) (ok : Ok (rw0 M₀ U) (rw0 M₀ V)) (x' y' : Fin 2 → ℚ)
    (hx : ∀ i, x' i = (U i : ℚ) / (M₀ : ℚ)) (hy : ∀ i, y' i = (V i : ℚ) / (M₀ : ℚ))
    (A : Type) [Group A] [DecidableEq A] (π : (ZMod M)ˣ →* A) :
    CohB X l N w n (fun s => (π (cycM M s))⁻¹) (GlobalTheory.KA.push π (shB X l M (clsG X l n N M w c d g x' y')))
      fun s t => Xi X l n N M₀ M w g (rw0 M₀ U) (rw0 M₀ V) (fun z => π z = t) (ws n M₀ s) := by
  have hx' : ∀ i, ∃ j : ℤ, x' i = toQ M₀ (rw0 M₀ U) i + j := fun i => by
    rw [hx i]
    exact exists_int_div_eq_toQ_rw0_add M₀ U i
  have hy' : ∀ i, ∃ j : ℤ, y' i = toQ M₀ (rw0 M₀ V) i + j := fun i => by
    rw [hy i]
    exact exists_int_div_eq_toQ_rw0_add M₀ V i
  obtain ⟨β, hβ, hc⟩ := hT Ω ε X l n N M₀ M w g lev hL c d ws law lv (rw0 M₀ U) (rw0 M₀ V) ok x' y' hx' hy'
  exact hB Ω ε X l n N M₀ M w g lev hL (rw0 M₀ U) (rw0 M₀ V) ok (ws n M₀) (law.coc n M₀ lv) _ β hβ hc A π

private def rdH (l n r N p : ℕ) : (ZMod (lvT l n r N p))ˣ →* (ZMod p)ˣ × (ZMod (l ^ r))ˣ :=
  (Units.map (ZMod.castHom (Dvd.intro_left _ rfl : p ∣ lvT l n r N p) (ZMod p)).toMonoidHom).prod
   (Units.map (ZMod.castHom ((Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) (N * N)).mul_right p)
     (ZMod (l ^ r))).toMonoidHom)

private theorem rdH_comp (l n r N p : ℕ) (h : lvT l n r N p ∣ lvT l n (r + 1) N p) (z : (ZMod (lvT l n (r + 1) N p))ˣ) :
    Prod.map id (redL l r) (rdT l n (r + 1) N p z) =
      rdH l n r N p (Units.map (ZMod.castHom h (ZMod (lvT l n r N p))).toMonoidHom z) := by
  have c1 : ∀ (a b c : ℕ) (h1 : b ∣ a) (h2 : c ∣ b) (u : ZMod a),
      ZMod.castHom h2 (ZMod c) (ZMod.castHom h1 (ZMod b) u) = ZMod.castHom (h2.trans h1) (ZMod c) u := by
    intro a b c h1 h2 u
    exact RingHom.congr_fun (ZMod.castHom_comp h2 h1) u
  apply Prod.ext
  · apply Units.ext
    exact (c1 _ _ _ _ _ _).symm
  · apply Units.ext
    exact (c1 _ _ _ _ _ _).trans (c1 _ _ _ _ _ _).symm

private theorem push_push {Γ Z A B B' M : Type} [Fintype Z] [Group A] [Fintype (A × B')] [DecidableEq (A × B')] [DecidableEq (A × B)]
    [AddCommMonoid M] (π : Z → A × B') (f : B' → B) (π' : Z → A × B) (h : ∀ z, Prod.map id f (π z) = π' z) (u : A)
    (Y : Γ → Z → M) (s : Γ) (y : A × B) :
    GlobalTheory.KA.push (Prod.map id f) (fun s (y' : A × B') => GlobalTheory.KA.push π Y s (y'.1 * u, y'.2)) s y = GlobalTheory.KA.push π' Y s (y.1 * u, y.2) := by
  classical
  have hmaps : ∀ z ∈ Finset.univ.filter (fun z => π' z = (y.1 * u, y.2)),
      (fun z => ((π z).1 * u⁻¹, (π z).2)) z ∈ Finset.univ.filter (fun y' : A × B' => Prod.map id f y' = y) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    rw [← h z] at hz
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 hz
    simp only [Prod.map_fst, Prod.map_snd, id] at h1 h2
    apply Prod.ext
    · simp [h1]
    · simpa using h2
  simp only [GlobalTheory.KA.push]
  refine Eq.trans ?_ (Finset.sum_fiberwise_of_maps_to hmaps _)
  apply Finset.sum_congr
  · ext y'
    simp
  intro y' hy'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy'
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hz
    refine ⟨?_, ?_⟩
    · rw [← h z, hz, ← hy']
      simp
    · rw [hz]
      simp
  · rintro ⟨-, hz⟩
    rw [← hz]
    simp

private theorem rdH_cyc (hG : SSlD) (hZ : SCycZ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N p : ℕ) [NeZero N] [NeZero p] :
    (fun s : Ω ≃ₐ[ℚ] Ω => (rdH l n r N p (cycM (lvT l n r N p) s))⁻¹) = kT l r p := by
  funext s
  have h := ((hG Ω ε X N (Nat.pos_of_ne_zero (NeZero.ne N))).2.2.2.2.2.2.2 (lvT l n r N p) s).2.2.2.2
  unfold kT
  rw [(hZ Ω l r s).1]
  exact Prod.ext (congrArg Inv.inv (h p _)) (congrArg Inv.inv (h (l ^ r) _))

private theorem main (hA : SApi) (hC : SCohApi) (hX : SXiCoh) (hD : SXiDist) (hS : SXiScal) (hG : SSlD)
    (hT : STopRel) (hB : SBridge) (hZ : SCycZ) : KatoTwistedClassNormCompatibleCyclotomic := by
  intro Ω _ _ _ ε X l _ N p _ _ x c d w g hyp hp hcop hws hL n r
  obtain ⟨ws, law⟩ := hws
  have hpr : l.Prime := Fact.out
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have C := hC Ω ε X l N w n hN ((ZMod p)ˣ × (ZMod (l ^ r))ˣ) (kT l r p)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact C.2.2.2.2.2.1 _ _
  haveI : NeZero l := ⟨hpr.ne_zero⟩
  have hl2 : l ≠ 2 := hyp.odd
  have hlN : l.Coprime N := hyp.cop
  have hpl : Nat.Coprime p l := Nat.Coprime.coprime_dvd_right ⟨N * c * d, by ring⟩ hcop
  have hpN : Nat.Coprime p N := Nat.Coprime.coprime_dvd_right ⟨l * c * d, by ring⟩ hcop
  have hpc : Nat.Coprime p c := Nat.Coprime.coprime_dvd_right ⟨l * N * d, by ring⟩ hcop
  have hpd : Nat.Coprime p d := Nat.Coprime.coprime_dvd_right ⟨l * N * c, by ring⟩ hcop
  have hpNL : ∀ L, Nat.Coprime p (N * l ^ L) := fun L => Nat.Coprime.mul_right hpN (Nat.Coprime.pow_right L hpl)
  have hNl : (N : ZMod l) ≠ 0 := by
    intro h0
    have h1 : l ∣ N := (CharP.cast_eq_zero_iff (ZMod l) l N).1 h0
    exact hpr.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hlN h1)
  haveI i1 : NeZero (N * l ^ (r + n) * p) :=
    ⟨mul_ne_zero (mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hpr.ne_zero)) (NeZero.ne p)⟩
  haveI i2 : NeZero (l * (N * l ^ (r + n) * p)) := ⟨mul_ne_zero hpr.ne_zero i1.out⟩
  haveI i3 : NeZero (lvT l n r N p) := ⟨by
    simp only [lvT]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hpr.ne_zero) (mul_ne_zero (NeZero.ne N) (NeZero.ne N))) (NeZero.ne p)⟩
  haveI i4 : NeZero (lvT l n (r + 1) N p) := ⟨by
    simp only [lvT]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hpr.ne_zero) (mul_ne_zero (NeZero.ne N) (NeZero.ne N))) (NeZero.ne p)⟩
  have eMr : lvT l n r N p = N * (N * l ^ (r + n) * p) := by simp only [lvT]; ring
  have eM1 : lvT l n (r + 1) N p = N * (l * (N * l ^ (r + n) * p)) := by simp only [lvT]; ring
  have hMM : lvT l n r N p ∣ lvT l n (r + 1) N p := ⟨l, by rw [eMr, eM1]; ring⟩
  have lev0 : Lev l n N (N * l ^ (r + n) * p) (lvT l n r N p) g :=
    ⟨eMr, ⟨l ^ (r + n) * p, by ring⟩, ⟨N * l ^ r * p, by ring⟩, hn, hlN, hyp.g0⟩
  have lev1 : Lev l n N (l * (N * l ^ (r + n) * p)) (lvT l n (r + 1) N p) g :=
    ⟨eM1, ⟨l * l ^ (r + n) * p, by ring⟩, ⟨l * N * l ^ r * p, by ring⟩, hn, hlN, hyp.g0⟩
  have cl : Nat.Coprime c l := Nat.Coprime.coprime_dvd_right ⟨6 * N, by ring⟩ hyp.cc
  have cN : Nat.Coprime c N := Nat.Coprime.coprime_dvd_right ⟨6 * l, by ring⟩ hyp.cc
  have dl : Nat.Coprime d l := Nat.Coprime.coprime_dvd_right ⟨6 * N, by ring⟩ hyp.cd
  have dN : Nat.Coprime d N := Nat.Coprime.coprime_dvd_right ⟨6 * l, by ring⟩ hyp.cd
  have cop3 : ∀ {e : ℕ}, Nat.Coprime e l → Nat.Coprime e N → Nat.Coprime e p →
      Nat.Coprime e (N * l ^ (r + n) * p) ∧ Nat.Coprime e (l * (N * l ^ (r + n) * p)) := fun a b q =>
    ⟨Nat.Coprime.mul_right (Nat.Coprime.mul_right b (Nat.Coprime.pow_right _ a)) q,
      Nat.Coprime.mul_right a (Nat.Coprime.mul_right (Nat.Coprime.mul_right b (Nat.Coprime.pow_right _ a)) q)⟩
  have lv0 : Lv c d (N * l ^ (r + n) * p) :=
    ⟨Nat.pos_of_ne_zero i1.out, (cop3 cl cN hpc.symm).1, (cop3 dl dN hpd.symm).1⟩
  have lv1 : Lv c d (l * (N * l ^ (r + n) * p)) :=
    ⟨Nat.pos_of_ne_zero i2.out, (cop3 cl cN hpc.symm).2, (cop3 dl dN hpd.symm).2⟩
  have rl0 := rows_l (l := l) (L := r + n) (N := N) (p := p) x (by omega) (hpNL _)
  have rl1 := rows_l (l := l) (L := r + 1 + n) (N := N) (p := p) x (by omega) (hpNL _)
  have hlQ : l ∣ N * l ^ (r + n) * p := Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N) p
  have ok0 : Ok (rw0 (N * l ^ (r + n) * p) (rU l (r + n) N p x)) (rw0 (N * l ^ (r + n) * p) (rV l (r + n) N p)) :=
    And.intro (two_ne hl2 hlQ _ 0 (by rw [rl0.1]; exact hNl)) (two_ne hl2 hlQ _ 1 (by rw [rl0.2.1]; exact hNl))
  have ok1 : Ok (rw0 (l * (N * l ^ (r + n) * p)) (rU l (r + 1 + n) N p x))
      (rw0 (l * (N * l ^ (r + n) * p)) (rV l (r + 1 + n) N p)) :=
    And.intro (two_ne hl2 (dvd_mul_right _ _) _ 0 (by rw [rl1.1]; exact hNl))
      (two_ne hl2 (dvd_mul_right _ _) _ 1 (by rw [rl1.2.1]; exact hNl))
  have e1n : N * l ^ (r + 1 + n) * p = l * (N * l ^ (r + n) * p) := by ring
  have hx1 : ∀ i, ixUT l (r + 1 + n) N p x i = (rU l (r + 1 + n) N p x i : ℚ) / ((l * (N * l ^ (r + n) * p) : ℕ) : ℚ) :=
    fun i => by rw [ixUT_eq, e1n]
  have hy1 : ∀ i, ixVT l (r + 1 + n) N p i = (rV l (r + 1 + n) N p i : ℚ) / ((l * (N * l ^ (r + n) * p) : ℕ) : ℚ) :=
    fun i => by rw [ixVT_eq, e1n]
  have hcp : Nat.Coprime (l ^ (r + n) * (N * N)) p :=
    (Nat.Coprime.mul_right (Nat.Coprime.pow_right _ hpl) (Nat.Coprime.mul_right hpN hpN)).symm
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcp 1 l
  have hkD : ∀ D, D ∣ l ^ (r + n) * (N * N) → (k : ZMod D) = 1 := fun D hD => by
    have h1 := (ZMod.natCast_eq_natCast_iff k 1 D).2 (Nat.ModEq.of_dvd hD hk1)
    simpa using h1
  have hkp : (k : ZMod p) = l := (ZMod.natCast_eq_natCast_iff k l p).2 hk2
  have kcop : Nat.Coprime k (lvT l n r N p) := by
    simp only [lvT]
    apply Nat.Coprime.mul_right
    · have h1 := Nat.ModEq.gcd_eq hk1
      simpa [Nat.Coprime] using h1
    · have h1 := Nat.ModEq.gcd_eq hk2
      rw [Nat.Coprime, h1]
      exact hpl.symm
  obtain ⟨ν, hνk⟩ : ∃ ν : (ZMod (lvT l n r N p))ˣ, (ν : ZMod (lvT l n r N p)) = k :=
    ⟨ZMod.unitOfCoprime k kcop, ZMod.coe_unitOfCoprime k kcop⟩
  have hν : ∀ D, D ∣ lvT l n r N p → (((ν : ZMod (lvT l n r N p)).val : ℕ) : ZMod D) = k := fun D hD => by
    rw [ZMod.natCast_val, hνk, ZMod.cast_natCast hD]
  have n1 : (((ν : ZMod (lvT l n r N p)).val : ℕ) : ZMod N) = 1 := by
    rw [hν N ⟨N * l ^ (r + n) * p, eMr⟩]
    exact hkD N ⟨l ^ (r + n) * N, by ring⟩
  have n2 : (((ν : ZMod (lvT l n r N p)).val : ℕ) : ZMod (l ^ n)) = 1 := by
    rw [hν _ ⟨l ^ r * (N * N) * p, by simp only [lvT]; ring⟩]
    exact hkD _ ⟨l ^ r * (N * N), by ring⟩
  have hkQ : (k : ZMod (N * l ^ (r + n))) = 1 := hkD _ ⟨N, by ring⟩
  have rs := rows_succ (l := l) (L := r + n) (N := N) (p := p) (k := k) x hlN (hpNL _) hkQ hkp
  rw [show r + n + 1 = r + 1 + n by omega] at rs
  have hQM : N * l ^ (r + n) * p ∣ lvT l n r N p := ⟨N, by rw [eMr, mul_comm]⟩
  have ex : dn l (N * l ^ (r + n) * p) (rw0 (l * (N * l ^ (r + n) * p)) (rU l (r + 1 + n) N p x)) =
      (((ν : ZMod (lvT l n r N p)).val : ℕ) : ZMod (N * l ^ (r + n) * p)) • rw0 (N * l ^ (r + n) * p) (rU l (r + n) N p x) := by
    rw [dn_rw0_mul_eq_rw0, hν _ hQM, rs.1]
  have ey : dn l (N * l ^ (r + n) * p) (rw0 (l * (N * l ^ (r + n) * p)) (rV l (r + 1 + n) N p)) =
      (((ν : ZMod (lvT l n r N p)).val : ℕ) : ZMod (N * l ^ (r + n) * p)) • rw0 (N * l ^ (r + n) * p) (rV l (r + n) N p) := by
    rw [dn_rw0_mul_eq_rw0, hν _ hQM, rs.2]
  have bas : Bas l N (rw0 (l * (N * l ^ (r + n) * p)) (rU l (r + 1 + n) N p x))
      (rw0 (l * (N * l ^ (r + n) * p)) (rV l (r + 1 + n) N p)) := by
    refine And.intro hlN ?_
    have b1 : rw0 (l * (N * l ^ (r + n) * p)) (rU l (r + 1 + n) N p x) 1 = 0 := by
      simp only [rw0]
      rw [rl1.2.2]
      simp
    rw [b1, ZMod.val_zero]
    simp only [Nat.cast_zero, zero_mul, sub_zero, rw0]
    rw [val_cast (dvd_mul_right l _), val_cast (dvd_mul_right l _), rl1.1, rl1.2.1]
    exact mul_ne_zero hNl hNl
  have hcyc := (hG Ω ε X 1 one_pos).2.2.2.2.2.2.2
  have Cr := topXi hT hB X l n N (N * l ^ (r + n) * p) (lvT l n r N p) w c d g lev0 hL ws law lv0
    (rU l (r + n) N p x) (rV l (r + n) N p) ok0 (ixUT l (r + n) N p x) (ixVT l (r + n) N p)
    (ixUT_eq l (r + n) N p x) (ixVT_eq l (r + n) N p) _ (rdH l n r N p)
  rw [rdH_cyc hG hZ X l n r N p] at Cr
  have C1 := topXi hT hB X l n N (l * (N * l ^ (r + n) * p)) (lvT l n (r + 1) N p) w c d g lev1 hL ws law lv1
    (rU l (r + 1 + n) N p x) (rV l (r + 1 + n) N p) ok1 (ixUT l (r + 1 + n) N p x) (ixVT l (r + 1 + n) N p)
    hx1 hy1 _ ((rdH l n r N p).comp (Units.map (ZMod.castHom hMM (ZMod (lvT l n r N p))).toMonoidHom))
  have hκ' : (fun s : Ω ≃ₐ[ℚ] Ω => (((rdH l n r N p).comp (Units.map (ZMod.castHom hMM (ZMod (lvT l n r N p))).toMonoidHom))
      (cycM (lvT l n (r + 1) N p) s))⁻¹) = kT l r p := by
    rw [← rdH_cyc hG hZ X l n r N p]
    funext s
    exact congrArg (fun u => (rdH l n r N p u)⁻¹) ((hcyc (lvT l n (r + 1) N p) s).2.2.2.2 (lvT l n r N p) hMM)
  rw [hκ'] at C1
  have Dn := down hA hC hX hD hS X l n N (N * l ^ (r + n) * p) (lvT l n r N p) (lvT l n (r + 1) N p) w c d g lev0 hL
    hMM eM1 ws law lv1 _ _ _ _ ok0 bas ν n1 n2 ex ey _ (rdH l n r N p)
  rw [rdH_cyc hG hZ X l n r N p] at Dn
  have chain1 := C.1.trans C1 Dn
  have hνp : (((rdH l n r N p ν).1 : (ZMod p)ˣ) : ZMod p) = l := by
    show (ZMod.castHom _ (ZMod p)) (ν : ZMod (lvT l n r N p)) = l
    rw [hνk, map_natCast, hkp]
  have hνl : (rdH l n r N p ν).2 = 1 := Units.ext (by
    show (ZMod.castHom _ (ZMod (l ^ r))) (ν : ZMod (lvT l n r N p)) = 1
    rw [hνk, map_natCast]
    exact hkD _ ⟨l ^ n * (N * N), by ring⟩)
  have hinv : inv1 p l = ((rdH l n r N p ν).1)⁻¹ := by
    have hu : IsUnit (l : ZMod p) := by
      rw [← hνp]
      exact Units.isUnit _
    rw [inv1, dif_pos hu, inv_inj]
    exact Units.ext (by rw [IsUnit.unit_spec, hνp])
  have htt : ((inv1 p l ^ (2 * (r + 1 + n)), (1 : (ZMod (l ^ r))ˣ)) : (ZMod p)ˣ × (ZMod (l ^ r))ˣ) * (rdH l n r N p ν) ^ 2 =
      (inv1 p l ^ (2 * (r + n)), 1) := by
    apply Prod.ext
    · show inv1 p l ^ (2 * (r + 1 + n)) * ((rdH l n r N p ν).1) ^ 2 = inv1 p l ^ (2 * (r + n))
      rw [hinv, show 2 * (r + 1 + n) = 2 * (r + n) + 2 by ring, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel,
        one_pow, mul_one]
    · show 1 * ((rdH l n r N p ν).2) ^ 2 = 1
      rw [hνl]
      simp
  have S1 := C.2.2.2.1 1 (inv1 p l ^ (2 * (r + 1 + n)), 1) _ _ chain1
  have S0 := C.2.2.2.1 1 (inv1 p l ^ (2 * (r + n)), 1) _ _ Cr
  simp only [mul_assoc, htt] at S1
  have fin := C.1.trans S1 (C.1.symm S0)
  have eqL : GlobalTheory.KA.push (Prod.map id (redL l r)) (YT X l n (r + 1) N p x c d w g) =
      fun s y => (1 : ℤ_[l]) • GlobalTheory.KA.push
        (⇑((rdH l n r N p).comp (Units.map (ZMod.castHom hMM (ZMod (lvT l n r N p))).toMonoidHom)))
        (shB X l (lvT l n (r + 1) N p) (clsT X l n (r + 1) N p x c d w g)) s
        (y * (inv1 p l ^ (2 * (r + 1 + n)), 1)) := by
    funext s y
    rw [one_smul]
    exact (push_push (rdT l n (r + 1) N p) (redL l r)
      (⇑((rdH l n r N p).comp (Units.map (ZMod.castHom hMM (ZMod (lvT l n r N p))).toMonoidHom)))
      (fun z => rdH_comp l n r N p hMM z) (inv1 p l ^ (2 * (r + 1 + n)))
      (shB X l (lvT l n (r + 1) N p) (clsT X l n (r + 1) N p x c d w g)) s y).trans
      (congrArg _ (Prod.ext rfl (mul_one y.2).symm :
        ((y.1 * inv1 p l ^ (2 * (r + 1 + n)), y.2) : (ZMod p)ˣ × (ZMod (l ^ r))ˣ) = y * (inv1 p l ^ (2 * (r + 1 + n)), 1)))
  have eqR : YT X l n r N p x c d w g =
      fun s y => (1 : ℤ_[l]) • GlobalTheory.KA.push (⇑(rdH l n r N p))
        (shB X l (lvT l n r N p) (clsT X l n r N p x c d w g)) s (y * (inv1 p l ^ (2 * (r + n)), 1)) := by
    funext s y
    rw [one_smul]
    exact congrArg (GlobalTheory.KA.push (rdT l n r N p) (shB X l (lvT l n r N p) (clsT X l n r N p x c d w g)) s)
      (Prod.ext rfl (mul_one y.2).symm :
        ((y.1 * inv1 p l ^ (2 * (r + n)), y.2) : (ZMod p)ˣ × (ZMod (l ^ r))ˣ) = y * (inv1 p l ^ (2 * (r + n)), 1))
  rw [eqL, eqR]
  exact fin

end UpperTheory.V.Z.Kato.Nb.NormOneTrace

theorem UpperTheory.V.Z.Kato.Nb.kato_normRelation_twistTower :
    UpperTheory.V.Z.Kato.Nb.KatoTwistedClassNormCompatibleCyclotomic :=
  UpperTheory.V.Z.Kato.Nb.NormOneTrace.main sApi sCohApi sXiCoh sXiDist sXiScal sSlD sTopRel sBridge sCycZ
