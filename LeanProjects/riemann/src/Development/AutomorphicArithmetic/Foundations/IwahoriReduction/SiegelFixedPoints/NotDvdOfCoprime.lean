import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgClosureOfTower
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L

private def Bd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (l k : ℕ) (y : Ω) : Prop := (l : Ω) ^ k * y ∈ A

private def lden (l : ℕ) (r : ℚ) : ℕ := r.den.factorization l

private noncomputable def pden (l : ℕ) (P : Polynomial ℚ) : ℕ := ∑ i ∈ Finset.range (P.natDegree + 1), lden l (P.coeff i)

private noncomputable def eB (l j : ℕ) : ℕ := pden l (Polynomial.bernoulli j) + lden l ((j : ℚ)⁻¹) + lden l (1 / 2)

private noncomputable def eD (j : ℕ) : ℕ := j + (Polynomial.bernoulli j).natDegree

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] {A : ValuationSubring Ω} {l : ℕ}

private theorem Bd.mono {k k' : ℕ} {y : Ω} (h : k ≤ k') (hy : Bd A l k y) : Bd A l k' y := by
  unfold Bd at *
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm, pow_add, mul_assoc]
  exact mul_mem (pow_mem (natCast_mem A l) e) hy

private theorem Bd.of_mem {k : ℕ} {y : Ω} (hy : y ∈ A) : Bd A l k y :=
  mul_mem (pow_mem (natCast_mem A l) k) hy

private theorem Bd.add {k : ℕ} {x y : Ω} (hx : Bd A l k x) (hy : Bd A l k y) : Bd A l k (x + y) := by
  unfold Bd at *; rw [mul_add]; exact add_mem hx hy

private theorem Bd.neg {k : ℕ} {x : Ω} (hx : Bd A l k x) : Bd A l k (-x) := by
  unfold Bd at *; rw [mul_neg]; exact neg_mem hx

private theorem Bd.sub {k : ℕ} {x y : Ω} (hx : Bd A l k x) (hy : Bd A l k y) : Bd A l k (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

private theorem Bd.mul {a b : ℕ} {x y : Ω} (hx : Bd A l a x) (hy : Bd A l b y) : Bd A l (a + b) (x * y) := by
  unfold Bd at *
  have e : (l : Ω) ^ (a + b) * (x * y) = ((l : Ω) ^ a * x) * ((l : Ω) ^ b * y) := by rw [pow_add]; ring
  rw [e]; exact mul_mem hx hy

private theorem Bd.mul_left {k : ℕ} {a y : Ω} (ha : a ∈ A) (hy : Bd A l k y) : Bd A l k (a * y) := by
  unfold Bd at *
  rw [mul_left_comm]; exact mul_mem ha hy

private theorem Bd.pow {a : ℕ} {x : Ω} (hx : Bd A l a x) (n : ℕ) : Bd A l (a * n) (x ^ n) := by
  unfold Bd at *
  rw [pow_mul, ← mul_pow]; exact pow_mem hx n

private theorem Bd.sum {ι : Type*} {k : ℕ} (s : Finset ι) (f : ι → Ω) (h : ∀ i ∈ s, Bd A l k (f i)) :
    Bd A l k (∑ i ∈ s, f i) := by
  unfold Bd at *
  rw [Finset.mul_sum]; exact sum_mem h

private theorem val_nat (hl : l.Prime) (hA : (l : Ω) ∈ A.nonunits) {a : ℕ} (ha : ¬ l ∣ a) :
    A.valuation (a : Ω) = 1 := by
  have hle : A.valuation (a : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (natCast_mem A a)
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  obtain ⟨u, v, huv⟩ : IsCoprime (a : ℤ) (l : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hl).2 ha).symm
  have h1 : (u : Ω) * a + v * l = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) huv
  have hu : A.valuation (u : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A u)
  have hv : A.valuation (v : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A v)
  have hl1 : A.valuation (l : Ω) < 1 := A.mem_nonunits_iff.1 hA
  have h2 : A.valuation ((u : Ω) * a) < 1 := by
    rw [map_mul]; exact lt_of_le_of_lt (by simpa using mul_le_mul' hu (le_refl (A.valuation (a : Ω)))) hlt
  have h3 : A.valuation ((v : Ω) * l) < 1 := by
    rw [map_mul]; exact lt_of_le_of_lt (by simpa using mul_le_mul' hv (le_refl (A.valuation (l : Ω)))) hl1
  have h4 := Valuation.map_add_lt _ h2 h3
  rw [h1, map_one] at h4
  exact lt_irrefl _ h4

private theorem inv_nat_mem (hl : l.Prime) (hA : (l : Ω) ∈ A.nonunits) {a : ℕ} (ha : ¬ l ∣ a) :
    ((a : Ω))⁻¹ ∈ A :=
  (A.valuation_le_one_iff _).1 (by rw [map_inv₀, val_nat hl hA ha, inv_one])

private theorem zpow_mem' {x : Ω} (hx : x ∈ A) (hx' : x⁻¹ ∈ A) (k : ℤ) : x ^ k ∈ A := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · rw [zpow_natCast]; exact pow_mem hx n
  · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem hx' n

private theorem Bd_rat (hl : l.Prime) (hA : (l : Ω) ∈ A.nonunits) (r : ℚ) : Bd A l (lden l r) (r : Ω) := by
  have hd := Nat.ordProj_mul_ordCompl_eq_self r.den l
  have hnd : ¬ l ∣ r.den / l ^ r.den.factorization l := Nat.not_dvd_ordCompl hl r.den_nz
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  set e := r.den.factorization l
  set u := r.den / l ^ e
  have hu0 : (u : Ω) ≠ 0 := Nat.cast_ne_zero.2 (fun h => hnd (h ▸ dvd_zero l))
  have hc : (r.den : Ω) = (l : Ω) ^ e * u := by rw [← hd]; push_cast; ring
  have h : (l : Ω) ^ e * (r : Ω) = r.num * (u : Ω)⁻¹ := by
    rw [Rat.cast_def, hc]; field_simp
  unfold Bd lden
  show (l : Ω) ^ e * (r : Ω) ∈ A
  rw [h]
  exact mul_mem (intCast_mem A _) (inv_nat_mem hl hA hnd)

private theorem Bd_eval (hl : l.Prime) (hA : (l : Ω) ∈ A.nonunits) (P : Polynomial ℚ) {y : ℚ} {k : ℕ}
    (hy : Bd A l k (y : Ω)) : Bd A l (pden l P + k * P.natDegree) ((P.eval y : ℚ) : Ω) := by
  rw [Polynomial.eval_eq_sum_range, Rat.cast_sum]
  refine Bd.sum _ _ fun i hi => ?_
  rw [Rat.cast_mul, Rat.cast_pow]
  refine Bd.mono ?_ ((Bd_rat hl hA (P.coeff i)).mul (hy.pow i))
  have h1 : lden l (P.coeff i) ≤ pden l P :=
    Finset.single_le_sum (f := fun i => lden l (P.coeff i)) (fun _ _ => Nat.zero_le _) hi
  have h2 : k * i ≤ k * P.natDegree :=
    Nat.mul_le_mul_left k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  exact Nat.add_le_add h1 h2

private theorem Bd_div (hl : l.Prime) (hA : (l : Ω) ∈ A.nonunits) {N M m : ℕ} (hN : ¬ l ∣ N)
    (hM : M = N * l ^ m) (x : ℤ) : Bd A l m ((x : Ω) / (M : Ω)) := by
  subst hM
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hN0 : (N : Ω) ≠ 0 := Nat.cast_ne_zero.2 (fun h => hN (h ▸ dvd_zero l))
  have e : (l : Ω) ^ m * ((x : Ω) / ((N * l ^ m : ℕ) : Ω)) = x * (N : Ω)⁻¹ := by
    push_cast; field_simp
  unfold Bd; rw [e]
  exact mul_mem (intCast_mem A x) (inv_nat_mem hl hA hN)

private theorem Bd_divN (hl : l.Prime) (hA : (l : Ω) ∈ A.nonunits) {N M m : ℕ} (hN : ¬ l ∣ N)
    (hM : M = N * l ^ m) (x : ℕ) : Bd A l m ((x : Ω) / (M : Ω)) := by
  simpa using Bd_div (A := A) hl hA hN hM (x : ℤ)

private theorem Bd_frc (hl : l.Prime) (hA : (l : Ω) ∈ A.nonunits) {N M m : ℕ} (hN : ¬ l ∣ N)
    (hM : M = N * l ^ m) (a : ℤ) : Bd A l m ((frc M a : ℚ) : Ω) := by
  have e : ((frc M a : ℚ) : Ω) = ((a % (M : ℤ) : ℤ) : Ω) / (M : Ω) := by
    unfold frc; rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  rw [e]; exact Bd_div hl hA hN hM _

private theorem Bd_coefPos (hl : l.Prime) (hA : (l : Ω) ∈ A.nonunits) {N M m : ℕ} (hN : ¬ l ∣ N)
    (hM : M = N * l ^ m) {z : Ω} (hz : z ∈ A) (hz' : z⁻¹ ∈ A) (j : ℕ) (a₁ a₂ : ℤ) (n : ℕ) :
    Bd A l (m * (j - 1)) (coefPos j M z a₁ a₂ n) := by
  unfold coefPos
  refine Bd.sum _ _ fun d _ => Bd.sub ?_ ?_
  · split_ifs
    · exact ((Bd_divN hl hA hN hM (n / d)).pow (j - 1)).mul (Bd.of_mem (k := 0) (zpow_mem' hz hz' _))
    · exact Bd.of_mem (zero_mem A)
  · split_ifs
    · exact ((Bd_divN hl hA hN hM (n / d)).neg.pow (j - 1)).mul (Bd.of_mem (k := 0) (zpow_mem' hz hz' _))
    · exact Bd.of_mem (zero_mem A)

private theorem Bd_const0 (hl : l.Prime) (hA : (l : Ω) ∈ A.nonunits) {N M m : ℕ} (hN : ¬ l ∣ N)
    (hM : M = N * l ^ m) (z : Ω) (j : ℕ) (a₁ a₂ : ℤ) (h1 : j = 1 → ¬ (M : ℤ) ∣ a₁) :
    Bd A l (eB l j + m * eD j) (const0 j M z a₁ a₂) := by
  unfold const0
  split_ifs with hj hd
  · exact absurd hd (h1 hj)
  · rw [Rat.cast_sub]
    refine Bd.sub ((Bd_rat hl hA _).mono ?_) ((Bd_frc hl hA hN hM a₁).mono ?_)
    · unfold eB; omega
    · have : m * 1 ≤ m * eD j := Nat.mul_le_mul_left m (by unfold eD; omega)
      omega
  · rw [div_eq_mul_inv, Rat.cast_mul]
    refine Bd.neg (Bd.mono ?_ ((Bd_eval hl hA _ (Bd_frc hl hA hN hM a₁)).mul (Bd_rat hl hA _)))
    unfold eB eD
    rw [Nat.mul_add]
    omega

private theorem Bd_eisF (hl : l.Prime) (hA : (l : Ω) ∈ A.nonunits) {N M m : ℕ} (hN : ¬ l ∣ N)
    (hM : M = N * l ^ m) {z : Ω} (hz : z ∈ A) (hz' : z⁻¹ ∈ A) (j : ℕ) (a₁ a₂ : ℤ)
    (h1 : j = 1 → ¬ (M : ℤ) ∣ a₁) (n : ℕ) : Bd A l (eB l j + m * eD j) (eisF j M z a₁ a₂ n) := by
  unfold eisF
  split_ifs
  · exact Bd_const0 hl hA hN hM z j a₁ a₂ h1
  · refine (Bd_coefPos hl hA hN hM hz hz' j a₁ a₂ n).mono ?_
    have : m * (j - 1) ≤ m * eD j := Nat.mul_le_mul_left m (by unfold eD; omega)
    omega

private theorem Bd_smF (hl : l.Prime) (hA : (l : Ω) ∈ A.nonunits) {N M m : ℕ} (hN : ¬ l ∣ N) (hm : 1 ≤ m)
    (hM : M = N * l ^ m) {z : Ω} (hz : z ∈ A) (hz' : z⁻¹ ∈ A) {c : ℕ} (hc : ¬ l ∣ c) (j : ℕ) (a₁ a₂ : ℤ)
    (h1 : j = 1 → ¬ (l : ℤ) ∣ a₁) (n : ℕ) :
    Bd A l (eB l j + m * eD j) (smF (c : ℤ) j M z a₁ a₂ n) := by
  have hlM : (l : ℤ) ∣ (M : ℤ) :=
    Int.natCast_dvd_natCast.2 (hM ▸ Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N)
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
  have hc1 : (((c : ℤ) : Ω)) ∈ A := intCast_mem A _
  have hc2 : (((c : ℤ) : Ω))⁻¹ ∈ A := by
    rw [Int.cast_natCast]; exact inv_nat_mem hl hA hc
  unfold smF
  refine Bd.sub (Bd.mul_left (pow_mem hc1 2) (Bd_eisF hl hA hN hM hz hz' j a₁ a₂ ?_ n))
    (Bd.mul_left (zpow_mem' hc1 hc2 _) (Bd_eisF hl hA hN hM hz hz' j _ _ ?_ n))
  · exact fun hj hd => h1 hj (hlM.trans hd)
  · intro hj hd
    rcases hp.dvd_or_dvd (hlM.trans hd) with h | h
    · exact hc (Int.natCast_dvd_natCast.1 h)
    · exact h1 hj h

private theorem not_dvd_row (hl : l.Prime) {N m v : ℕ} (hN : ¬ l ∣ N) (hm : 1 ≤ m) (hv : ¬ l ∣ v) (t : ℤ) :
    ¬ (l : ℤ) ∣ (N : ℤ) * (v : ℤ) + (l : ℤ) ^ m * t := by
  intro h
  have h1 : (l : ℤ) ∣ (l : ℤ) ^ m * t := Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) t
  have h2 : (l : ℤ) ∣ (N : ℤ) * (v : ℤ) := (dvd_add_left h1).1 h
  have h3 : l ∣ N * v := by exact_mod_cast h2
  exact ((hl.dvd_mul).1 h3).elim hN hv

private theorem not_dvd_of_coprime (hl : l.Prime) {c N : ℕ} (h : Nat.Coprime c (6 * l * N)) : ¬ l ∣ c := by
  intro hd
  have h1 : l ∣ Nat.gcd c (6 * l * N) := Nat.dvd_gcd hd (Dvd.dvd.mul_right (Dvd.intro_left 6 rfl) N)
  rw [h] at h1
  exact hl.one_lt.ne' (Nat.dvd_one.1 h1)

end SlopeTestRemainingChoices

end UpperTheory.Kd.L

theorem UpperTheory.Kd.L.small :
    ∀ (l : ℕ) [Fact l.Prime] (w L₀ : ℕ), ∃ c₂ : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (x : ZMod N) (m : ℕ), 1 ≤ m → m ≤ L₀ → ∀ (β : ℕ) (t a : ℤ) (i : ℕ), (l : Ω) ^ c₂ * toQ (l ^ m) (pieceT N l m m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a * t, 0) (a * t, 0) (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β) ((unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i ∈ A := by
  intro l _ w L₀
  refine ⟨2 * L₀ + (eB l (w + 1) + L₀ * eD (w + 1)) + (eB l 1 + L₀ * eD 1), ?_⟩
  intro Ω _ _ _ _ ε N _ c d gm hP A hA x m hm1 hmL β t a i
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl : l.Prime := Fact.out
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hz : eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β ∈ A := pow_mem (GlobalTheory.UlCusp.eOm_mem ε A _) β
  have hz' : (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β)⁻¹ ∈ A := by
    rw [← inv_pow]; exact pow_mem (GlobalTheory.UlCusp.eOm_inv_mem ε A _) β
  generalize eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β = z at hz hz' ⊢
  have hlc : ¬ l ∣ c := not_dvd_of_coprime hl hP.cc
  have hld : ¬ l ∣ d := not_dvd_of_coprime hl hP.dc
  have key : ∀ (b : ℕ) (S : Ω), Bd A l b S → (l : Ω) ^ (2 * L₀ + b) *
      (-((l : Ω) ^ ((m : ℤ) * (((w + 2 : ℕ) : ℤ) - 4))) * S) ∈ A := by
    intro b S hS
    set e : ℤ := (m : ℤ) * (((w + 2 : ℕ) : ℤ) - 4) with he
    have he0 : 0 ≤ 2 * (L₀ : ℤ) + e := by
      have h1 : (0 : ℤ) ≤ (m : ℤ) * (w : ℤ) := by positivity
      have h2 : (m : ℤ) ≤ L₀ := by exact_mod_cast hmL
      rw [he]; push_cast; nlinarith
    obtain ⟨u, hu⟩ := Int.eq_ofNat_of_zero_le he0
    have h3 : (l : Ω) ^ (2 * L₀ + b) * (l : Ω) ^ e = (l : Ω) ^ u * (l : Ω) ^ b := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hl0, ← zpow_add₀ hl0]
      congr 1; push_cast; omega
    have h4 : (l : Ω) ^ (2 * L₀ + b) * (-((l : Ω) ^ e) * S) = -((l : Ω) ^ u * ((l : Ω) ^ b * S)) := by
      linear_combination (-S) * h3
    rw [h4]
    exact neg_mem (mul_mem (pow_mem (natCast_mem A l) u) hS)
  have hsum := add_assoc (2 * L₀) (eB l (w + 1) + L₀ * eD (w + 1)) (eB l 1 + L₀ * eD 1)
  rw [hsum]
  unfold toQ pieceT
  refine key _ _ (Bd.sum _ _ fun γ hγ => ?_)
  have hγ' := Finset.mem_filter.1 (Finset.mem_filter.1 hγ).1
  have hψ : (1 : DirichletCharacter Ω (l ^ m))
      (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det.val : ℕ) : ZMod (l ^ m)) ∈ A := by
    by_cases hu : IsUnit (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det.val : ℕ) : ZMod (l ^ m))
    · rw [MulChar.one_apply hu]; exact one_mem A
    · rw [MulChar.map_nonunit _ hu]; exact zero_mem A
  refine Bd.mul_left hψ ?_
  unfold cmul
  refine Bd.sum _ _ fun r _ => Bd.mul ?_ ?_
  · refine (Bd_smF hl hA hP.cop hm1 rfl hz hz' hlc _ _ _ (fun _ => not_dvd_row hl hP.cop hm1 hγ'.2.1 _) _).mono ?_
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hmL) _
  · refine (Bd_smF hl hA hP.cop hm1 rfl hz hz' hld _ _ _ (fun _ => not_dvd_row hl hP.cop hm1 hγ'.2.2 _) _).mono ?_
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hmL) _
