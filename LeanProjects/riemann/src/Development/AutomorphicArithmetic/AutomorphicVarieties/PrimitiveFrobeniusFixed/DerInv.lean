import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.DerBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.AdmProd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

namespace UpperTheory.V.ML

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem di_mem {N : ℕ} {g : G ℚ Ω} : g ∈ fixMu ℚ Ω N ↔ ∀ x : Ω, x ^ N = 1 → g x = x := Iff.rfl

private theorem di_der_mul (τ : ℕ → G ℚ Ω) (L : List ℕ) (u v : Ω) :
    der τ L (u * v) = der τ L u * der τ L v := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    show der1 q (τ q) (der τ L (u * v)) = der1 q (τ q) (der τ L u) * der1 q (τ q) (der τ L v)
    rw [ih]
    simp only [der1, map_mul, mul_pow, Finset.prod_mul_distrib]

private theorem di_der_one (τ : ℕ → G ℚ Ω) (L : List ℕ) : der τ L (1 : Ω) = 1 := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    show der1 q (τ q) (der τ L 1) = 1
    rw [ih]
    simp [der1]

private theorem di_der_inv (τ : ℕ → G ℚ Ω) (L : List ℕ) (u : Ω) :
    der τ L u⁻¹ = (der τ L u)⁻¹ := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    show der1 q (τ q) (der τ L u⁻¹) = (der1 q (τ q) (der τ L u))⁻¹
    rw [ih]
    simp only [der1, map_inv₀, inv_pow, Finset.prod_inv_distrib]

private theorem di_der_pow (τ : ℕ → G ℚ Ω) (L : List ℕ) (u : Ω) (k : ℕ) :
    der τ L (u ^ k) = der τ L u ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, di_der_one]
  | succ k ih => rw [pow_succ, pow_succ, di_der_mul, ih]

private theorem di_der_prod (τ : ℕ → G ℚ Ω) (L : List ℕ) (f : ℕ → Ω) (k : ℕ) :
    der τ L (∏ i ∈ Finset.range k, f i) = ∏ i ∈ Finset.range k, der τ L (f i) := by
  induction k with
  | zero => rw [Finset.prod_range_zero, Finset.prod_range_zero, di_der_one]
  | succ k ih => rw [Finset.prod_range_succ, Finset.prod_range_succ, di_der_mul, ih]

private theorem di_inf {a b : ℕ} (h : a.Coprime b) {g : G ℚ Ω} (ha : g ∈ fixMu ℚ Ω a) (hb : g ∈ fixMu ℚ Ω b) :
    g ∈ fixMu ℚ Ω (a * b) := by
  rw [di_mem] at ha hb ⊢
  intro x hx
  by_cases h0 : x = 0
  · subst h0
    simp
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr h
  have e1 : g (x ^ b) = x ^ b := ha _ (by rw [← pow_mul, mul_comm]; exact hx)
  have e2 : g (x ^ a) = x ^ a := hb _ (by rw [← pow_mul]; exact hx)
  have e : (a : ℤ) * u + b * v = 1 := by linarith
  have hx' : x = (x ^ a) ^ u * (x ^ b) ^ v := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ h0, e, zpow_one]
  nth_rewrite 1 [hx']
  rw [map_mul, map_zpow₀, map_zpow₀, e1, e2]
  exact hx'.symm

private theorem di_cop {l F r q : ℕ} (h : AdmP l F r q) : q.Coprime F := by
  unfold Nat.Coprime
  rw [h.2.1.gcd_eq]
  exact Nat.gcd_one_left F

variable [IsAlgClosure ℚ Ω]

private theorem di_lifts_pow {q : ℕ} (hq : q ≠ 0) {c : (ZMod q)ˣ} {t : G ℚ Ω} (h : Lifts q c t) (i : ℕ) :
    Lifts q (c ^ i) (t ^ i) := by
  haveI : NeZero q := ⟨hq⟩
  induction i with
  | zero =>
    intro x hx
    rw [pow_zero, pow_zero, Units.val_one, AlgEquiv.one_apply, ZMod.val_one_eq_one_mod,
      ← pow_eq_pow_mod 1 hx, pow_one]
  | succ i ih =>
    intro x hx
    rw [pow_succ t i, AlgEquiv.mul_apply, h x hx,
      ih _ (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]),
      ← pow_mul, pow_succ c i, Units.val_mul, ZMod.val_mul, ← pow_eq_pow_mod _ hx, mul_comm]

private theorem forall_fixMu_of_mul_closed_of_tau_of_fixMu_mul {N q : ℕ} (τ : G ℚ Ω) (P : G ℚ Ω → Prop)
    (hmul : ∀ g h, P g → P h → P (g * h)) (hq : q.Prime) (hNq : N.Coprime q) (hτ : IsTau q τ)
    (hP : P τ) (hbig : ∀ g ∈ fixMu ℚ Ω (N * q), P g) : ∀ g ∈ fixMu ℚ Ω N, P g := by
  intro g hg
  haveI : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨b0, hgen, hlift⟩ := hτ.2
  have GB := galBasic Ω q hq.ne_zero
  obtain ⟨b, hb⟩ := GB.2.2.2.2.1 g
  obtain ⟨k, hk⟩ : b ∈ Submonoid.powers b0 := mem_powers_iff_mem_zpowers.mpr (hgen b)
  have hlk : Lifts q b (τ ^ k) := by
    rw [← hk]
    exact di_lifts_pow hq.ne_zero hlift k
  have hh : (τ ^ k)⁻¹ * g ∈ fixMu ℚ Ω q := ((GB.2.2.2.2.2.2.2.2.2 b b (τ ^ k) g hlk hb).2.2).mp rfl
  have hτN : τ ∈ fixMu ℚ Ω N := hτ.1 N hNq
  have hhN : (τ ^ k)⁻¹ * g ∈ fixMu ℚ Ω N :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hτN k)) hg
  have hPk : ∀ j : ℕ, P (τ ^ j) := by
    intro j
    induction j with
    | zero => exact hbig _ (by rw [pow_zero]; exact Subgroup.one_mem _)
    | succ j ih => rw [pow_succ]; exact hmul _ _ ih hP
  have := hmul _ _ (hPk k) (hbig _ (di_inf hNq hhN hh))
  rwa [mul_inv_cancel_left] at this

private theorem di_gen {l F r : ℕ} (τ : ℕ → G ℚ Ω) (P : G ℚ Ω → Prop)
    (hmul : ∀ g h, P g → P h → P (g * h)) (L : List ℕ) : AdmL l F r L → (∀ q ∈ L, IsTau q (τ q)) →
    (∀ g ∈ fixMu ℚ Ω (F * L.prod), P g) → (∀ q ∈ L, P (τ q)) → ∀ g ∈ fixMu ℚ Ω F, P g := by
  induction L with
  | nil =>
    intro _ _ hbig _ g hg
    exact hbig g (by simpa using hg)
  | cons q L ih =>
    intro hL hτ hbig hP
    have hL' : AdmL l F r L := ⟨hL.1.of_cons, fun p hp => hL.2 p (List.mem_cons_of_mem _ hp)⟩
    have hqP : AdmP l F r q := hL.2 q (by simp)
    have hqc : q.Coprime L.prod := (isCrys_isDR_prod l F r L hL').2.2.1 q hL
    have hqF : q.Coprime F := di_cop hqP
    refine ih hL' (fun p hp => hτ p (List.mem_cons_of_mem _ hp)) ?_
      (fun p hp => hP p (List.mem_cons_of_mem _ hp))
    refine forall_fixMu_of_mul_closed_of_tau_of_fixMu_mul (τ q) P hmul hqP.1 (Nat.Coprime.mul hqF.symm hqc.symm) (hτ q (by simp))
      (hP q (by simp)) ?_
    intro g hg
    apply hbig
    have e : F * (q :: L).prod = F * L.prod * q := by rw [List.prod_cons]; ring
    rw [e]
    exact hg

private theorem di_step {l M F r : ℕ} (hF : F ≠ 0) (hM : M ∣ F) {x : ℕ → Ω} {s : ℕ → ℕ → ℕ} (hS : Sys l F r x s)
    (τ : ℕ → G ℚ Ω) (q : ℕ) (L : List ℕ) (hL : AdmL l F r (q :: L)) (hτ : IsTau q (τ q))
    (ih : ∀ g ∈ fixMu ℚ Ω F, ∃ z : Ω, (∀ h ∈ fixMu ℚ Ω (F * L.prod), h z = z) ∧
      z ^ M = g (der τ L (x L.prod)) / der τ L (x L.prod)) :
    ∃ z : Ω, (∀ h ∈ fixMu ℚ Ω (F * (q * L.prod)), h z = z) ∧
      z ^ M = τ q (der τ (q :: L) (x (q * L.prod))) / der τ (q :: L) (x (q * L.prod)) := by
  have hL' : AdmL l F r L := ⟨hL.1.of_cons, fun p hp => hL.2 p (List.mem_cons_of_mem _ hp)⟩
  have AP := isCrys_isDR_prod l F r L hL'
  have AP2 := isCrys_isDR_prod l F r (q :: L) hL
  have hqP : AdmP l F r q := hL.2 q (by simp)
  have hq : q.Prime := hqP.1
  have hqmod : q % F = 1 % F := hqP.2.1
  have hAqd : admitted l F r (q * L.prod) := by
    have := AP2.1
    rwa [List.prod_cons] at this
  have hd0 : L.prod ≠ 0 := AP.2.1
  have hN1 : F * L.prod ≠ 0 := mul_ne_zero hF hd0
  have hN2 : F * (q * L.prod) ≠ 0 := mul_ne_zero hF (mul_ne_zero hq.ne_zero hd0)
  have hcop : (F * L.prod).Coprime q := Nat.Coprime.mul (di_cop hqP).symm (AP.2.2.1 q hL).symm
  have hτq : τ q ∈ fixMu ℚ Ω (F * L.prod) := hτ.1 _ hcop
  have DB := derBasic Ω (F * (q * L.prod)) r hN2 τ L (x (q * L.prod)) (hS.ne _ hAqd) (hS.fix _ hAqd)
  have DBU := derBasic Ω (F * (q * L.prod)) r hN2 τ [] (der τ L (x (q * L.prod))) DB.1 DB.2.1
  have DBY := derBasic Ω (F * L.prod) r hN1 τ L (x L.prod) (hS.ne _ AP.1) (hS.fix _ AP.1)
  have GB1 := galBasic Ω (F * L.prod) hN1
  obtain ⟨φ, hφL⟩ := GB1.2.2.2.1 (ZMod.unitOfCoprime q hcop.symm)
  have hφ : Pows (F * L.prod) q φ := by
    intro y hy
    rw [hφL y hy, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod q hy]
  have hφF : φ ∈ fixMu ℚ Ω F := by
    rw [di_mem]
    intro y hy
    have hyN : y ^ (F * L.prod) = 1 := by rw [pow_mul, hy, one_pow]
    rw [hφ y hyN, pow_eq_pow_mod q hy, hqmod, ← pow_eq_pow_mod 1 hy, pow_one]
  obtain ⟨z0, hz0fix, hz0⟩ := ih φ⁻¹ (Subgroup.inv_mem _ hφF)
  have hnormX := hS.norm L.prod q hq hAqd (τ q) hτq hτ.2 φ hφ
  have hfq : τ q ^ (q - 1) ∈ fixMu ℚ Ω q := by
    obtain ⟨b0, -, hb0⟩ := hτ.2
    haveI : Fact q.Prime := ⟨hq⟩
    have hl := di_lifts_pow hq.ne_zero hb0 (q - 1)
    rw [ZMod.units_pow_card_sub_one_eq_one] at hl
    rw [di_mem]
    intro y hy
    rw [hl y hy, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hy, pow_one]
  have hτpow : τ q ^ (q - 1) ∈ fixMu ℚ Ω (F * (q * L.prod)) := by
    have := di_inf hcop (Subgroup.pow_mem _ hτq _) hfq
    rwa [show F * L.prod * q = F * (q * L.prod) by ring] at this
  have hlast := DBU.2.2.2.2.2.2.2.2 q hq.one_lt.le (DB.2.1 _ hτpow)
  have hnrm : nrm q (τ q) (der τ L (x (q * L.prod))) =
      (der τ L (x L.prod) / φ⁻¹ (der τ L (x L.prod))) ^ s L.prod q := by
    calc nrm q (τ q) (der τ L (x (q * L.prod)))
        = der τ L (nrm q (τ q) (x (q * L.prod))) := by
          simp only [nrm]
          rw [di_der_prod]
          exact Finset.prod_congr rfl (fun i _ => DB.2.2.1 (τ q ^ i))
      _ = der τ L ((x L.prod / φ⁻¹ (x L.prod)) ^ s L.prod q) := by rw [hnormX]
      _ = _ := by
          rw [di_der_pow, div_eq_mul_inv, di_der_mul, di_der_inv, ← div_eq_mul_inv, ← DBY.2.2.1 φ⁻¹]
  have hFq : F ∣ q - 1 := (Nat.modEq_iff_dvd' hq.one_lt.le).mp hqmod.symm
  obtain ⟨e, he⟩ := dvd_trans hM hFq
  have hle := (galBasic Ω (F * (q * L.prod)) hN2).2.2.2.2.2.2.2.2.1 (F * L.prod)
    (mul_dvd_mul_left F (dvd_mul_left L.prod q))
  show ∃ z : Ω, (∀ h ∈ fixMu ℚ Ω (F * (q * L.prod)), h z = z) ∧
    z ^ M = τ q (der1 q (τ q) (der τ L (x (q * L.prod)))) / der1 q (τ q) (der τ L (x (q * L.prod)))
  refine ⟨der τ L (x (q * L.prod)) ^ e * z0 ^ s L.prod q, ?_, ?_⟩
  · intro h hh
    rw [map_mul, map_pow, map_pow, DB.2.1 h hh, hz0fix h (hle hh)]
  · rw [hlast, hnrm, mul_pow, ← pow_mul, ← pow_mul, mul_comm e M, ← he, mul_comm (s L.prod q) M,
      pow_mul z0 M, hz0, div_eq_mul_inv (der τ L (x (q * L.prod)) ^ (q - 1)), ← inv_pow, inv_div]

end

end UpperTheory.V.ML

theorem UpperTheory.V.ML.derInv :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l M F r : ℕ), F ≠ 0 → M ∣ F → ∀ (x : ℕ → Ω) (s : ℕ → ℕ → ℕ), Sys l F r x s → ∀ (τ : ℕ → G ℚ Ω) (L : List ℕ), AdmL l F r L → (∀ q ∈ L, IsTau q (τ q)) →
    ∀ g ∈ fixMu ℚ Ω F, ∃ z : Ω, (∀ h ∈ fixMu ℚ Ω (F * L.prod), h z = z) ∧ z ^ M = g (der τ L (x L.prod)) / der τ L (x L.prod) := by
  intro Ω _ _ _ l M F r hF hM x s hS τ
  suffices key : ∀ n (L : List ℕ), L.length = n → AdmL l F r L → (∀ q ∈ L, IsTau q (τ q)) →
      ∀ g ∈ fixMu ℚ Ω F, ∃ z : Ω, (∀ h ∈ fixMu ℚ Ω (F * L.prod), h z = z) ∧
        z ^ M = g (der τ L (x L.prod)) / der τ L (x L.prod) by
    intro L hL hτ
    exact key _ L rfl hL hτ
  intro n
  induction n with
  | zero =>
    intro L hlen _ _ g hg
    obtain rfl : L = [] := List.length_eq_zero_iff.mp hlen
    have h1 : admitted l F r 1 := ⟨squarefree_one, fun q hq hd => absurd (Nat.dvd_one.mp hd) hq.ne_one⟩
    refine ⟨1, fun _ _ => map_one _, ?_⟩
    rw [List.prod_nil]
    show (1 : Ω) ^ M = g (x 1) / x 1
    rw [hS.fix 1 h1 g (by rwa [mul_one]), div_self (hS.ne 1 h1), one_pow]
  | succ n ihn =>
    intro L hlen hL hτ
    have AP := isCrys_isDR_prod l F r L hL
    have hN : F * L.prod ≠ 0 := mul_ne_zero hF AP.2.1
    have DB := derBasic Ω (F * L.prod) r hN τ L (x L.prod) (hS.ne _ AP.1) (hS.fix _ AP.1)
    have GB := galBasic Ω (F * L.prod) hN
    refine di_gen τ (fun g => ∃ z : Ω, (∀ h ∈ fixMu ℚ Ω (F * L.prod), h z = z) ∧
        z ^ M = g (der τ L (x L.prod)) / der τ L (x L.prod)) ?_ L hL hτ ?_ ?_
    · rintro g h ⟨z1, hz1f, hz1⟩ ⟨z2, hz2f, hz2⟩
      refine ⟨g z2 * z1, ?_, ?_⟩
      · intro k hk
        rw [map_mul, hz1f k hk, GB.2.2.2.2.2.2.1 z2 hz2f g k hk]
      · have hD := DB.1
        have hgD : g (der τ L (x L.prod)) ≠ 0 := (map_ne_zero g).mpr hD
        rw [mul_pow, ← map_pow, hz2, hz1, map_div₀, AlgEquiv.mul_apply]
        field_simp
    · intro g hg
      refine ⟨1, fun _ _ => map_one _, ?_⟩
      rw [DB.2.1 g hg, div_self DB.1, one_pow]
    · intro q hq
      have hp := List.perm_cons_erase hq
      have hlen' : (L.erase q).length = n := by
        rw [List.length_erase_of_mem hq, hlen]
        rfl
      have hL2 : AdmL l F r (q :: L.erase q) :=
        ⟨hp.nodup_iff.mp hL.1, fun p hp' => hL.2 p (hp.symm.subset hp')⟩
      have hτ2 : ∀ p ∈ L.erase q, IsTau p (τ p) := fun p hp' => hτ p (List.mem_of_mem_erase hp')
      have hL3 : AdmL l F r (L.erase q) :=
        ⟨hL2.1.of_cons, fun p hp' => hL2.2 p (List.mem_cons_of_mem _ hp')⟩
      obtain ⟨z, hz1, hz2⟩ := di_step hF hM hS τ q (L.erase q) hL2 (hτ q hq)
        (ihn (L.erase q) hlen' hL3 hτ2)
      have hprod : L.prod = q * (L.erase q).prod := by rw [hp.prod_eq, List.prod_cons]
      have hder : der τ L (x L.prod) = der τ (q :: L.erase q) (x L.prod) := DB.2.2.2.2.2.2.2.1 _ hp
      refine ⟨z, ?_, ?_⟩
      · rw [hprod]
        exact hz1
      · rw [hder, hprod]
        exact hz2
