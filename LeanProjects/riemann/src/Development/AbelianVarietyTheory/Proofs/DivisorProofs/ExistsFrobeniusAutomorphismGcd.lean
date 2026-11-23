import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowRootOfUnity

noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit

namespace GlobalTheory.LKRes.ResSplit.Tau

theorem pow_eq_pow_of_modEq' {M : Type*} [Monoid M] {ζ : M} {N a b : ℕ} (hζ : ζ ^ N = 1)
    (h : a ≡ b [MOD N]) : ζ ^ a = ζ ^ b := by
  have h' : a % N = b % N := h
  rw [← Nat.mod_add_div a N, ← Nat.mod_add_div b N, pow_add, pow_add, pow_mul, pow_mul, hζ, one_pow,
    one_pow, h']

theorem pow_modEq_pow_mod (p r a : ℕ) (hp : 1 ≤ p) : p ^ a ≡ p ^ (a % r) [MOD p ^ r - 1] := by
  have h1 : p ^ r ≡ 1 [MOD p ^ r - 1] := ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp)).2 dvd_rfl).symm
  have h2 := (Nat.ModEq.pow (a / r) h1).mul_left (p ^ (a % r))
  rw [one_pow, mul_one, ← pow_mul, ← pow_add, Nat.mod_add_div] at h2
  exact h2

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem pow_fix {σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p} {x : PadicAlgCl p} (h : σ x = x) (n : ℕ) :
    (σ ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, h]

theorem pow_apply_root' {σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p} {q N : ℕ}
    (h : ∀ ζ : PadicAlgCl p, ζ ^ N = 1 → σ ζ = ζ ^ q) {ζ : PadicAlgCl p} (hζ : ζ ^ N = 1) (k : ℕ) :
    (σ ^ k) ζ = ζ ^ q ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h1 : (ζ ^ q ^ n) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    rw [pow_succ', AlgEquiv.mul_apply, ih, h _ h1, ← pow_mul, pow_succ]

theorem frob_pow_mod (hK : FiniteDimensional ℚ_[p] K) {m : ℕ} (hm : 0 < m) {x : PadicAlgCl p}
    (hx : x ∈ Kn p K m) (a : ℕ) : (frobK p K ^ a) x = (frobK p K ^ (a % m)) x := by
  have h := (IsFrobOn.pow_fixes_iff p K hK hm ((isFrob_frobK hK).isFrobOn m) (m * (a / m))).2
    (dvd_mul_right _ _)
  conv_lhs => rw [← Nat.mod_add_div a m, pow_add, AlgEquiv.mul_apply, h x hx]

theorem exists_tau : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (f r : ℕ) (hq : qK p K = p ^ f), 0 < r →
    ∃ τ : Kn p K (r / Nat.gcd f r) ≃+* Kn p K (r / Nat.gcd f r),
      (∀ x, τ x = x ↔ (x : PadicAlgCl p) ∈ K) ∧ (∀ x, (⇑τ)^[r / Nat.gcd f r] x = x) ∧
      ∀ b : Qr p r, τ (incQ p K hq r b) = incQ p K hq r ((frobQ p r ^ Nat.gcd f r) b) := by
  intro p _ K hK f r hq hr
  have hp0 : 0 < p := (Nat.Prime.one_lt Fact.out).le
  have hd0 : 0 < Nat.gcd f r := Nat.gcd_pos_of_pos_right f hr
  have hm0 : 0 < r / Nat.gcd f r := Nat.div_pos (Nat.gcd_le_right (m := f) (n := r) hr) hd0
  have hrdm : r = Nat.gcd f r * (r / Nat.gcd f r) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right f r)).symm
  have hfdf : f = Nat.gcd f r * (f / Nat.gcd f r) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left f r)).symm
  have hcop : Nat.Coprime (f / Nat.gcd f r) (r / Nat.gcd f r) := Nat.coprime_div_gcd_div_gcd hd0
  set d := Nat.gcd f r with hd
  set m := r / d with hm
  set f' := f / d with hf'
  set k := f' ^ (Nat.totient m - 1) with hk
  have hk1 : f' * k ≡ 1 [MOD m] := by
    have ht : 0 < Nat.totient m := Nat.totient_pos.2 hm0
    have := Nat.ModEq.pow_totient hcop
    rwa [← Nat.sub_add_cancel ht, pow_succ'] at this
  have hk2 : f * k ≡ d [MOD r] := by
    have := Nat.ModEq.mul_left' d hk1
    rw [mul_one, ← mul_assoc, ← hfdf, ← hrdm] at this
    exact this
  let σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p := frobK p K ^ k
  have hσ : ∀ x ∈ Kn p K m, σ x ∈ Kn p K m := fun x hx => UnramifiedExtensions.map_mem_Kn K m σ hx
  have hσ' : ∀ x ∈ Kn p K m, σ⁻¹ x ∈ Kn p K m := fun x hx => UnramifiedExtensions.map_mem_Kn K m σ⁻¹ hx
  let τ : Kn p K m ≃+* Kn p K m :=
    { toFun := fun x => ⟨σ x, hσ x x.2⟩
      invFun := fun x => ⟨σ⁻¹ x, hσ' x x.2⟩
      left_inv := fun x => Subtype.ext (by
        show σ⁻¹ (σ (x : PadicAlgCl p)) = x
        rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply])
      right_inv := fun x => Subtype.ext (by
        show σ (σ⁻¹ (x : PadicAlgCl p)) = x
        rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply])
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : PadicAlgCl p) y)
      map_add' := fun x y => Subtype.ext (map_add σ (x : PadicAlgCl p) y) }
  have hτ : ∀ x, ((τ x : Kn p K m) : PadicAlgCl p) = σ x := fun _ => rfl
  refine ⟨τ, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_, fun b => ?_⟩
  · have h1 : σ x = x := by rw [← hτ, h]
    have h2 : (frobK p K ^ (k * f')) x = x := by rw [pow_mul]; exact pow_fix h1 f'
    have h3 : frobK p K (x : PadicAlgCl p) = x := by
      have e := frob_pow_mod hK hm0 x.2 (k * f')
      have e1 := frob_pow_mod hK hm0 x.2 1
      rw [pow_one] at e1
      have e2 : (k * f') % m = 1 % m := by rw [mul_comm]; exact hk1
      rw [e1, ← e2, ← e, h2]
    exact mem_of_frobK_fixed hK (Kn_le_Kur hm0 x.2) h3
  · exact Subtype.ext (show σ (x : PadicAlgCl p) = x from σ.commutes ⟨x, h⟩)
  · have hit : ∀ n (y : Kn p K m), (((⇑τ)^[n] y : Kn p K m) : PadicAlgCl p) = (σ ^ n) y := by
      intro n
      induction n with
      | zero => intro y; rfl
      | succ n ih =>
        intro y
        rw [Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, ← ih]
        rfl
    apply Subtype.ext
    rw [hit, ← pow_mul, frob_pow_mod hK hm0 x.2, show k * m % m = 0 by simp, pow_zero]
    rfl
  · have hN : ¬ p ∣ p ^ r - 1 := by
      intro h
      have h2 := Nat.dvd_sub (dvd_pow_self p hr.ne') h
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp0)] at h2
      exact (Nat.Prime.one_lt Fact.out).ne' (Nat.dvd_one.1 h2)
    have hpow : p ^ (f * k) ≡ p ^ d [MOD p ^ r - 1] := by
      have e := pow_modEq_pow_mod p r (f * k) hp0
      rw [show f * k % r = d % r from hk2] at e
      exact e.trans (pow_modEq_pow_mod p r d hp0).symm
    apply Subtype.ext
    rw [hτ, coe_incQ, coe_incQ, coe_frobQ_pow]
    refine UnramifiedExtensions.eqOn_Kn (Q0 p) (σ := resGK bot_le σ) (τ := frobK p (Q0 p) ^ d) (fun ζ hζ => ?_) b.2
    rw [residue_cardinality_base_field] at hζ
    rw [resGK_apply, frobenius_pow_root_of_unity p hN hζ d]
    have hfr := fun ζ' hζ' => (isFrob_iff hK (frobK p K)).1 (isFrob_frobK hK) ζ' (p ^ r - 1) hN hζ'
    show (frobK p K ^ k) ζ = _
    rw [pow_apply_root' hfr hζ k, hq, ← pow_mul]
    exact pow_eq_pow_of_modEq' hζ hpow

end GlobalTheory.LKRes.ResSplit.Tau
