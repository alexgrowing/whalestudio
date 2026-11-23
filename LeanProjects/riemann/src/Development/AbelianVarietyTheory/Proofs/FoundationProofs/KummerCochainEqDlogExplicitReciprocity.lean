import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HTLawAt
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AnnihilatorKaehlerDerivationPrimitiveRootStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SqPrimeSmulKaehlerDerivationEqSmulRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTransportsKaehlerRelationsOverInvariantsStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.RecOne

section Der

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [Module S M]

theorem smul_der_pow (d : Derivation R S M) (x : S) (n : ℕ) : x • d (x ^ n) = ((n : S) * x ^ n) • d x := by
  rcases n with _ | n
  · simp
  · rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul S, smul_smul, smul_smul]
    congr 1
    rw [Nat.add_sub_cancel]; ring

theorem rel_one (d : Derivation R S M) (e V Z p y : S) (L n : ℕ) (h1 : e • d V = y • d Z)
    (h2 : d (V ^ L) = p • d (Z ^ n)) :
    ((L : S) * V ^ L * Z * y - e * V * p * n * Z ^ n) • d Z = 0 := by
  have a1 := smul_der_pow d V L
  have a2 := smul_der_pow d Z n
  linear_combination (norm := module) (-((L : S) * V ^ L * Z)) • h1 - (e * Z) • a1 + (e * Z * V) • h2 +
    (e * V * p) • a2

theorem rel_two (d : Derivation R S M) (e V Z y y' : S) (n k c : ℕ) (h1 : e • d V = y • d Z)
    (h2 : e • d ((Z ^ n) ^ k * V) = y' • d (Z ^ c)) :
    (y' * c * Z ^ c - Z * (Z ^ n) ^ k * y - e * V * k * n * (Z ^ n) ^ k) • d Z = 0 := by
  have a1 := smul_der_pow d Z c
  have a2 := smul_der_pow d Z (n * k)
  rw [pow_mul, Nat.cast_mul] at a2
  rw [Derivation.leibniz] at h2
  linear_combination (norm := module) (Z * (Z ^ n) ^ k) • h1 - y' • a1 - Z • h2 + (e * V) • a2

end Der

theorem field_step {F : Type*} [Field F] (l L α u V Z ζ K p y y' Z' w w' w₂ k t c e : F) (hL : L ≠ 0) (hα : α ≠ 0)
    (hu : u ≠ 0) (hV : V ≠ 0) (hK : K ≠ 0)
    (h1 : l ^ 4 * (L * u * Z * y - l ^ 2 * V * p * (α * L) * ζ) = α * L * L * w)
    (h1' : l ^ 4 * (L * u * Z' * y' - l ^ 2 * (K * V) * p * (α * L) * ζ) = α * L * L * w')
    (h2 : l ^ 4 * (y' * c * Z' - Z * K * y - l ^ 2 * V * k * (α * L) * K) = α * L * L * w₂)
    (hc : c = 1 + t * L + e * L * L) :
    l ^ 6 * k - (l ^ 6 * (t * (ζ * p / u)) + (w' * u⁻¹ * (K * V)⁻¹ - w * u⁻¹ * V⁻¹)) =
      L * (l ^ 6 * e * (ζ * p * u⁻¹) + (t + e * L) * (w' * u⁻¹ * (K⁻¹ * V⁻¹)) - w₂ * (K⁻¹ * V⁻¹)) := by
  have h3 : (α * L * L) * (l ^ 6 * k * u * K * V - l ^ 6 * t * ζ * p * K * V - w' + w * K) =
      (α * L * L) * (L * (l ^ 6 * e * ζ * p * K * V + (t + e * L) * w' - w₂ * u)) := by
    subst hc
    linear_combination (-(L * u)) * h2 + (1 + t * L + e * L * L) * h1' - K * h1
  have h4 := mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hα hL) hL) h3
  field_simp
  linear_combination h4

theorem kummer_eq_dlog_one : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (m : ℕ) (ζ ζ' : Ω), IsPrimitiveRoot ζ (l ^ m) → ζ' ^ (l ^ m) = ζ →
  ∀ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) → P.eval ζ ∈ A → (P.eval ζ)⁻¹ ∈ A → P.eval ζ ≠ 0 →
  ∃ x ∈ A, ∀ s, s ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m s = 1 → ∀ k t : ZMod (l ^ m),
    GlobalTheory.Col.KumVal m ζ (P.eval ζ) s k → s ζ' = ζ ^ t.val * ζ' →
    GlobalTheory.Glue.CgA A l m ((l : Ω) ^ c * (k.val : Ω))
      ((l : Ω) ^ c * ((t.val : Ω) * (ζ * (Polynomial.derivative P).eval ζ / P.eval ζ)) + (s x - x)) := by
  intro l hl hl2
  refine ⟨6, ?_⟩
  intro Ω _ _ _ A hA m ζ ζ' hζ hζ' P hP hu hu' hu0
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hlp : l.Prime := Fact.out
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hlp.ne_zero
  have hpos : ∀ j : ℕ, 0 < l ^ j := fun j => pow_pos hlp.pos j
  haveI : ∀ j : ℕ, NeZero (l ^ j) := fun j => ⟨(hpos j).ne'⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, A.zero_mem, fun s _ _ k t _ _ => ⟨0, A.zero_mem, ?_⟩⟩
    have hk : k.val = 0 := by have := ZMod.val_lt k; simpa using this
    have ht : t.val = 0 := by have := ZMod.val_lt t; simpa using this
    rw [hk, ht]; simp
  set φ : fixA A →+* Ω := A.subtype.comp (fixA A).subtype with hφ
  obtain ⟨Q, rfl⟩ : ∃ Q : Polynomial (fixA A), Q.map φ = P := by
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases h0 : P.coeff n = 0
    · exact ⟨0, by simp [h0]⟩
    · obtain ⟨h1, h2⟩ := hP _ (Polynomial.coeff_mem_coeffs h0)
      exact ⟨⟨⟨P.coeff n, h1⟩, h2⟩, rfl⟩
  have hev : ∀ (R : Polynomial (fixA A)) (x : A), ((Polynomial.aeval x R : A) : Ω) = (R.map φ).eval (x : Ω) := by
    intro R x
    rw [Polynomial.eval_map, Polynomial.aeval_def]
    exact Polynomial.hom_eval₂ R (algebraMap (fixA A) A) A.subtype x
  have hsev : ∀ s ∈ Ine (F := ℚ) A, ∀ (R : Polynomial (fixA A)) (x : Ω),
      s ((R.map φ).eval x) = (R.map φ).eval (s x) := by
    intro s hs R x
    rw [Polynomial.eval_map, Polynomial.eval_map]
    have h := Polynomial.hom_eval₂ R φ (s : Ω →+* Ω) x
    have e : (s : Ω →+* Ω).comp φ = φ := RingHom.ext fun a => a.2 s hs
    rw [e] at h
    exact h
  rw [Polynomial.derivative_map]
  set u := (Q.map φ).eval ζ with hudef
  set p := ((Polynomial.derivative Q).map φ).eval ζ with hpdef
  obtain ⟨V, hV⟩ := IsAlgClosed.exists_pow_nat_eq u (hpos m)
  have hV0 : V ≠ 0 := by
    rintro rfl
    exact hu0 (by rw [← hV, zero_pow (hpos m).ne'])
  have hVA : V ∈ A := mem_of_pow_mem A (hpos m).ne' (hV ▸ hu)
  have hVA' : V⁻¹ ∈ A := mem_of_pow_mem A (hpos m).ne' (by rw [inv_pow, hV]; exact hu')
  obtain ⟨α, hα⟩ := GlobalTheory.T.sq_prime_smul_kaehlerDerivation_eq_smul_rootOfUnity l hl2 Ω A hA ⟨V, hVA⟩
  obtain ⟨Z, hZ⟩ := IsAlgClosed.exists_pow_nat_eq ζ' (hpos α)
  have hZζ : Z ^ l ^ (α + m) = ζ := by rw [pow_add, pow_mul, hZ, hζ']
  have hZp : IsPrimitiveRoot Z (l ^ (α + m + m)) := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h1 : ¬ Z ^ l ^ (α + (m' + 1) + m') = 1 := by
      rw [pow_add, pow_mul, hZζ]
      exact hζ.pow_ne_one_of_pos_of_lt (hpos m').ne' (Nat.pow_lt_pow_right hlp.one_lt (by omega))
    have h2 : Z ^ l ^ (α + (m' + 1) + m' + 1) = 1 := by
      rw [add_assoc (α + (m' + 1)), pow_add, pow_mul, hZζ, hζ.pow_eq_one]
    have h3 := orderOf_eq_prime_pow h1 h2
    have h4 := IsPrimitiveRoot.orderOf Z
    rwa [h3] at h4
  have hZA : Z ∈ A := mem_of_pow_mem A (hpos (α + m + m)).ne' (by rw [hZp.pow_eq_one]; exact A.one_mem)
  have hζA : ζ ∈ A := hZζ ▸ pow_mem hZA _
  have hζA' : ζ⁻¹ ∈ A := mem_of_pow_mem A (hpos m).ne' (by rw [inv_pow, hζ.pow_eq_one, inv_one]; exact A.one_mem)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (hpos m).ne'
  set VA : A := ⟨V, hVA⟩
  set ZA : A := ⟨Z, hZA⟩
  obtain ⟨y, hy⟩ := hα (α + m + m) (by omega) ZA hZp
  have hZAζ : ((ZA ^ l ^ (α + m) : A) : Ω) = ζ := by simpa using hZζ
  set pA : A := Polynomial.aeval (ZA ^ l ^ (α + m)) (Polynomial.derivative Q) with hpA
  have hpAp : (pA : Ω) = p := by rw [hpA, hev, hZAζ]
  have hpmem : p ∈ A := hpAp ▸ pA.2
  have hVu : VA ^ l ^ m = Polynomial.aeval (ZA ^ l ^ (α + m)) Q := by
    apply Subtype.ext
    rw [hev, hZAζ]
    simpa using hV
  have hd : dA A (VA ^ l ^ m) = pA • dA A (ZA ^ l ^ (α + m)) := by
    rw [hVu, Derivation.map_aeval]
  obtain ⟨w, hwA, hw⟩ := GlobalTheory.T.annihilator_kaehlerDerivation_primitiveRoot l hl2 Ω A hA _ ZA hZp _ (rel_one (dA A) _ VA ZA pA y _ _ hy hd)
  have hw1 : (l : Ω) ^ 4 * ((l : Ω) ^ m * u * Z * y - (l : Ω) ^ 2 * V * p * ((l : Ω) ^ α * (l : Ω) ^ m) * ζ) =
      (l : Ω) ^ α * (l : Ω) ^ m * (l : Ω) ^ m * w := by
    rw [← hV, ← hpAp, ← hZζ, ← pow_add, ← pow_add, ← hw]
    push_cast
    rfl
  refine ⟨w * u⁻¹ * V⁻¹, mul_mem (mul_mem hwA hu') hVA', ?_⟩
  rintro s hs hcyc k t ⟨v, hv, hsv⟩ hst
  have hsA : ∀ x ∈ A, s x ∈ A := fun x hx => (apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs) x).2 hx
  have hsζ : s ζ = ζ := GlobalTheory.Col.fix_of_cycMod le_rfl hcyc hζ.pow_eq_one
  have hsu : s u = u := by rw [hudef, hsev s hs, hsζ]
  have hsp : s p = p := by rw [hpdef, hsev s hs, hsζ]
  have hsV : s V = ζ ^ k.val * V := by
    have h1 : (v / V) ^ l ^ m = 1 := by rw [div_pow, hv, hV, div_self hu0]
    obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one h1
    have h2 : v = ζ ^ j * V := by rw [hj]; field_simp
    rw [h2, map_mul, map_pow, hsζ] at hsv
    exact mul_left_cancel₀ (pow_ne_zero j hζ0) (by rw [hsv]; ring)
  obtain ⟨c, -, hc⟩ := hZp.eq_pow_of_pow_eq_one (ξ := s Z) (by rw [← map_pow, hZp.pow_eq_one, map_one])
  have htr := GlobalTheory.T.inertia_transports_kaehler_relations_over_invariants Ω A s hs ((l : A) ^ 2) VA y ZA ((l : A) ^ 2) ((ZA ^ l ^ (α + m)) ^ k.val * VA)
    ⟨s y, hsA _ y.2⟩ (ZA ^ c) (by simp) (by push_cast; rw [hZζ]; exact hsV.symm) rfl (by simpa using hc) hy
  obtain ⟨w₂, hw₂A, hw₂⟩ := GlobalTheory.T.annihilator_kaehlerDerivation_primitiveRoot l hl2 Ω A hA _ ZA hZp _ (rel_two (dA A) _ VA ZA y _ _ _ _ hy htr)
  have hw2 : (l : Ω) ^ 4 * (s y * (c : Ω) * s Z - Z * ζ ^ k.val * y -
      (l : Ω) ^ 2 * V * (k.val : Ω) * ((l : Ω) ^ α * (l : Ω) ^ m) * ζ ^ k.val) =
      (l : Ω) ^ α * (l : Ω) ^ m * (l : Ω) ^ m * w₂ := by
    rw [← hc, ← hZζ, ← pow_add, ← pow_add, ← hw₂]
    push_cast
    rfl
  have hw1' := congrArg s hw1
  simp only [map_mul, map_sub, map_pow, map_natCast, hsu, hsp, hsζ, hsV] at hw1'
  obtain ⟨e, he⟩ : ∃ e : ℤ, (c : Ω) = 1 + (t.val : Ω) * (l : Ω) ^ m + (e : Ω) * (l : Ω) ^ m * (l : Ω) ^ m := by
    have h1 : Z ^ (c * l ^ α) = Z ^ (l ^ (α + m) * t.val + l ^ α) := by
      rw [pow_mul, hc, ← map_pow, hZ, hst, pow_add, pow_mul, hZζ, hZ]
    rw [(hZp.isOfFinOrder (hpos _).ne').pow_eq_pow_iff_modEq, ← hZp.eq_orderOf, Nat.modEq_iff_dvd] at h1
    obtain ⟨e, he⟩ := h1
    refine ⟨-e, ?_⟩
    have h2 := congrArg (Int.cast : ℤ → Ω) he
    push_cast at h2
    apply mul_left_cancel₀ (pow_ne_zero α hl0)
    push_cast
    linear_combination -h2
  have hfin := field_step (l : Ω) ((l : Ω) ^ m) ((l : Ω) ^ α) u V Z ζ (ζ ^ k.val) p y (s y) (s Z) w (s w) w₂
    (k.val : Ω) (t.val : Ω) (c : Ω) (e : Ω) (pow_ne_zero _ hl0) (pow_ne_zero _ hl0) hu0 hV0 (pow_ne_zero _ hζ0)
    hw1 hw1' hw2 he
  have hlA : (l : Ω) ∈ A := natCast_mem A l
  have hKV : (ζ ^ k.val)⁻¹ * V⁻¹ ∈ A := mul_mem (by rw [← inv_pow]; exact pow_mem hζA' _) hVA'
  refine ⟨_, ?_, by rw [map_mul, map_mul, map_inv₀, map_inv₀, hsu, hsV]; exact hfin⟩
  refine sub_mem (add_mem (mul_mem (mul_mem (pow_mem hlA _) (intCast_mem A e)) (mul_mem (mul_mem hζA hpmem) hu'))
    (mul_mem (add_mem (natCast_mem A _) (mul_mem (intCast_mem A e) (pow_mem hlA _)))
      (mul_mem (mul_mem (hsA w hwA) hu') hKV))) (mul_mem hw₂A hKV)

end GlobalTheory.RecOne
