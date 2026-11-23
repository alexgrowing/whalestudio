import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem cls_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {n M : ℕ} [NeZero n] (h : n ∣ M) {s : G ℚ Ω}
    (hs : ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) : Chr.cls ℚ Ω n s = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  have h1 : s ζ = ζ := hs ζ (by obtain ⟨k, rfl⟩ := h; rw [pow_mul, hζ.pow_eq_one, one_pow])
  have h2 := Chr.cls_spec (k := ℚ) n s ζ hζ.pow_eq_one
  rw [h1] at h2
  have h3 : ζ ^ ((Chr.cls ℚ Ω n s : ZMod n)).val = ζ ^ (1 : ℕ) := by rw [pow_one]; exact h2.symm
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨n, NeZero.pos n, hζ.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h3
  ext
  rw [Units.val_one, ← ZMod.natCast_zmod_val ((Chr.cls ℚ Ω n s : ZMod n)), (ZMod.natCast_eq_natCast_iff _ _ _).2 h3,
    Nat.cast_one]

private theorem exp_ex {l n : ℕ} (hl : l.Prime) (hn : n ≠ 0) :
    ∃ k m : ℕ, l.Coprime m ∧ n ∣ k * m ∧ ∀ m' : ℕ, l.Coprime m' → k ≡ 1 [MOD Nat.gcd n m'] := by
  obtain ⟨a, m, hlm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.one_lt.ne'
  have hcop : l.Coprime m := (Nat.Prime.coprime_iff_not_dvd hl).2 hlm
  have hcop2 : (l ^ a).Coprime m := Nat.Coprime.pow_left a hcop
  let k := Nat.chineseRemainder hcop2 0 1
  have hk0 : k ≡ 0 [MOD l ^ a] := k.2.1
  have hk1 : k ≡ 1 [MOD m] := k.2.2
  refine ⟨k, m, hcop, ?_, ?_⟩
  · exact Nat.mul_dvd_mul (Nat.modEq_zero_iff_dvd.1 hk0) dvd_rfl
  · intro m' hm'
    refine Nat.ModEq.of_dvd ?_ hk1
    have hg : (Nat.gcd (l ^ a * m) m').Coprime (l ^ a) :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) (Nat.Coprime.pow_right a hm'.symm)
    exact hg.dvd_of_dvd_mul_left (Nat.gcd_dvd_left _ _)

private theorem cyclotomicClass_eq_of_isComplexConj {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] {σ τ : G ℚ Ω}
    (hσ : IsCC σ) (hτ : IsCC τ) : Chr.cls ℚ Ω N σ = Chr.cls ℚ Ω N τ := by
  have key : ∀ {ρ : G ℚ Ω}, IsCC ρ → ∀ ζ : Ω, ζ ^ N = 1 → ρ ζ = ζ⁻¹ := by
    rintro ρ ⟨j, hj⟩ ζ hζ
    apply j.injective
    rw [hj, map_inv₀, Complex.inv_eq_conj]
    exact Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ, map_one]) (NeZero.ne N)
  have h1 : Chr.cls ℚ Ω N (τ⁻¹ * σ) = 1 := cls_one (dvd_refl N) (fun ζ hζ => by
    rw [AlgEquiv.mul_apply, key hσ ζ hζ, ← key hτ ζ hζ]
    exact AlgEquiv.aut_inv τ ▸ τ.symm_apply_apply ζ)
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

private theorem exists_character_of_dirichlet_data {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (hD : D.Good) {e N : ℕ} [NeZero N] {ψ : DirichletCharacter c.O N} {n' p₁ m₀ : ℕ}
    (hO : Aut.OfChar D e ψ n' p₁ m₀) :
    ∃ (χ : G ℚ Ω →* c.Oˣ) (N m : ℕ), 1 ≤ N ∧ Af.KillsMu N χ ∧ l.Coprime m ∧ χ ^ m = 1 ∧ (∀ σ, IsCC σ → χ σ = 1) ∧
      (∀ A, Raw.Away D.S A → Ine (F := ℚ) A ≤ χ.ker) ∧
      ∀ g, (∃ m' : ℕ, l.Coprime m' ∧ D.ψ g ^ m' = 1) → χ g = (D.om ^ (D.e + 3) * D.ξ * D.ψ) g := by
  obtain ⟨-, hpsi, -, hp1, ξ', ξ₀, -, -, -, hxi⟩ := hO
  haveI := hp1
  have hlp : l.Prime := hl.out
  haveI : NeZero l := ⟨hlp.ne_zero⟩
  have hl2 : l ≠ 2 := hD.l_odd
  have hn0 : Fintype.card (ZMod N)ˣ ≠ 0 := Fintype.card_ne_zero
  obtain ⟨k, m, hlm, hnkm, hk⟩ := exp_ex hlp hn0
  have hom : IsOmT c D.om := ⟨hD.om_pow, fun σ => Ideal.Quotient.eq.1 (hD.om_bar σ)⟩
  obtain ⟨hker1, hker2, -, -, hcc, hunr, -, -⟩ := (omT Ω l c).2 D.om hom
  obtain ⟨mξ, hlξ, hξm⟩ := hD.xi_ord
  have hψn : ∀ g, D.ψ g ^ Fintype.card (ZMod N)ˣ = 1 := by
    intro g
    rw [hpsi]
    show (MulChar.toUnitHom ψ) (Chr.cls ℚ Ω N g) ^ Fintype.card (ZMod N)ˣ = 1
    rw [← map_pow, pow_card_eq_one, map_one]
  have hψk : ∀ g, (∃ m' : ℕ, l.Coprime m' ∧ D.ψ g ^ m' = 1) → D.ψ g ^ k = D.ψ g := by
    rintro g ⟨m', hm', hg⟩
    have hd : orderOf (D.ψ g) ∣ Nat.gcd (Fintype.card (ZMod N)ˣ) m' :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (hψn g)) (orderOf_dvd_of_pow_eq_one hg)
    conv_rhs => rw [← pow_one (D.ψ g)]
    exact pow_eq_pow_iff_modEq.2 ((hk m' hm').of_dvd hd)
  have hψ1 : D.ψ ^ Fintype.card (ZMod N)ˣ = 1 := MonoidHom.ext fun g => by rw [MonoidHom.pow_apply, hψn g, MonoidHom.one_apply]
  refine ⟨D.om ^ (D.e + 3) * D.ξ * D.ψ ^ k, l * N * p₁ * 2 ^ n', (l - 1) * mξ * m, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hlp.ne_zero (NeZero.ne N)) (NeZero.ne p₁)) (pow_ne_zero _ two_ne_zero))
  · intro s hs
    have hl' : Chr.cls ℚ Ω l s = 1 := cls_one ⟨N * p₁ * 2 ^ n', by ring⟩ hs
    have hN' : Chr.cls ℚ Ω N s = 1 := cls_one ⟨l * p₁ * 2 ^ n', by ring⟩ hs
    have hp' : Chr.cls ℚ Ω p₁ s = 1 := cls_one ⟨l * N * 2 ^ n', by ring⟩ hs
    have hq' : Chr.cls ℚ Ω (2 ^ n') s = 1 := cls_one ⟨l * N * p₁, by ring⟩ hs
    have h1 : D.om s = 1 := by
      have : s ∈ (Chr.cls ℚ Ω l).ker := hl'
      rw [← hker2] at this
      exact this
    have h2 : D.ξ s = 1 := by
      rw [hxi, MonoidHom.mul_apply]
      simp only [Chr.dirG, MonoidHom.comp_apply, hp', hq', map_one, mul_one]
    have h3 : D.ψ s = 1 := by
      rw [hpsi]
      simp only [Chr.dirG, MonoidHom.comp_apply, hN', map_one]
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, h1, h2, h3, one_pow, mul_one]
  · have h : l.Coprime (l - 1) := (Nat.Prime.coprime_iff_not_dvd hlp).2
      (Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hlp.one_lt) (Nat.sub_lt hlp.pos one_pos))
    exact Nat.Coprime.mul_right (Nat.Coprime.mul_right h hlξ) hlm
  · obtain ⟨t, ht⟩ := hnkm
    have a1 : (D.om ^ (D.e + 3)) ^ ((l - 1) * mξ * m) = 1 := by
      rw [← pow_mul, show (D.e + 3) * ((l - 1) * mξ * m) = (l - 1) * ((D.e + 3) * mξ * m) by ring, pow_mul,
        hD.om_pow, one_pow]
    have a2 : D.ξ ^ ((l - 1) * mξ * m) = 1 := by
      rw [show (l - 1) * mξ * m = mξ * ((l - 1) * m) by ring, pow_mul, hξm, one_pow]
    have a3 : (D.ψ ^ k) ^ ((l - 1) * mξ * m) = 1 := by
      rw [← pow_mul, show k * ((l - 1) * mξ * m) = Fintype.card (ZMod N)ˣ * (t * ((l - 1) * mξ)) by
        rw [show Fintype.card (ZMod N)ˣ * (t * ((l - 1) * mξ)) = (Fintype.card (ZMod N)ˣ * t) * ((l - 1) * mξ) by ring,
          ← ht]
        ring, pow_mul, hψ1, one_pow]
    rw [mul_pow, mul_pow, a1, a2, a3, mul_one, mul_one]
  · intro σ hσ
    have ho : D.om σ = -1 := hcc σ hσ hl2
    have hx : D.ξ σ = -1 := by
      rw [← hD.xi_odd, hxi]
      simp only [MonoidHom.mul_apply, Chr.dirG, MonoidHom.comp_apply, cyclotomicClass_eq_of_isComplexConj _ hσ hD.isCC]
    have hchi : chiO ℚ Ω l c.O D.cc = -1 := by
      have h := IsConjOm.cyc (E := ℚ) (l := l) (σ := MulSemiringAction.toRingAut (G ℚ Ω) Ω D.cc) hD.isCC
      show Units.map _ (cycZ ℚ Ω l D.cc) = -1
      rw [show cycZ ℚ Ω l D.cc = -1 from h]
      ext
      simp
    have hP := hD.Psi_even
    simp only [Raw.Psi, Chr.Psi, MonoidHom.mul_apply] at hP
    rw [show (chiO ℚ Ω l c.O ^ (D.e : ℤ)) D.cc = (chiO ℚ Ω l c.O D.cc) ^ (D.e : ℤ) from rfl, hchi, zpow_natCast] at hP
    have hψσ : D.ψ σ = (-1) ^ D.e := by
      rw [hpsi] at hP ⊢
      have : Chr.dirG ℚ Ω ψ σ = Chr.dirG ℚ Ω ψ D.cc := by
        simp only [Chr.dirG, MonoidHom.comp_apply, cyclotomicClass_eq_of_isComplexConj _ hσ hD.isCC]
      rw [this]
      rw [← mul_right_inj ((-1 : c.Oˣ) ^ D.e), hP, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have hsq : D.ψ σ ^ k = D.ψ σ := hψk σ ⟨2, (Nat.coprime_primes hlp Nat.prime_two).2 hl2,
      by rw [hψσ, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]⟩
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply]
    rw [ho, hx, hsq, hψσ, ← pow_succ, ← pow_add]
    exact Even.neg_one_pow ⟨D.e + 2, by ring⟩
  · intro A hA
    have h1 : Ine A ≤ D.om.ker := hunr A (hA l hD.l_mem)
    have h2 := hD.xi_unr A hA
    have h3 := hD.psi_unr A hA
    intro x hx
    have a1 : D.om x = 1 := h1 hx
    have a2 : D.ξ x = 1 := h2 hx
    have a3 : D.ψ x = 1 := h3 hx
    rw [MonoidHom.mem_ker]
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, a1, a2, a3, one_pow, mul_one]
  · intro g hg
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply]
    rw [hψk g hg]

theorem UpperTheory.V.Ws.Lk.etaEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}, (Ctx2 D ∨ Ctx3 D) → ∃ (η : G ℚ Ω →* (PadicAlgCl l)ˣ) (N m : ℕ), 1 ≤ N ∧ Af.KillsMu N η ∧ l.Coprime m ∧ η ^ m = 1 ∧ (∀ σ, IsCC σ → η σ = 1) ∧ (∀ A, Raw.Away D.S A → Ine (F := ℚ) A ≤ η.ker) ∧ ∀ g, (∃ m' : ℕ, l.Coprime m' ∧ D.ψ g ^ m' = 1) → η g * toQ (D.om ^ (D.e + 3) * D.ξ * D.ψ) g = 1 := by
  intro Ω _ _ _ l _ c D hC
  have key : ∃ (χ : G ℚ Ω →* c.Oˣ) (N m : ℕ), 1 ≤ N ∧ Af.KillsMu N χ ∧ l.Coprime m ∧ χ ^ m = 1 ∧
      (∀ σ, IsCC σ → χ σ = 1) ∧ (∀ A, Raw.Away D.S A → Ine (F := ℚ) A ≤ χ.ker) ∧
      ∀ g, (∃ m' : ℕ, l.Coprime m' ∧ D.ψ g ^ m' = 1) → χ g = (D.om ^ (D.e + 3) * D.ξ * D.ψ) g := by
    rcases hC with ⟨hD, h, t, e, ψ, -, -, -, -, -, hO⟩ | ⟨hD, h, t, e, ψ, -, -, -, -, -, hO⟩
    · exact exists_character_of_dirichlet_data hD hO
    · exact exists_character_of_dirichlet_data hD hO
  obtain ⟨χ, N, m, hN, hK, hm, hχm, hcc, hA, hg⟩ := key
  have hval : ∀ g, (toQ χ)⁻¹ g = (Units.map (algebraMap c.O (PadicAlgCl l) : c.O →* PadicAlgCl l) (χ g))⁻¹ :=
    fun g => rfl
  refine ⟨(toQ χ)⁻¹, N, m, hN, ?_, hm, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [hval, hK s hs, map_one, inv_one]
  · ext g
    rw [MonoidHom.pow_apply, hval, inv_pow, ← map_pow, ← MonoidHom.pow_apply, hχm]
    simp
  · intro σ hσ
    rw [hval, hcc σ hσ, map_one, inv_one]
  · intro A hAw x hx
    have h1 : χ x = 1 := hA A hAw hx
    rw [MonoidHom.mem_ker, hval, h1, map_one, inv_one]
  · intro g hg'
    rw [hval, show toQ (D.om ^ (D.e + 3) * D.ξ * D.ψ) g =
      Units.map (algebraMap c.O (PadicAlgCl l) : c.O →* PadicAlgCl l) ((D.om ^ (D.e + 3) * D.ξ * D.ψ) g) from rfl,
      ← hg g hg', inv_mul_cancel]
