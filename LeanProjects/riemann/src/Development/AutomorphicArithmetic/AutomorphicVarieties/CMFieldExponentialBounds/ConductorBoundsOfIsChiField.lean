import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

private theorem lcm_le_mul' {a b c d : ℕ} (hc : a ≤ c) (hd : b ≤ d) (ha : 0 < a) (hb : 0 < b) :
    Nat.lcm a b ≤ c * d := by
  exact (Nat.le_of_dvd (Nat.mul_pos ha hb) (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a))).trans
    (Nat.mul_le_mul hc hd)

private theorem descend {E : Type} [Field E] [NumberField E] {N L : ℕ} [NeZero N]
    (j : E →ₐ[ℚ] CyclotomicField N ℚ) {ζ : CyclotomicField N ℚ} (hζ : IsPrimitiveRoot ζ N) (hL : L ∣ N)
    (H : ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ), τ ζ = ζ ^ a →
      a ≡ 1 [MOD L] → ∀ x : E, τ (j x) = j x) :
    Nonempty (E →ₐ[ℚ] CyclotomicField L ℚ) := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  have hL0 : L ≠ 0 := by
    rintro rfl
    exact hN0 (Nat.eq_zero_of_zero_dvd hL)
  haveI : NeZero L := ⟨hL0⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast hN0⟩
  haveI : NeZero ((L : ℕ) : ℚ) := ⟨by exact_mod_cast hL0⟩
  obtain ⟨M, hNLM⟩ := hL
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hN0 (by rw [hNLM, mul_zero])
  have hMdvd : M ∣ N := ⟨L, by rw [hNLM, mul_comm]⟩
  have hk : N / M = L := by
    rw [hNLM, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hM0)]
  have hη : IsPrimitiveRoot (ζ ^ M) L := by
    have := hζ.pow_of_dvd hM0 hMdvd
    rwa [hk] at this
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  haveI : IsCyclotomicExtension {L} ℚ (CyclotomicField L ℚ) :=
    CyclotomicField.isCyclotomicExtension L ℚ
  haveI : IsGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isGalois {N} ℚ _
  haveI : FiniteDimensional ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.finiteDimensional {N} ℚ _
  let F : IntermediateField ℚ (CyclotomicField N ℚ) := IntermediateField.adjoin ℚ {ζ ^ M}
  haveI : IsCyclotomicExtension {L} ℚ F := hη.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hmem : ∀ x : E, j x ∈ F := by
    intro x
    rw [← IsGalois.fixedField_fixingSubgroup F, IntermediateField.mem_fixedField_iff]
    intro τ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
    have hτη : τ (ζ ^ M) = ζ ^ M := hτ _ (IntermediateField.mem_adjoin_simple_self ℚ _)
    have hpow : (τ ζ) ^ N = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨a, -, hζa⟩ := hζ.eq_pow_of_pow_eq_one hpow
    apply H τ a hζa.symm
    have h1 : ζ ^ (a * M) = ζ ^ (1 * M) := by
      rw [pow_mul, hζa, ← map_pow, hτη, one_mul]
    have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
    have h2 : a * M ≡ 1 * M [MOD N] := by
      unfold Nat.ModEq
      apply hζ.pow_inj (Nat.mod_lt _ hNpos) (Nat.mod_lt _ hNpos)
      have e1 := pow_mod_orderOf ζ (a * M)
      have e2 := pow_mod_orderOf ζ (1 * M)
      rw [← hζ.eq_orderOf] at e1 e2
      rw [e1, e2, h1]
    rw [hNLM] at h2
    exact Nat.ModEq.mul_right_cancel' hM0 h2
  exact ⟨(IsCyclotomicExtension.algEquiv {L} ℚ F (CyclotomicField L ℚ)).toAlgHom.comp
    (j.codRestrict F.toSubalgebra hmem)⟩

private theorem finrank_le {E : Type} [Field E] [NumberField E] {c : ℕ} (hc : 0 < c)
    (j : E →ₐ[ℚ] CyclotomicField c ℚ) : Module.finrank ℚ E ≤ c := by
  haveI : NeZero c := ⟨hc.ne'⟩
  haveI : NeZero ((c : ℕ) : ℚ) := ⟨by exact_mod_cast hc.ne'⟩
  haveI : IsCyclotomicExtension {c} ℚ (CyclotomicField c ℚ) := CyclotomicField.isCyclotomicExtension c ℚ
  haveI : FiniteDimensional ℚ (CyclotomicField c ℚ) := IsCyclotomicExtension.finiteDimensional {c} ℚ _
  calc Module.finrank ℚ E ≤ Module.finrank ℚ (CyclotomicField c ℚ) :=
        LinearMap.finrank_le_finrank_of_injective (f := j.toLinearMap) j.toRingHom.injective
    _ = c.totient := IsCyclotomicExtension.finrank _ (Polynomial.cyclotomic.irreducible_rat hc)
    _ ≤ c := Nat.totient_le c

theorem UpperTheory.V.conductor_bounds_of_isChiField :
    ∀ (ψ : PChar) (e q d : ℕ), 0 < q → 0 < d → ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ e q d E →
      1 ≤ condF E ∧ condF E ≤ 2 ^ (e + 2) * ψ.N * q * d ∧ Module.finrank ℚ E ≤ condF E := by
  intro ψ e q d hq hd E _ _ hE
  obtain ⟨N, hNZ, j, ζ, h2, hψ, hqN, hdN, hζ, hτ⟩ := hE
  haveI := hNZ
  haveI := ψ.ne
  have hψpos : 0 < ψ.N := NeZero.pos ψ.N
  have hApos : 0 < 2 ^ (e + 2) := pow_pos two_pos _
  have hLN : Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d ∣ N :=
    Nat.lcm_dvd (Nat.lcm_dvd (Nat.lcm_dvd h2 hψ) hqN) hdN
  have d1 : 2 ^ (e + 2) ∣ Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d :=
    (Nat.dvd_lcm_left _ _).trans ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_left _ _))
  have dψ : ψ.N ∣ Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d :=
    (Nat.dvd_lcm_right _ _).trans ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_left _ _))
  have dq : q ∣ Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d :=
    (Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_left _ _)
  have dd : d ∣ Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d := Nat.dvd_lcm_right _ _
  have jac : ∀ (a m : ℕ), a ≡ 1 [MOD m] → jacobiSym (a : ℤ) m = 1 := by
    intro a m h
    have hm : (a : ℤ) % (m : ℤ) = 1 % (m : ℤ) := by
      unfold Nat.ModEq at h
      exact_mod_cast congrArg (Nat.cast (R := ℤ)) h
    rw [jacobiSym.mod_left, hm, ← jacobiSym.mod_left, jacobiSym.one_left]
  have hemb := descend j hζ hLN (by
    intro τ a hτa ha x
    refine ((hτ τ a hτa).mpr ⟨Or.inl (ha.of_dvd d1), ?_, jac a q (ha.of_dvd dq), jac a d (ha.of_dvd dd)⟩) x
    show ψ.χ (a : ZMod ψ.N) = 1
    have h' : ((a : ℕ) : ZMod ψ.N) = ((1 : ℕ) : ZMod ψ.N) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (ha.of_dvd dψ)
    rw [h', Nat.cast_one, MulChar.map_one])
  have hLpos : 0 < Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d :=
    Nat.pos_of_dvd_of_pos hLN (NeZero.pos N)
  unfold condF
  have hset : Nat.lcm (Nat.lcm (Nat.lcm (2 ^ (e + 2)) ψ.N) q) d ∈
      {N | 0 < N ∧ Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)} := ⟨hLpos, hemb⟩
  have hmem := Nat.sInf_mem ⟨_, hset⟩
  refine ⟨hmem.1, (Nat.sInf_le hset).trans ?_, ?_⟩
  · have hY := lcm_le_mul' (le_refl (2 ^ (e + 2))) (le_refl ψ.N) hApos hψpos
    have hX := lcm_le_mul' hY (le_refl q) (Nat.lcm_pos hApos hψpos) hq
    exact lcm_le_mul' hX (le_refl d) (Nat.lcm_pos (Nat.lcm_pos hApos hψpos) hq) hd
  · obtain ⟨hpos, ⟨j'⟩⟩ := hmem
    exact finrank_le hpos j'
