import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.compsup

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem deg_jac {a p n : ℕ} (h : a.Coprime p) : jacobiSym ((a ^ (2 * n) : ℕ) : ℤ) p = 1 := by
  have hc : Int.gcd ((a ^ n : ℕ) : ℤ) (p : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact Nat.Coprime.pow_left n h
  have he : ((a ^ (2 * n) : ℕ) : ℤ) = ((a ^ n : ℕ) : ℤ) ^ 2 := by
    push_cast
    ring
  rw [he]
  exact jacobiSym.sq_one' hc

private theorem deg_ker (A : AbF) {a : ℕ} (n : ℕ) (h : a.Coprime A.m) : A.ker (a ^ (A.deg * n)) := by
  haveI : NeZero A.m := ⟨A.pos.ne'⟩
  let u : (ZMod A.m)ˣ := ZMod.unitOfCoprime a h
  refine ⟨u ^ (A.deg * n), ?_, ?_⟩
  · rw [pow_mul]
    exact Subgroup.pow_mem _ (Subgroup.pow_index_mem A.H u) n
  · push_cast
    simp [u, ZMod.coe_unitOfCoprime]

private theorem deg_two {a e : ℕ} (n : ℕ) (h : a.Coprime (2 ^ (e + 2))) :
    a ^ (2 ^ (e + 1) * n) ≡ 1 [MOD 2 ^ (e + 2)] := by
  have ht := Nat.ModEq.pow_totient h
  rw [Nat.totient_prime_pow Nat.prime_two (by omega)] at ht
  simp only [Nat.add_sub_cancel, show (2 : ℕ) - 1 = 1 from rfl, mul_one] at ht
  rw [pow_mul]
  simpa using ht.pow n

theorem UpperTheory.V.Odd.deg :
    ∀ (M : AbF) (e q d : ℕ), PrimePair M.m q d → ∀ (E : Type) [Field E] [NumberField E], IsCompField M e q d E → ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ Module.finrank ℚ E → l ∣ M.deg := by
  intro M e q d _ E _ _ hE l hl hl2 hldvd
  obtain ⟨N, hN, j, ζ, h1, h2, h3, h4, hζ, hfix⟩ := hE
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.ne⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  haveI : IsGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isGalois {N} ℚ _
  have hpowζ : ∀ (τ : Gal(CyclotomicField N ℚ/ℚ)) (a n : ℕ), τ ζ = ζ ^ a → (τ ^ n) ζ = ζ ^ (a ^ n) := by
    intro τ a n hτ
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ τ n, AlgEquiv.mul_apply, hτ, map_pow, ih, ← pow_mul, pow_succ a n]
  have hmem : ∀ (τ : Gal(CyclotomicField N ℚ/ℚ)) (x : E),
      (τ ^ (2 ^ (e + 1) * M.deg)) (j x) = j x := by
    intro τ
    have hτ : τ ζ = ζ ^ ((hζ.autToPow ℚ τ : (ZMod N)ˣ) : ZMod N).val := (hζ.autToPow_spec ℚ τ).symm
    have hcop : (((hζ.autToPow ℚ τ : (ZMod N)ˣ) : ZMod N).val).Coprime N := ZMod.val_coe_unit_coprime _
    refine (hfix _ _ (hpowζ τ _ (2 ^ (e + 1) * M.deg) hτ)).mpr ⟨Or.inl ?_, ?_, ?_, ?_⟩
    · exact deg_two M.deg (hcop.coprime_dvd_right h1)
    · have hk := deg_ker M (2 ^ (e + 1)) (hcop.coprime_dvd_right h2)
      rwa [mul_comm M.deg] at hk
    · have hk := deg_jac (n := 2 ^ e * M.deg) (hcop.coprime_dvd_right h3)
      rwa [show 2 * (2 ^ e * M.deg) = 2 ^ (e + 1) * M.deg by ring] at hk
    · have hk := deg_jac (n := 2 ^ e * M.deg) (hcop.coprime_dvd_right h4)
      rwa [show 2 * (2 ^ e * M.deg) = 2 ^ (e + 1) * M.deg by ring] at hk
  obtain ⟨F, hF⟩ : ∃ F : IntermediateField ℚ (CyclotomicField N ℚ), F = j.fieldRange := ⟨_, rfl⟩
  have hcomm : ∀ σ τ : Gal(CyclotomicField N ℚ/ℚ), σ * τ = τ * σ := by
    intro σ τ
    apply IsPrimitiveRoot.autToPow_injective ℚ hζ
    rw [map_mul, map_mul, mul_comm]
  haveI hKn : F.fixingSubgroup.Normal :=
    ⟨fun n hn g => by rw [hcomm g n, mul_assoc, mul_inv_cancel, mul_one]; exact hn⟩
  have hKmem : ∀ τ : Gal(CyclotomicField N ℚ/ℚ), τ ^ (2 ^ (e + 1) * M.deg) ∈ F.fixingSubgroup := by
    intro τ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [hF] at hx
    obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
    exact hmem τ y
  have hindex : F.fixingSubgroup.index = Module.finrank ℚ E := by
    have e1 : Module.finrank ℚ E = Module.finrank ℚ F := by
      rw [hF]
      exact (AlgEquiv.ofInjectiveField j).toLinearEquiv.finrank_eq
    have e2 := Module.finrank_mul_finrank ℚ F (CyclotomicField N ℚ)
    have e3 := IsGalois.card_fixingSubgroup_eq_finrank F
    have e4 := IsGalois.card_aut_eq_finrank ℚ (CyclotomicField N ℚ)
    have e5 := F.fixingSubgroup.card_mul_index
    have hpos : 0 < Module.finrank F (CyclotomicField N ℚ) := Module.finrank_pos
    rw [e1]
    rw [e3, e4, ← e2, mul_comm (Module.finrank ℚ F)] at e5
    exact Nat.eq_of_mul_eq_mul_left hpos e5
  haveI : Fact l.Prime := ⟨hl⟩
  have hcard : l ∣ Nat.card (Gal(CyclotomicField N ℚ/ℚ) ⧸ F.fixingSubgroup) := by
    show l ∣ F.fixingSubgroup.index
    rw [hindex]
    exact hldvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l hcard
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hxk : ((g : Gal(CyclotomicField N ℚ/ℚ) ⧸ F.fixingSubgroup)) ^ (2 ^ (e + 1) * M.deg) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hKmem g
  have hdk := orderOf_dvd_of_pow_eq_one hxk
  rw [hx] at hdk
  have hcop : l.Coprime (2 ^ (e + 1)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hl Nat.prime_two).mpr hl2)
  exact hcop.dvd_of_dvd_mul_left hdk
